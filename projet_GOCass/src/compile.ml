(* étiquettes
     F_function      entrée fonction
     E_function      sortie fonction
     L_xxx           sauts
     S_xxx           chaîne

   expression calculée avec la pile si besoin, résultat final dans %rdi

   fonction : arguments sur la pile, résultat dans %rax ou sur la pile

            res k
            ...
            res 1
            arg n
            ...
            arg 1
            adr. retour
   rbp ---> ancien rbp
            ...
            var locales
            ...
            calculs
   rsp ---> ...

*)

open Format
open Ast
open Tast
open X86_64

let debug = ref false

let strings = Hashtbl.create 32
let alloc_string =
  let r = ref 0 in
  fun s ->
    incr r;
    let l = "S_" ^ string_of_int !r in
    Hashtbl.add strings l s;
    l

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz"

let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

type env = {
  exit_label: string;
  ofs_this: int;
  nb_locals: int ref; (* maximum *)
  next_local: int; (* 0, 1, ... *)
  pos_var: (int, int) Hashtbl.t
}

let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0; pos_var = Hashtbl.create 0}

let mk_bool d = { expr_desc = d; expr_typ = Tbool }

(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f =
  let l_true = new_label () and l_end = new_label () in
  f l_true ++
  movq (imm 0) (reg rdi) ++ jmp l_end ++
  label l_true ++ movq (imm 1) (reg rdi) ++ label l_end

let rec expr env e = match e.expr_desc with
  | TEskip ->
    nop
  | TEconstant (Cbool true) ->
    movq (imm 1) (reg rdi)
  | TEconstant (Cbool false) ->
    movq (imm 0) (reg rdi)
  | TEconstant (Cint x) ->
    movq (imm64 x) (reg rdi)
  | TEnil ->
    xorq (reg rdi) (reg rdi)
  | TEconstant (Cstring s) ->
    let l = alloc_string s in
      movq (ilab l) (reg rdi)
  | TEbinop (Band, e1, e2) ->
      expr env {expr_typ = e.expr_typ; expr_desc = TEif (e1, e2, {expr_typ = Tbool; expr_desc = TEconstant (Cbool false)})}
  | TEbinop (Bor, e1, e2) ->
      expr env {expr_typ = e.expr_typ; expr_desc = TEif (e1, {expr_typ = Tbool; expr_desc = TEconstant (Cbool true)}, e2)}
  | TEbinop (Beq | Bne | Blt | Ble | Bgt | Bge as op, e1, e2) ->
      let jmptyp = (match op with Blt -> jl | Ble -> jle | Bgt -> jg | Bge -> jge | Beq -> je | Bne -> jne | _ -> assert false) in
        expr env e1 ++
        pushq (reg rdi) ++
        expr env e2 ++
        popq rax ++
        cmpq (reg rax) (reg rdi) ++
        compile_bool jmptyp
  | TEbinop (Badd | Bsub | Bmul as op, e1, e2) ->
    let optyp = (match op with Badd -> addq | Bsub -> subq | Bmul -> imulq | _ -> assert false) in
        expr env e1 ++
        pushq (reg rdi) ++
        expr env e2 ++
        popq rax ++
        optyp (reg rax) (reg rdi)
  | TEbinop (Bdiv | Bmod as op, e1, e2) ->
    let regtyp = (match op with Bdiv -> rax | Bmod -> rdx | _ -> assert false) in
        expr env e1 ++
        pushq (reg rdi) ++
        expr env e2 ++
        popq rax ++
        movq (imm 0) (reg rdx) ++
        idivq (reg rdi) ++
        movq (reg regtyp) (reg rdi)
  | TEunop (Uneg, e1) ->
      expr env e1 ++
      negq (reg rdi)
  | TEunop (Unot, e1) ->
      expr env e1 ++
      notq (reg rdi)
  | TEunop (Uamp, _) -> assert false (* TODO *)
  | TEunop (Ustar, e1) ->
      expr env e1 ++
      movq (ind rdi) (reg rdi)
  | TEprint el ->
      let rec print_list = function
        | [] -> nop
        | t::q when t.expr_typ = Tint -> expr env t ++ call "print_int" ++ call "print_space" ++ print_list q
        | t::q when t.expr_typ = Tbool -> expr env t ++ call "print_bool" ++ call "print_space" ++ print_list q
        | t::q when t.expr_typ = Tstring -> expr env t ++ call "print_string" ++ call "print_space" ++ print_list q
        | _ -> assert false  in
      print_list el
  | TEident x ->
      movq (ind ~ofs:(Hashtbl.find env.pos_var x.v_id) rbp) (reg rdi)
  | TEassign ([{expr_desc=TEident x}], [e1]) ->
      expr env e1 ++
      (if x.v_name = "_" then nop
      else movq (reg rdi) (ind ~ofs:(Hashtbl.find env.pos_var x.v_id) rbp))
  | TEassign ([lv], [e1]) ->
    (* TODO code pour x1,... := e1,... *) assert false 
  | TEassign (_, _) ->
     assert false
  | TEblock el ->
      let rec block = function
        | [] -> nop
        | {expr_desc = TEvars v}::q ->
            let rec parcours next x = if x.v_name = "_" then nop else
            (Hashtbl.add env.pos_var x.v_id !(env.nb_locals);
            incr env.nb_locals;
            pushq (imm 0) ++ next) in List.fold_left parcours nop v ++ block q
        | t::q -> expr env t ++ block q in
      block el
  | TEif (e1, e2, e3) ->
      let l_then = new_label () and l_else = new_label () in
      expr env e1 ++
      cmpq (imm 0) (reg rdi) ++
      jne l_then ++
      expr env e2 ++
      jmp l_else ++
      label l_then ++
      expr env e3 ++
      label l_else
  | TEfor (e1, e2) ->
      let l_for = new_label () and l_exit = new_label () in
      label l_for ++
      expr env e1 ++
      cmpq (imm 0) (reg rdi) ++
      je l_exit ++
      expr env e2 ++
      jmp l_for ++
      label l_exit
  | TEnew ty ->
     (* TODO code pour new S *) assert false
  | TEcall (f, el) ->
     (* TODO code pour appel fonction *) assert false
  | TEdot (e1, {f_ofs=ofs}) ->
     (* TODO code pour e.f *) assert false
  | TEvars _ ->
     assert false (* fait dans block *)
  | TEreturn [] ->
    (* TODO code pour return e *) assert false
  | TEreturn [e1] ->
    (* TODO code pour return e1,... *) assert false
  | TEreturn _ ->
     assert false
  | TEincdec (e1, op) ->
      let optyp = (match op with Inc -> addq | Dec -> subq) in
      expr env e1 ++
      optyp (imm 1) (reg rdi)

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  (* TODO code pour fonction *) 
  let locals = ref 0 in fun () ->
  let s = f.fn_name in
  let n = List.length f.fn_params in
  let env = { exit_label = "F_"^s; ofs_this = n; nb_locals = ref n; next_local = !locals; pos_var = Hashtbl.create 0} in
  locals := !locals + n;
  label ("F_" ^ s) ++
  pushq (reg rbp) ++
  movq (reg rsp) (reg rbp) ++
  expr env e ++
  movq (reg rbp) (reg rsp) ++
  popq rbp ++
  ret

let decl code = function
  | TDfunction (f, e) -> code ++ function_ f e ()
  | TDstruct _ -> code

let file ?debug:(b=false) dl =
  debug := b;
  (* TODO calcul offset champs *)
  (* TODO code fonctions *) let funs = List.fold_left decl nop dl in
  { text =
      globl "main" ++ label "main" ++
      call "F_main" ++
      xorq (reg rax) (reg rax) ++
      ret ++
      funs ++
      inline "
print_int:
        movq    %rdi, %rsi
        movq    $S_int, %rdi
        xorq    %rax, %rax
        call    printf
        ret
print_bool:
        test    %rdi, %rdi
        jnz     print_true
        mov     $S_false, %rdi
        call    printf
        xorq    %rax, %rax
        ret
print_true:
        mov     $S_true, %rdi
        call    printf
        xorq    %rax, %rax
        ret
print_string:
        mov     %rdi, %rsi
        mov     $S_string, %rdi
        xorq    %rax, %rax
        call    printf
        ret    
print_space:
        mov     $S_space, %rdi
        xorq    %rax, %rax
        call    printf
        ret   
"; (* TODO print pour d'autres valeurs *)
   (* TODO appel malloc de stdlib *)
    data =
      label "S_int" ++ string "%ld" ++
      label "S_true" ++ string "true" ++
      label "S_false" ++ string "false" ++
      label "S_string" ++ string "%s" ++
      label "S_space" ++ string " " ++
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop)
    ;
  }
