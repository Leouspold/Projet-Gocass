
open Format
open Lib
open Ast
open Tast

let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string

let error loc e = raise (Error (loc, e))

(* TODO environnement pour les types structure *)

let decl_struct = Hashtbl.create 0
let decl_function = Hashtbl.create 0

(* TODO environnement pour les fonctions *)

let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | _ -> error dummy_loc ("unknown struct ") (* TODO type structure *)

let rec ptyp_to_typ = function
  | PTptr t -> Tptr (ptyp_to_typ t)
  | PTident { id = id; loc = loc } -> match id with
    | "bool" -> Tbool
    | "int" -> Tint
    | "string" -> Tstring
    | s -> Tstruct(Hashtbl.find decl_struct (String.sub s 7 ((String.length s)-8)))

let rec eq_type ty1 ty2 = match ty1, ty2 with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | _ -> false
    (* TODO autres types *)

let fmt_used = ref false
let fmt_imported = ref false

let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let new_var =
  let id = ref 0 in
  fun x loc ?(used=false) ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty; v_used = used; v_addr = false }

let rec param_to_var = function 
  | ({ id = id; loc = loc }, ptyp) -> new_var id loc (ptyp_to_typ ptyp)

module Env = struct
  module M = Map.Make(String)
  type t = var M.t
  let empty = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env
  let all_vars = ref []
  let check_unused () =
    let check v =
      if v.v_name <> "_" && (* TODO used *) true then error v.v_loc "unused variable" in
    List.iter check !all_vars
  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    add env v, v

  (* TODO type () et vecteur de types *)
end

let tvoid = Tmany []
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid

let rec constant_to_typ = function
  | Cbool _ -> Tbool
  | Cint _ -> Tint
  | Cstring _ -> Tstring

let pfunc_to_function = function
  {pf_name=pf_name ;pf_params=pf_params ;pf_typ=pf_typ ;pf_body=pf_body} -> 
  {fn_name = pf_name.id; fn_params = (List.map param_to_var pf_params); fn_typ = (List.map ptyp_to_typ pf_typ) }

let pfunc_type = function
  |[x] -> x
  | l -> Tmany l

let rec ptr_bypass = function
  | Tptr t -> ptr_bypass t
  | t -> t

let rec expr env e =
 let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  { expr_desc = e; expr_typ = ty }, rt

and expr_desc env loc = function
  | PEskip ->
     TEskip, tvoid, false
  | PEconstant c ->
     TEconstant c, (constant_to_typ c), false
  | PEbinop (op,e1,e2) -> 
    let desc1,ty1,rt1 = expr_desc env e1.pexpr_loc e1.pexpr_desc in
    let desc2,ty2,rt2 = expr_desc env e2.pexpr_loc e2.pexpr_desc in
   (match op with 
    | Badd | Bsub | Bmul | Bdiv | Bmod ->
    (if (ty1 = Tint && ty2 = Tint)
      then TEbinop (op, make desc1 ty1, make desc2 ty2), Tint, false
      else error loc "Int operation on non ints")
    | Beq | Bne ->
    (if (ty1 = ty2)
      then TEbinop (op, make desc1 ty1, make desc2 ty2), Tbool, false
      else error loc "Can't compare differently typed expressions")
    | Blt | Ble | Bgt | Bge | Band | Bor ->
    (if (ty1 = Tbool && ty2 = Tbool)
      then TEbinop (op, make desc1 ty1, make desc2 ty2), Tbool, false
      else error loc "Bool operation on non bools"))
  | PEunop (Uamp, e1) ->
      let desc1,rt1 = expr env e1 in
      TEunop (Uamp, desc1), Tptr desc1.expr_typ, false
  | PEunop (Ustar, e1) ->
      let desc1,rt1 = expr env e1 in
      if (desc1.expr_typ = Tptr _) 
      then let Tptr ptr = desc1.expr_typ in
        TEunop (Ustar, desc1), desc1.expr_typ,false
      else error loc "Expression is not a pointer"  
  | PEunop (Uneg | Unot as op, e1) ->
      let desc1,rt1 = expr env e1 in
      if ((desc1.expr_typ = Tint)&&(op = Uneg))||((desc1.expr_typ = Tbool)&&(op = Unot))
      then TEunop (op, desc1), desc1.expr_typ, false
      else error loc "Wrong type negation"
  | PEcall ({id = "fmt.Print"}, el) ->
      if not !fmt_imported then error loc "fmt not imported"
      else (fmt_used := true ; TEprint (List.map (function x -> fst (expr env x)) el), tvoid, false)
  | PEcall ({id="new"}, [{pexpr_desc=PEident {id}}]) ->
     let ty = match id with
       | "int" -> Tint | "bool" -> Tbool | "string" -> Tstring
       | _ -> if Hashtbl.mem decl_struct id 
        then (ptyp_to_typ (PTident {id=id;loc=loc}))
        else error loc ("No such type " ^ id) in
        TEnew ty, Tptr ty, false
  | PEcall ({id="new"}, _) ->
     error loc "new expects a type"
  | PEcall (id, el) ->
      if Hashtbl.mem decl_function id.id
      then let f = (pfunc_to_function (Hashtbl.find decl_function id.id)) in
         TEcall (f,List.map (function x -> fst (expr env x)) el ), pfunc_type f.fn_typ, false
      else error loc ("No such function " ^ id.id)
  | PEfor (e, b) ->
     let texpr,trt = expr env e in
     let bexpr,brt = expr env b in
     if texpr.expr_typ = Tbool then TEfor(texpr,bexpr), tvoid, false
     else error loc "For loop not holding a condition"
  | PEif (e1, e2, e3) ->
     let expr1,rt1 = expr env e1 in
     let expr2,rt2 = expr env e2 in
     let expr3,rt3 = expr env e3 in
     if expr1.expr_typ = Tbool then TEif(expr1,expr2,expr3), tvoid, false
     else error loc "If not holding a condition"
  | PEnil -> TEnil, tvoid, false
  | PEident {id=id} ->
     (try let v = Env.find id env in 
      (v.v_used <- true; TEident v, v.v_typ, false)
      with Not_found -> error loc ("Unbound variable " ^ id))
  | PEdot (e, id) ->
     (let estruct,b = expr env e in
     match ptr_bypass estruct.expr_typ with
       | Tstruct str -> (if not (Hashtbl.mem decl_struct str.s_name)
          then error loc ("Unbound structure" ^ str.s_name)
          else if not (Hashtbl.mem str.s_fields id.id)
          then error loc ("Structure " ^ str.s_name ^ " holds no such field " ^ id.id)
          else let champ = Hashtbl.find str.s_fields id.id in
            TEdot (estruct, champ), champ.f_typ, false)
       | _ -> error loc "Expression is not a structure")
  | PEassign (lvl, el) ->
     (* TODO *) TEassign ([], []), tvoid, false 
  | PEreturn el ->
     (* TODO *) TEreturn [], tvoid, true
  | PEblock el ->
     (* TODO *) TEblock [], tvoid, false
  | PEincdec (e, op) ->
     (* TODO *) assert false
  | PEvars _ ->
     (* TODO *) assert false 

let found_main = ref false

(* 1. declare structures *)

let phase1 = function
  | PDstruct { ps_name = { id = id; loc = loc }} -> 
    if not (Hashtbl.mem decl_struct id)
      then Hashtbl.add decl_struct id { s_name = id; s_fields = Hashtbl.create 0 }
      else error loc "Structure name already used"
  | PDfunction _ -> ()

let sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | _ -> (* TODO *) assert false 

(* 2. declare functions and type fields *)

let rec dup_exist = function  (*verifie l'existence de doublons dans une liste*)
  | [] -> false
  | hd::tl -> List.exists ((=) hd) tl || dup_exist tl

let rec ptyp_declared = function
  | PTptr t -> ptyp_declared t
  | PTident { id = id; loc = loc } -> (Hashtbl.mem decl_struct id)

let pfield_to_field = function
  | ({ id = id; loc = loc }, ptyp) -> { f_name = id; f_typ = (ptyp_to_typ ptyp); f_ofs = 0}


let phase2 = function
  | PDfunction { pf_name={id=id; loc=loc}; pf_params=pl; pf_typ=tyl; pf_body=body} ->
      if (Hashtbl.mem decl_function id)   (* fonction déjà déclareé *)
        then error loc "Function already declared"
      else if (dup_exist (List.map fst pl))  (* unicités des noms de variables *)
        then error loc "Multiple variables holding the same name in function declaration"
      else if not (List.for_all ptyp_declared (List.map snd pl))  (* types biens formés *)
        || not (List.for_all ptyp_declared tyl)  (* types biens formés *)
        then error loc "Invalid data type used in function declaration"
      else Hashtbl.add decl_function id { pf_name={id=id; loc=loc}; pf_params=pl; pf_typ=tyl; pf_body=body}
  | PDstruct { ps_name = {id=id; loc=loc}; ps_fields = fl } ->
      if not (Hashtbl.mem decl_struct id)  (*structure bien déclarée*)
        then error loc "Unbound structure value"
      else if (dup_exist (List.map fst fl))  (* unicité des noms de variables *)
        then error loc "Multiple variables holding the same name in structure declaration"
      else if not (List.for_all ptyp_declared (List.map snd fl))  (* types biens formés *)
        then error loc "Invalid data type used in structure declaration"
      else List.iter (fun x -> Hashtbl.add (Hashtbl.find decl_struct id).s_fields (fst x).id (pfield_to_field x)) fl


(* 3. type check function bodies *)

let rec prefixe l1 l2 = match l1,l2 with
  | [],l2 -> (true,l2)
  | l1,[] -> (false,[])
  | t1::q1,t2::q2 -> let b,l = (prefixe q1 q2) in if b then (t1 = t2,l) else (false,[])

let test_id s loc = function
  | PTident { id = id } -> (id = s)
  | PTptr _ -> error loc "Expression is not a pointer"

let rec same_id ptyp1 ptyp2 = match (ptyp1,ptyp2) with
  | (PTident id1,PTident id2) -> id1.id = id2.id
  | (PTptr ptr1,PTptr ptr2) -> same_id ptr1 ptr2
  | _ -> false

let hashtbl_exists tbl f =
  let b = ref false in
  let s = ref {s_name = ""; s_fields = Hashtbl.create 0} in
  (Hashtbl.iter (fun k v -> (if ((f v) || !b) then (s := v; b := true))) tbl ; (!b,!s))

let rec typ_to_ptyp = function
  | Tint -> PTident { loc = dummy_loc; id = "int" }
  | Tbool -> PTident { loc = dummy_loc; id = "bool" }
  | Tstring -> PTident { loc = dummy_loc; id = "string" }
  | Tstruct { s_name = name; s_fields = fields} -> PTident { loc = dummy_loc; id = name }
  | Tptr typ -> PTptr (typ_to_ptyp typ)
  | Tmany _ -> raise Exit

let block_bypass e = match e.pexpr_desc with
  | PEblock l -> l
  | PEskip -> []
  | _ -> raise Exit

let rec return_type pexprlist tyl = 
  if (pexprlist = []) then (tyl = []) else
  let pexpr,q,hdtyl,tltyl = (List.hd pexprlist),(List.tl pexprlist),(List.hd tyl),(List.tl tyl)
  in match pexpr.pexpr_desc with
  | PEskip -> return_type q tyl
  | PEconstant Cbool _ -> (test_id "bool" pexpr.pexpr_loc hdtyl)&&(return_type q tltyl)
  | PEconstant Cint _ -> (test_id "int" pexpr.pexpr_loc hdtyl)&&(return_type q tltyl)
  | PEconstant Cstring _ -> (test_id "string" pexpr.pexpr_loc hdtyl)&&(return_type q tltyl)
  | PEbinop (op,_,_) -> (test_id (match op with
    | Badd -> "int"
    | Bsub -> "int"
    | Bmul -> "int"
    | Bdiv -> "int"
    | Bmod -> "int"
    | _ -> "bool") pexpr.pexpr_loc hdtyl)&&(return_type q tltyl)
  | PEunop (op,e) -> ((match op with
    | Uneg -> (test_id "int" pexpr.pexpr_loc hdtyl)
    | Unot -> (test_id "bool" pexpr.pexpr_loc hdtyl)
    | Uamp -> (hdtyl = PTptr _)
    | Ustar -> if (return_type [e] [PTptr _]) 
      then (return_type [e] [PTptr hdtyl])
      else error e.pexpr_loc "Expression is not a pointer" ))&&(return_type q tltyl)
  | PEnil -> (hdtyl = PTptr _)&&(return_type q tltyl)
  | PEcall (idf,varlist) -> 
    let b,tylq = prefixe (Hashtbl.find decl_function idf.id).pf_typ tyl
      in b && (return_type q tylq)
  | PEident idv -> (test_id idv.id pexpr.pexpr_loc hdtyl)
  | PEdot (e,s) ->
    (let (b,exprstruct) = (hashtbl_exists decl_struct (function dstruct -> return_type [e] [PTident { loc = e.pexpr_loc; id = dstruct.s_name }])) in
      if not b then error e.pexpr_loc "Unbound structure or wrong expression"
    else if not (Hashtbl.mem exprstruct.s_fields s.id) then error s.loc "Unbound structure field"
    else try same_id (typ_to_ptyp (Hashtbl.find exprstruct.s_fields s.id).f_typ) hdtyl 
      with Exit -> error pexpr.pexpr_loc "Internal error : field should not hold several or no types")&&(return_type q tltyl)
  | PEassign _ -> return_type q tyl
  | PEvars _ -> return_type q tyl
  | PEif (_,e1,e2) -> ((return_type ((block_bypass e1)@q) tyl) && (return_type ((block_bypass e2)@q) tyl))
  | PEreturn _ -> error pexpr.pexpr_loc "Internal error : wrong return expression verification" (*impossible case*)
  | PEblock _ -> error pexpr.pexpr_loc "Internal error : wrong return expression verification" (*impossible case*)
  | PEfor (e1,e2) -> (return_type ((block_bypass e2)@q) tyl)
  | PEincdec _ -> (test_id "int" pexpr.pexpr_loc hdtyl)&&(return_type q tltyl)

let rec return_exists pexpr = let q = List.tl pexpr in match (List.hd pexpr).pexpr_desc with
  | PEif (e1,e2,e3) -> (((return_exists (block_bypass e2)) && (return_exists (block_bypass e3))) || return_exists q)
  | PEreturn _ -> true
  | PEblock l -> ((return_exists l)||(return_exists q))
  | PEfor (e1,e2) -> ((return_exists (block_bypass e2))||(return_exists q))
  | _ -> return_exists q


let decl = function
  | PDfunction { pf_name={id; loc}; pf_body = e; pf_typ=tyl } ->
    (* TODO check name and type *)
    let f = { fn_name = id; fn_params = []; fn_typ = []} in
    let e, rt = expr Env.empty e in
    TDfunction (f, e)
  | PDstruct {ps_name={id}} ->
    (* TODO *) let s = { s_name = id; s_fields = Hashtbl.create 5 } in
     TDstruct s

let file ~debug:b (imp, dl) =
  debug := b;
  (* fmt_imported := imp; *)
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  Env.check_unused (); (* TODO variables non utilisees *)
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl
