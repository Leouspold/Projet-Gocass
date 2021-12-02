
open Format
open Lib
open Ast
open Tast

let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string

let error loc e = raise (Error (loc, e))

(* TODO environnement pour les types structure *)

(* TODO environnement pour les fonctions *)

let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | _ -> error dummy_loc ("unknown struct ") (* TODO type structure *)

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

let rec expr env e =
 let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  { expr_desc = e; expr_typ = ty }, rt

and expr_desc env loc = function
  | PEskip ->
     TEskip, tvoid, false
  | PEconstant c ->
    (* TODO *) TEconstant c, tvoid, false
  | PEbinop (op, e1, e2) ->
    (* TODO *) assert false
  | PEunop (Uamp, e1) ->
    (* TODO *) assert false
  | PEunop (Uneg | Unot | Ustar as op, e1) ->
    (* TODO *) assert false
  | PEcall ({id = "fmt.Print"}, el) ->
    (* TODO *) TEprint [], tvoid, false
  | PEcall ({id="new"}, [{pexpr_desc=PEident {id}}]) ->
     let ty = match id with
       | "int" -> Tint | "bool" -> Tbool | "string" -> Tstring
       | _ -> (* TODO *) error loc ("no such type " ^ id) in
     TEnew ty, Tptr ty, false
  | PEcall ({id="new"}, _) ->
     error loc "new expects a type"
  | PEcall (id, el) ->
     (* TODO *) assert false
  | PEfor (e, b) ->
     (* TODO *) assert false
  | PEif (e1, e2, e3) ->
     (* TODO *) assert false
  | PEnil ->
     (* TODO *) assert false
  | PEident {id=id} ->
     (* TODO *) (try let v = Env.find id env in TEident v, v.v_typ, false
      with Not_found -> error loc ("unbound variable " ^ id))
  | PEdot (e, id) ->
     (* TODO *) assert false
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

let decl_struct = Hashtbl.create 0

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

let decl_function = Hashtbl.create 0

let rec ptyp_declared = function
  | PTptr t -> ptyp_declared t
  | PTident { id = id; loc = loc } -> (Hashtbl.mem decl_struct id)

let rec ptyp_to_typ = function
  | PTptr t -> Tptr (ptyp_to_typ t)
  | PTident { id = id; loc = loc } -> match id with
    | "bool" -> Tbool
    | "int" -> Tint
    | "string" -> Tstring
    | s -> Tstruct(Hashtbl.find decl_struct (String.sub s 7 ((String.length s)-8)))

let rec param_to_var = function 
  | ({ id = id; loc = loc }, ptyp) -> new_var id loc (ptyp_to_typ ptyp)

let pfield_to_field = function
  | ({ id = id; loc = loc }, ptyp) -> { f_name = id; f_typ = (ptyp_to_typ ptyp); f_ofs = 0}


let phase2 = function
  | PDfunction { pf_name={id=id; loc=loc}; pf_params=pl; pf_typ=tyl; } ->
      if (Hashtbl.mem decl_function id)   (* fonction déjà déclareé *)
        then error loc "Function already declared"
      else if (dup_exist (List.map fst pl))  (* unicités des noms de variables *)
        then error loc "Multiple variables holding the same name in function declaration"
      else if not (List.for_all ptyp_declared (List.map snd pl))  (* types biens formés *)
        || not (List.for_all ptyp_declared tyl)  (* types biens formés *)
        then error loc "Invalid data type used in function declaration"
      else Hashtbl.add decl_function id { 
        fn_name = id;
        fn_params = (List.map param_to_var pl); 
        fn_typ = (List.map ptyp_to_typ tyl) }
  | PDstruct { ps_name = {id=id; loc=loc}; ps_fields = fl } ->
      if not (Hashtbl.mem decl_struct id)  (*structure bien déclarée*)
        then error loc "Unbound structure value"
      else if (dup_exist (List.map fst fl))  (* unicité des noms de variables *)
        then error loc "Multiple variables holding the same name in structure declaration"
      else if not (List.for_all ptyp_declared (List.map snd fl))  (* types biens formés *)
        then error loc "Invalid data type used in structure declaration"
      else List.iter (fun x -> Hashtbl.add (Hashtbl.find decl_struct id).s_fields (fst x).id (pfield_to_field x)) fl


(* 3. type check function bodies *)
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
