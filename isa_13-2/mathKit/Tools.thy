(*********************************************************************** 
* HiVe theory files
* 
* Copyright (C) 2015 Commonwealth of Australia as represented by Defence Science and Technology 
* Group (DST Group)
* 
* All rights reserved.
*
* The HiVe theory files are free software: released for redistribution and use, and/or modification,
* under the BSD License, details of which can be found in the LICENSE file included in the 
* distribution. 
************************************************************************)

header {* Some ML tools *}

theory Tools 

imports
  xHOL_Syntax_Chap

begin

text {*

We introduce a number of functions for manipulating the ML data structures supporting Isar.
The primary functions are for constructing terms, matching terms and inspecting terms.

*}

ML {*

structure dTools =
struct

local

val ctxt = (put_claset HOL_cs @{context}) delrules 
  [@{thm "iffI"},
   @{thm "notI"},
   @{thm "impI"},
   @{thm "disjCI"},
   @{thm "conjI"},
   @{thm "TrueI"},
   @{thm "refl"},
   @{thm "iffCE"},
   @{thm "FalseE"},
   @{thm "impCE"},
   @{thm "disjE"},
   @{thm "conjE"},
   @{thm "ex_ex1I"},
   @{thm "allI"},
   @{thm "the_equality"},
   @{thm "exI"},
   @{thm "exE"},
   @{thm "allE"}];

in

val empty_cs = claset_of ctxt;

end;

fun assoc x = (AList.lookup (op =)) x;
fun assocs x = (these oo AList.lookup (op =)) x;
fun overwrite x = ((AList.update (op =)) o Library.swap) x;

fun atomT str = Type(str, []);
fun prodT (a, b) = Type(@{type_name "prod"}, [a, b]);
fun funT (a, b) = Type(@{type_name "fun"}, [a, b]);
val boolT = atomT @{type_name "bool"};
val intT = atomT @{type_name "int"};
fun setT a = funT (a, boolT)
fun listT a = Type(@{type_name "list"}, [a]);
fun varT a = TVar((a, 0), []);
fun freeT a = TFree(a, []);


val read_str = Syntax.read_term_global;

(* translations from HOL to ML data structures *)

fun bool_of_term (Const (@{const_name "True"}, _))
    = true
 |  bool_of_term (Const (@{const_name "False"}, _))
    = false;

fun bool_of_term_tr (Const (@{const_syntax "True"}, _))
    = true
 |  bool_of_term_tr (Const (@{const_syntax "False"}, _))
    = false;

fun term_of_bool true 
    = Const (@{const_name "True"}, boolT)
 |  term_of_bool talse 
    = Const (@{const_name "False"}, boolT)

(*

fun bin_of_term_tr (Const (@{const_syntax "Int.Pls"}, _)) 
    = [true]
 |  bin_of_term_tr (Const (@{const_syntax "Int.Min"}, _)) 
    = [false]
 |  bin_of_term_tr (Const (@{const_syntax "Int.Bit0"}, _) $ bs) 
    = false :: bin_of_term_tr bs
 |  bin_of_term_tr (Const (@{const_syntax "Int.Bit1"}, _) $ bs) 
    = true :: bin_of_term_tr bs;

fun bin_of_term (Const (@{const_name "Int.Pls"}, _)) 
    = [true]
 |  bin_of_term (Const (@{const_name "Int.Min"}, _)) 
    = [false]
 |  bin_of_term (Const (@{const_name "Int.Bit0"}, _) $ bs) 
    = false :: bin_of_term bs
 |  bin_of_term (Const (@{const_name "Int.Bit1"}, _) $ bs) 
    = true :: bin_of_term bs;

fun term_of_bin [true]
    = Const(@{const_name "Int.Pls"}, intT)
 |  term_of_bin [false] 
    = Const(@{const_name "Int.Min"}, intT)
 |  term_of_bin (true::bs)
    = (Const (@{const_name "Int.Bit1"}, funT(intT, intT))) $ (term_of_bin bs)
 |  term_of_bin (false::bs)
    = (Const (@{const_name "Int.Bit0"}, funT(intT, intT))) $ (term_of_bin bs);

local 

fun iot bot tm =
let
  fun int_of n [] 
      = n
   |  int_of n (b :: bs) 
      = int_of (2 * n + (if b then 1 else 0)) bs;      
  val (sgn :: rev_digs) = rev (bot tm);
in
  (if sgn then 1 else ~1)*(int_of 0 rev_digs)
end;

in

val int_of_term = iot bin_of_term;
val int_of_term_tr = iot bin_of_term_tr;

end
  *)

fun list_of_term (Const(@{const_name "Cons"}, _) $ tm $ tms)
    = tm::(list_of_term tms)
 |  list_of_term (Const(@{const_name "Nil"}, _))
    = [];

fun list_of_term_tr (Const(@{const_syntax "Cons"}, _) $ tm $ tms)
    = tm::(list_of_term_tr tms)
 |  list_of_term_tr (Const(@{const_syntax "Nil"}, _))
    = [];

local

fun consT T = funT(T, funT(listT T, listT T));

in

fun term_of_list T (tm::tms) 
    = Const(@{const_name "Cons"}, consT T) $ tm $ (term_of_list T tms)
 |  term_of_list T [] 
    = Const(@{const_name "Nil"}, listT T)

end;

(* 
  I stole the get_sort straight out of proof_context!
*)


(*

fun typs_of_terms ctxt typs =
let

fun mk_sorts (T::Ts) = (Syntax.term_sorts T)@(mk_sorts Ts)
 |  mk_sorts [] = [];

val tsorts = mk_sorts typs;

val tsig = ProofContext.tsig_of ctxt;

val get_sort  =
  let

    val text = distinct (op =) (map (apsnd (Type.minimize_sort tsig)) tsorts);
    val _ =
      (case duplicates (eq_fst (op =)) text of
        [] => ()
      | dups => error ("Inconsistent sort constraints for type variable(s) "
          ^ commas_quote (map (Term.string_of_vname' o fst) dups)));

    fun lookup xi =
      (case AList.lookup (op =) text xi of
        NONE => NONE
      | SOME S => if S = dummyS then NONE else SOME S);

    fun get xi =
      (case (lookup xi, Variable.def_sort ctxt xi) of
        (NONE, NONE) => Type.defaultS tsig
      | (NONE, SOME S) => S
      | (SOME S, NONE) => S
      | (SOME S, SOME S') =>
          if Type.eq_sort tsig (S, S') then S'
          else error ("Sort constraint " ^ Syntax.string_of_sort ctxt S ^
            " inconsistent with default " ^ Syntax.string_of_sort ctxt S' ^
            " for type variable " ^ quote (Term.string_of_vname' xi)));
  in get end;
fun typ_of_term get_sort tm =
  let
    fun err () = raise TERM ("typ_of_term: bad encoding of type", [tm]);

    fun typ_of (Free (x, _)) = TFree (x, get_sort (x, ~1))
      | typ_of (Var (xi, _)) = TVar (xi, get_sort xi)
      | typ_of (Const ("_tfree",_) $ (t as Free _)) = typ_of t
      | typ_of (Const ("_tvar",_) $ (t as Var _)) = typ_of t
      | typ_of (Const ("_ofsort", _) $ Free (x, _) $ _) = TFree (x, get_sort (x, ~1))
      | typ_of (Const ("_ofsort", _) $ (Const ("_tfree",_) $ Free (x, _)) $ _) =
          TFree (x, get_sort (x, ~1))
      | typ_of (Const ("_ofsort", _) $ Var (xi, _) $ _) = TVar (xi, get_sort xi)
      | typ_of (Const ("_ofsort", _) $ (Const ("_tvar",_) $ Var (xi, _)) $ _) =
          TVar (xi, get_sort xi)
      | typ_of (Const ("_dummy_ofsort", _) $ t) = TFree ("'_dummy_", Syntax.sort_of_term t)
      | typ_of t =
          let
            val (head, args) = Term.strip_comb t;
            val a =
              (case head of
                Const (c, _) => (Lexicon.unmark_type c handle Fail _ => c)
              | _ => err ());
          in Type (a, map typ_of args) end;
  in typ_of tm end;
in
  map ((* (Type.cert_typ_mode Type.mode_syntax tsig) o *) (typ_of_term get_sort)) typs
end;


fun typ_of_term ctxt typ = 
let
  val (T::_) = typs_of_terms ctxt [typ];
in
  T
end;
*)

local

fun ws n = if (n>0) then " "^(ws(n-1)) else "";
 
fun 
  pr_tm (Free(n,_),x) = 
    "Free("^n^")"
| pr_tm (Var((n,m),_),x) =
    "Var("^n^"."^(string_of_int m)^")"
| pr_tm (Const(n,_),x) = 
    "Const("^n^")"
| pr_tm (Bound m,x) = 
    "Bound("^(string_of_int m)^")"
| pr_tm (Abs(n,_,b),x) = 
    "%"^n^".\n"^(ws(x+1))^
    (pr_tm (subst_bounds ([Free("B@"^n,dummyT)], b),x+1))
| pr_tm (f $ a,x) = 
    (pr_tm (f,x))^"\n"^(ws (x))^"$ "^(pr_tm (a,x+2));

fun 
  mk_list _ [a] = a
| mk_list sep (a::xs) =
    fold (fn a => fn b => b^sep^a) xs a
| mk_list _ [] = "";

fun
  pr_typ (TFree(n,s),x) =
    (ws x)^"TFree("^n^", ["^(mk_list ", " s)^"])"
| pr_typ (TVar((n,m),s),x) =
    (ws x)^"TVar("^n^"."^(string_of_int m)^", ["^
    (mk_list ", " s)^"])"
| pr_typ (Type(n,[]),x) =
    (ws x)^"Type("^n^")"
| pr_typ (Type(n,ts),x) =
    (ws x)^"Type("^n^")\n"^
    (mk_list "\n" (map (fn a => pr_typ (a, x+1)) ts));

fun 
  pr_tm_full (Free(n,T),x) = 
    "Free("^n^", "^(pr_typ(T,0))^")"
| pr_tm_full (Var((n,m),T),x) =
    "Var("^n^"."^(string_of_int m)^", "^(pr_typ(T,0))^")"
| pr_tm_full (Const(n,T),x) = 
    "Const("^n^", "^(pr_typ(T,0))^")"
| pr_tm_full (Bound m,x) = 
    "Bound("^(string_of_int m)^")"
| pr_tm_full (Abs(n,T,b),x) = 
    "%"^n^"::"^(pr_typ(T,0))^".\n"^(ws(x+1))^
    (pr_tm_full (subst_bounds ([Free("B@"^n,dummyT)], b),x+1))
| pr_tm_full (f $ a,x) = 
    (pr_tm_full (f,x))^"\n"^(ws (x))^"$ "^(pr_tm_full (a,x+2));

in

fun print_term t = (writeln(pr_tm(t,0)); t);

fun print_term_full t = (writeln(pr_tm_full(t,0)); t);

fun print_type t = (writeln(pr_typ(t,0)); t);

end;
fun funap_tr tm (a1::args) = funap_tr (tm$a1) args
 |  funap_tr tm [] = tm;

(*
fun intern_typ_instance sgn (T1, T2) =
let
  val T1' = Sign.intern_typ sgn T1;
  val T2' = Sign.intern_typ sgn T2;
  val tsg = Sign.tsig_of sgn;
in
  Type.typ_instance tsg (T1', T2')
end;

*)

fun key_sort ko = sort (prod_ord ko (make_ord (fn _ => true)));

fun ncopy a 0 = []
 |  ncopy a n = a::(ncopy a (n-1));

end (* dTools *);

*}

ML {*

signature PTOOLS = 
sig
  val empty_cs : claset;
  val atomT : string -> Term.typ;
  val boolT : Term.typ;
  val prodT : Term.typ * Term.typ -> Term.typ;
  val funT : Term.typ * Term.typ -> Term.typ;
  val setT : Term.typ -> Term.typ;
  val listT : Term.typ -> Term.typ;
  val varT : string -> Term.typ;
  val freeT : string -> Term.typ;
  val funap_tr : Term.term -> Term.term list -> Term.term;
  val ncopy : 'a -> int -> 'a list;
  val read_str : Context.theory -> string -> Term.term;
(*
  val typ_of_term : Proof.context -> Term.term -> Term.typ;
*)
  val print_term : Term.term -> Term.term;
  val print_term_full : Term.term -> Term.term;
  val print_type : Term.typ -> Term.typ;
end;

structure pTools:PTOOLS = dTools;

(* Turn off Sledgehammer *)

(* ResAxioms.suppress_endtheory := true; *)

open pTools;

*}

text {*

We introduce a variant of Isar namespaces aimed at supporting process modeling.

*}

ML {*

structure NameClasses = 
struct

val separator = "@";

fun mk_class suff nm = nm^separator^suff;

fun get_name nm = hd (space_explode separator nm);

fun get_class nm = hd (rev (space_explode separator nm));

fun is_class suff nm = (suff = get_class nm);

fun mk_class_tr' suff str =
  (mk_class suff str, funap_tr (Free(str,dummyT)));

end (* NameClasses *);

*}

ML {*

structure HNameSpace = 
struct

val separator = ".";
val implode_name = space_implode separator;
val explode_name = space_explode separator;

fun base "" = ""
  | base name = List.last (explode_name name);

fun append name1 "" = name1
  | append "" name2 = name2
  | append name1 name2 = name1 ^ separator ^ name2;

end (* HNameSpace *);

*}
(*

text {*

This doesn't seem to be used?

*}

ML {*

structure LemmasCollection = 
struct

fun extend_lemmas tblnm thmstr thy =
let
  val thm_att_args = 
        [(Facts.named thmstr,
          [Args.src ((tblnm, 
                      (Outer_Syntax.scan Position.none "add")), 
                     Position.none)])];
  val flthy = #2 o Specification.theorems_cmd "" [(Attrib.empty_binding, thm_att_args)];
  val lthy = Named_Target.theory_init thy;
  val lthy' = flthy lthy;
  val ctxt' = Local_Theory.exit lthy';
  val thy' = ProofContext.theory_of ctxt';
in
  thy'
end;

end (* LemmasCollection *);

*}
*)

end
