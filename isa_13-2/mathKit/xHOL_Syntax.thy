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

theory xHOL_Syntax 

imports 
  Tools
  xHOL_Syntax_Chap

begin

(*<*)

text {*

Put these first so as to cope with loss of old syntax and allow for need 
to put in reverse order. 
Possibly put in separate theory for inclusion as appendix?

*}

no_translations
  "SOME x. P" == "CONST Eps (%x. P)"

no_translations
  "SUM x|P. t" => "CONST setsum (%x. t) {x. P}"
  "\<Sum>x|P. t" => "CONST setsum (%x. t) {x. P}"

no_translations -- {* Beware of argument permutation! *}
  "SUM i:A. b" == "CONST setsum (%i. b) A"
  "\<Sum>i\<in>A. b" == "CONST setsum (%i. b) A"

no_translations
  "PROD x|P. t" => "CONST setprod (%x. t) {x. P}"
  "\<Prod>x|P. t" => "CONST setprod (%x. t) {x. P}"

no_translations -- {* Beware of argument permutation! *}
  "PROD i:A. b" == "CONST setprod (%i. b) A" 
  "\<Prod>i\<in>A. b" == "CONST setprod (%i. b) A" 

no_translations
  "{x. P}" == "CONST Collect (%x. P)"

no_translations
  "INT x y. B"  == "INT x. INT y. B"
  "INT x. B"    == "CONST INTER CONST UNIV (%x. B)"
  "INT x. B"    == "INT x:CONST UNIV. B"
  "INT x:A. B"  == "CONST INTER A (%x. B)"

no_translations
  "UN x y. B"   == "UN x. UN y. B"
  "UN x. B"     == "CONST UNION CONST UNIV (%x. B)"
  "UN x. B"     == "UN x:CONST UNIV. B"
  "UN x:A. B"   == "CONST UNION A (%x. B)"

no_translations
  "SOME x. P" == "CONST Eps (%x. P)"

no_translations
  "ALL x:A. P" == "CONST Ball A (%x. P)"
  "EX x:A. P" == "CONST Bex A (%x. P)"
  "EX! x:A. P" => "EX! x. x:A & P"
  "LEAST x:A. P" => "LEAST x. x:A & P"

no_translations
  "SIGMA x:A. B" == "CONST Sigma A (%x. B)"

no_translations
  "INF x y. B"   == "INF x. INF y. B"
  "INF x. B"     == "CONST INFI CONST UNIV (%x. B)"
  "INF x. B"     == "INF x:CONST UNIV. B"
  "INF x:A. B"   == "CONST INFI A (%x. B)"
  "SUP x y. B"   == "SUP x. SUP y. B"
  "SUP x. B"     == "CONST SUPR CONST UNIV (%x. B)"
  "SUP x. B"     == "SUP x:CONST UNIV. B"
  "SUP x:A. B"   == "CONST SUPR A (%x. B)"

no_translations
  "GREATEST x WRT m. P" == "CONST GreatestM m (%x. P)"

no_translations
  "LEAST x WRT m. P" == "CONST LeastM m (%x. P)"

text {*

We adjust existing notation that we wish to use.

*}

(*J: 19/11/2015 These aren't known (without Multivariate_Analysis and pGCL)
no_notation
  refines (infix "\<sqsubseteq>" 70)

notation
  refines (infix "\<prefines>" 70)

no_notation
  exp_conj (infixl "&&" 71)

notation
  exp_conj (infixl "\<pconj>" 71)
*)

(*>*)

text {*

%The default HOL syntax is massaged to be more familiar to
%the average Z user. In addition some simple inference
%rules are developed.

In this chapter we summarize the syntax of Higher Order Logic (HOL) as it will
be used in the mechanisations underlying the {\HiVe} tool -- and, indeed, in
formal modelling work undertaken by the {\hasc} while the tool
is being developed.  Isabelle's HOL is distributed with a syntax that we have
found not always comfortable to use in specifications and
other mathematical treatments.  Instead, we prefer to use the Z (pronounced 'zed')
 syntax.
It is more precise in its representation of set comprehension, and uniform
across all forms of bindings.  Thus, the major motivation for the reworking
here is to massage HOL syntax to be more familiar to the average Z user.

We also use this opportunity to record the tricks we have developed for
preparing high-quality output in the Isabelle/Isar environment.  In no sense do
we try to make this a self-contained explanation of how to use Isar, but rather
provide tips which other users may find useful.

Thereto, we begin with a short section on how to leverage the {\LaTeX} macro
system through \verb+isatool+ -- Isar's session management tool which generates the
{\LaTeX} output.  We then simply present the Z-like syntax.  This presentation
is divided into sections according to the mathematical application of the
syntax contained.
*}


section {* Isar and literate formal modelling *}

text{*

Isar~\cite{Isabelle2005}\footnote{The 2005 version of Isabelle is used exclusively
in this work. Conversion to the 2007 version is a 
large undertaking that we have postponed
to the next version of this work.} is Isabelle's Semi-Automated Reasoning environment.  
From its introduction in the 1999 distribution,
Isar has grown to be a very impressive
tool for the production of literate formal theories and proofs.  The currently
most advanced method for a user to interface to Isar is through an
emacs-based~\cite{emacs} editing tool, Proof-General~\cite{proofgeneral}.  The
user -- whether entering descriptive text, constructing a formal logic, or
carrying out a formal proof -- types Isar commands with appropriate arguments
into a ``.thy'' file in an emacs buffer inside Proof-General and sends the
buffer to Isabelle incrementally as it is built up.  The resulting theories are
interpreted by the \verb+isatool+ session manager, and converted to 
{\LaTeX}~\cite{Lamport:1994fj} files
which can be post-processed as usual to produce PDF~\cite{pdf:v6} documents.  
The
user directs the {\LaTeX} interaction through an overall ``root.tex'' file.  The
uniformity of input, and the incremental nature of the construction, mean that
the resulting documents can be logically laid out with any desired narrative
flow.  As usual with {\LaTeX}, any informal text or pictures and diagrams can be
easily inserted, greatly enhancing readability.

Another crucial ingredient in readability -- evident in any technical document,
mathematical paper, or textbook -- is the use of succint and precise notation.
Here we gather all such devices together under the rubric {\em syntax}.  Part
of Isar's power derives from the ability to use different input and output
syntax\footnote{
Input syntax is that which Isar parses to construct terms,
while output syntax is that which is sends to the screen or through
{\tt isatool} to {\LaTeX} documents.  A given mode can be one or the other, or
both.}
modes.  Different syntax can be defined in the different modes, and
used for different purposes.  For example, the default syntax mode allows
for pretty-printing via \LaTeX\ macros -- the standard HOL syntax is in this
mode, and can be extended in a user-defined \LaTeX ``.sty'' file.
Proof-General itself optionally utilises the {\em x-symbols} mode, which
provides a rudimentary pretty-printing facility for obtaining syntax in the
screen representation of the emacs input buffer.  The user may introduce
further modes, and since we are introducing rival syntax this is indeed what we
will do.  But first, let us briefly describe the {\HiVe} program and where
the current description fits in.  
*}

text{*

Eventually, the {\HiVe} will provide sophisticated screen and print
presentation layers that are significantly superior to existing Isabelle 
presentation techniques. However, for the moment, we are able to mimic some of
the desired functionality of the {\HiVe} Writer by adopting stricted coding practices 
together with some simple text processing automation.

We introduce the @{text "zed"} syntax mode to support the new Z-like syntax.  A
significant amount of the existing HOL language (at least that required 
to support the Z
toolkit), and all new constructs, are given @{text "zed"} syntax.  The @{text
"zed"} mode is both an input and output mode.  Any new {\em input} syntax is
defined solely for the newly defined @{text "zed"} mode.  However, the @{text
"zed"} syntax is specifically aimed at producing high quality {\LaTeX} output in
a Z-like syntax, so it is not very readable in ascii or Proof-General input
mode (which the developer is working with).  The x-symbols output
modes{\footnote{Of course, the output mode cannot be used to create legal
inputs. This not entirely satisfactory situation will be resolved with the
first stage of the {\HiVe} user interface tool.}} help with the reading of
goal states in Proof-General sessions.  Thus, our general approach to syntax
modification is to define only new {\em output} syntax for ascii and x-symbols
syntax modes.  However, it really is useful to have the same output and input
syntax, so where acceptable we do make use of xsymbols-supported tokens
in the Zed input syntax.

*}

section {* Post-processing Isar for better {\LaTeX} output *}

text {*
Let us take a moment to explain our use of syntax modes, and our embellishments on
suggested Isabelle practise.  

There are two styles of {\LaTeX} tokens used in Isabelle. They differ primarily
in how they are converted for {\LaTeX} output. 
\begin{enumerate}
\item
The \verb+\<token>+ style is converted to \verb+{\isasymtoken}+;
\item
The \verb+\<^token>+ is converted to \verb+\isactrltoken+. 
\end{enumerate}
The presence of enclosing braces in the translation of the former style means
that its corresponding {\LaTeX} macro cannot have arguments. Syntactic
operators which require sophisticated {\LaTeX} typesetting of their arguments  
must be given syntax in the latter form.

As an example, consider an operator @{text "OP"} which displays its
argument $x$ as a subscript to an operator symbol $\cal O$,
thus ${\cal O}_x$.
In order to achieve this, we might define the following @{text "zed"} mode
syntax (verbatim).

\begin{verbatim}
syntax (zed)
  OP :: "'a => 'a" ("\<^lOP>_\<^rOP>")
\end{verbatim}

Corresponding to this we define a {\LaTeX} macro \verb+\isactrllOP+ as
follows.

\begin{verbatim}
\def\isactrllOP#1\isactrlrOP{\isamath{\cal O}\isactrlsub{#1}}
\end{verbatim}

This macro definition must occur in the preamble to \verb+document/root.tex+
or else in a style file included therein.

A complication to this approach is the fact that the {\LaTeX} processor
will not correctly nest applications of the \verb+\isactrllOP+ macro.
Thus a term such as 
\begin{verbatim}
\<^lOP>\<^lOP>x\<^rOP>\<^rOP>
\end{verbatim}
will not be correctly typeset. The first occurrence of \verb+\isactrlrOP+ is
matched with the first \verb+\isactrllOP+, leaving the second
\verb+\isactrllOP+ and \verb+\isactrlrOP+ unmatched.  It seems this cannot be
avoided without intervening in Isabelle's document preparation process. One aim
of {\HiVe} is to rationalise the document preparation process to use a more
standard approach to literate programming, generating the document and the
theory through separate technologies.

The other annoyance in Isabelle document generation is the
difficulty in using exotic syntax for variables.  
Isabelle 2005~\cite{Isabelle2005}
offers a useful, but fixed, collection of characters for constructing
identifiers. These include italic and normal Roman characters, Greek characters,
caligraphic characters, Gothic characters, and sub-/super-scripted indices. 
Although this is an improvement on older
versions of Isabelle, it is still unnecessarily constrictive.
For example, it is not possible to typeset type 
generics in the traditional manner using lower
case Greek, or to use blackboard-bold font faces, 
or to use abstract symbols for variable names.

*}

text_raw {*

\begin{table}
\centering{
\begin{tabular}{|l|l|}
\hline
\verb+'a+, \verb+'b+, \verb+'c+, \verb+'d+ 
  & @{text "'a"}, @{text "'b"}, @{text "'c"}, @{text "'d"} \\
\hline
\verb+'A+, \verb+'B+, \verb+'C+, \verb+'D+ 
  & @{text "'A"}, @{text "'B"}, @{text "'C"}, @{text "'D"} \\
\hline
\verb+x_u_2+, \verb+x_d_2+ &
  @{text "x_u_2"}, @{text "x_d_2"} \\
\hline
\verb+BS_alpha+, \verb+BS_sum+ & 
  @{text "BS_alpha"}, @{text "BS_sum"} \\
\hline
\verb+BB_N+ & 
  @{text "BB_N"} \\
\hline
\verb+FR_N+ & 
  @{text "FR_N"} \\
\hline
\verb+BF_N+ & 
  @{text "BF_N"} \\
\hline
\verb+IT_N+ & 
  @{text "IT_N"} \\
\hline
\verb+RM_N+ & 
  @{text "RM_N"} \\
\hline
\verb+SF_N+ & 
  @{text "SF_N"} \\
\hline
\verb+TT_N+ & 
  @{text "TT_N"} \\
\hline
\verb+CL_A+ 
& @{text "CL_A"} 
\\
\hline
\verb+VC_x+ 
& @{text "VC_x"}
\\
\hline
\verb+\<^token>[:arg:]+ 
& \verb+@{text "\<^token>[:arg:]"}+
\\
\hline
\verb+\<^token>{:arg:}+ 
& \verb+@{text "\<^token>{:arg:}"}+
\\
\hline
\end{tabular}}
\caption{Isabelle post-processor conventions}
\label{tab:conv}
\end{table}

*} 

text {*

We address all of these problems by adopting an Isabelle post-processor which
replaces occurrences of certain character combinations to produce more
acceptable {\LaTeX} output. The conversion conventions are as shown in
Table~\ref{tab:conv}. The actual conversion script is in \verb+postisa+, which
uses \verb+postisa.sed+.  The sed script is given in Appendix~\ref{app:sed},
where we also explain how to incorporate it into the documentation preparation
process in a given Isabelle session.

The final two lines of the table represent our approach to handling the
{\LaTeX} argument identification problem discussed above. By enclosing
arguments to @{text "zed"} mode syntactic operators in matching
\verb+{:+/\verb+:}+ delimiters and then post-processing these to standard
{\LaTeX} \verb+{+/\verb+}+ delimiters we finesse the problem neatly.

Thus, for our example above we make the following @{text "zed"} mode
syntax declaration:
\begin{verbatim}
syntax (zed)
  OP :: "'a => 'a" ("\<^OP>{:_:}") 
\end{verbatim}
and accompany it with the following {\LaTeX} macro:
\begin{verbatim}
\def\isactrlOP#1{\isamath{\cal O}\isactrlsub{#1}}
\end{verbatim}
The nesting is then straightforward: one simply writes what is desired. For example,
the nesting above is just
\begin{verbatim}
\<^OP>{:\<^OP>{:x:}:}
\end{verbatim}
which produces the result
\[
{\def\isactrlOP#1{\isamath{\cal O}\isactrlsub{#1}}
\isactrlOP{\isactrlOP{x}}} \, .
\]

Sometimes it is useful to have optional parameters to a {\LaTeX} macro, and
this is usually indicated by enclosing them in square brackets.  We also
support this: the syntax is introduced exactly as above, but with
\verb+[:+/\verb+:]+ delimiters.

*}

subsection {* Avoiding syntax clashes in different theories *}

text {*

An important convention we adopt is the use of full path names when defining
syntax for constants. This overcomes the Isabelle shortcoming of not using
namespaces on AST (abstract Syntax Tree) operators.  If you wish syntax to
respect namespaces you must explicitly indicate this.  For example, if the
constant is declared in a theory \verb+Test+, we would declare:
\begin{verbatim}
syntax (zed)
  "Test.OP" :: "'a => 'a" ("\<^OP>{:_:}") 
\end{verbatim}
Without the full path declaration, a later (or earlier) declaration of syntax
for an @{text "OP"} constant in another theory would interfere destructively
with the current one.

We now proceed with declaring the Z-like syntax. 

*}


section {* Term Manipulators *}

text {*

We introduce syntax to help analyse syntactic translations.

The @{text "\<^prtm>{:_:}"} operator prints term structure prior 
to the application of parse translations.

*}

syntax (zed)
  "_xHOL_Syntax\<ZZ>prtm" :: "any => any" ("\<^prtm>{:_:}")

parse_translation {*

let
  fun prtm_tr _ [t] = print_term t;
in
  [("_xHOL_Syntax\<ZZ>prtm", prtm_tr)]
end

*}

text {*


The @{text "\<^prid>{:_:}"} operator prints term structure 
subsequent to the application of parse translations.

*}


definition
  prid :: "'a => 'a"
where
  prid_def: "prid a == a"

notation (zed)
  prid ("\<^prid>{:_:}")

print_translation {*

let
  fun prtm_tr' _ [t] = print_term t;
in
  [(@{const_syntax "xHOL_Syntax.prid"}, prtm_tr')]
end

*}

text {*

We introduce a general syntax for instantiating free variables in the types of constants. 
Since only the free variables are addressed, this can save considerable effort in addressing all of the
type constructors in the type definition.

*}

syntax
  "_xHOL_Syntax\<ZZ>type_inst" :: "[logic, types] => logic" ("_-[_]" [1000, 0] 1000)

parse_translation {*

let 

fun type_inst_tr ctxt [term, typs] =
let
(*

fun mk_sorts (Const("_types", _) $ T $ Ts) = (Syntax.term_sorts T)@(mk_sorts Ts)
 |  mk_sorts T = Syntax.term_sorts T;

val tsorts = mk_sorts typs;


val get_sort  =
  let
    val tsig = Proof_Context.tsig_of ctxt;

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

fun mk_types (Const("_types", _) $ T $ Ts) 
    = (Syntax.typ_of_term get_sort T)::(mk_types Ts)
 |  mk_types T = [Syntax.typ_of_term get_sort T];
*)

fun mk_types (Const("_types", _) $ T $ Ts) 
    = (Syntax_Phases.decode_typ T)::(mk_types Ts)
 |  mk_types T 
    = [Syntax_Phases.decode_typ T];

val const_space = Proof_Context.consts_of ctxt;

fun unmark nm =
  case try (unprefix "\<^const>") nm of
    SOME c => c
  | NONE => nm;

fun mk_name (Free(nm, _)) 
      = Consts.intern const_space (unmark nm)
 |  mk_name (Const("_constrain", _) $ Free(nm, _) $ _)
      = Consts.intern const_space (unmark nm)
 |  mk_name (Const(nm, _)) 
      = Consts.intern const_space (unmark nm);
 
val Ts = mk_types typs;

val inm = mk_name (term);

in
  Sign.mk_const (Proof_Context.theory_of ctxt) (inm, Ts)
end;

in

[ ("_xHOL_Syntax\<ZZ>type_inst", type_inst_tr) ]

end

*}

section {* @{theory Pure} notations *}

text {*

The function type symbol is changed syntactically 
to agree with the Z standard's use of single shafted arrows, 
that is @{text "(_ \<rightarrow> _)"}.

*}

type_notation (xsymbols)
  "fun" ("(_/ \<rightarrow> _)" [1, 0] 0)

syntax (xsymbols)
  "_bracket" :: "[types, type] => type" ("([_]/ \<rightarrow> _)" [0, 0] 0)

setup {*

let
  val ra = "\\"^"<"^"Rightarrow"^">";
  val typ = Simple_Syntax.read_typ;
  val tycon = Lexicon.mark_type;

in

Sign.del_modesyntax_i (Symbol.xsymbolsN, true)
   [(tycon "fun",         
      typ "type => type => type",   
      Mixfix ("(_/ "^ra^" _)", [1, 0], 0)),
    ("_bracket",          
      typ "types => type => type",  
      Mixfix ("([_]/ "^ra^" _)", [0, 0], 0))]
end;

*}
    
text {*

New notations are introduced for some of the basic logical connectives.
The existing Isabelle notations have several problems from a 
Z-practitioner's viewpoint.

\begin{itemize}

\item The use of the fullstop as the binder separator does not
 parse well in general text and
 tends to disappear on the printed page. 
 The Z-style @{text "\<bullet>"} separator is introduced for
 binders and schema-text style quantifier qualification is also introduced; 
 for the lambda and meta-all operators in Pure and also throughout HOL as
 described below.

\item The @{text "\<defs>"} notation is introduced for meta-equality in
definitional axioms.

\item The @{text "\<Longrightarrow>"} character for meta-implication is cumbersome.
The (@{text "\<turnstile>"}) character is adopted instead.

\end{itemize}

*}


syntax (zed)
  "_xHOL_Syntax\<ZZ>defmeq" :: "['a::{}, 'a] \<rightarrow> prop" (infixr "\<defs>" 2)

translations
  "_xHOL_Syntax\<ZZ>defmeq" \<rightharpoonup> "op =="

(*J: 19/11/2015 Required for Multivariate_Analysis import
no_notation
  inner (infix "\<bullet>" 70)
*)

no_syntax (xsymbols)
  "\<^const>all_binder" :: "[idts, prop] \<rightarrow> prop" ("(3\<And>_./ _)" [0, 0] 0)
  "\<^const>==>" :: "[prop, prop] \<rightarrow> prop" (infixr "\<Longrightarrow>" 1)
  "_bigimpl" :: "[asms, prop] \<rightarrow> prop" ("((1\<lbrakk>_\<rbrakk>)/ \<Longrightarrow> _)" [0, 1] 1)
  "_lambda" :: "[pttrns, 'a] \<rightarrow> logic" ("(3\<olambda>_./ _)" [0, 3] 3)

syntax (xsymbols)
  "\<^const>all_binder" :: "[idts, prop] \<rightarrow> prop" ("(3\<And> _ \<bullet>/ _)" [0, 0] 0)
  "\<^const>==>" :: "[prop, prop] \<rightarrow> prop" ("(3(_)/  \<turnstile> (_))" [2, 1] 1)
  "_bigimpl" :: "[asms, prop] \<rightarrow> prop" ("((3\<lbrakk>_\<rbrakk>)/ \<turnstile> _)" [0, 1] 1)
  "_lambda" :: "[pttrns, 'a] \<rightarrow> logic" ("(3\<olambda> _ \<bullet>/ _)" [0, 3] 3)

section {* @{theory "HOL"} Notations *}

text {*

We introduce blackboard bold notations for the booleans.

*}

type_notation (xsymbols)
  bool ("\<bool>") 

text {*

We introduce shortened forms for the boolean constructors.

*}

notation (xsymbols)
  "True" ("\<True>") and 
  "False" ("\<False>")

text {*

We intend to use the @{text "|"} character extensively in schematext notations, 
so remove it as the
ASCII disjunction operator.

*}

no_notation
  "HOL.disj"  (infixr "|" 30)

text {*

We prefer Z-like @{text "(_ \<Rightarrow> _)"} over @{text "(_ \<longrightarrow> _)"} for implication.

*}

notation (xsymbols)
  "implies" (infixr "\<Rightarrow>" 25)

no_notation (xsymbols)
  "implies" (infixr "\<longrightarrow>" 25)

text {*

The @{text "(_ \<Leftrightarrow> _)"} notation is introduced for equality on
booleans, rather than @{text "(_ \<longleftrightarrow> _)"}. 
It binds more weakly than @{text "(_ = _)"} to allow easy interactions with atomic equalities,
eg @{text "a = b \<Leftrightarrow> 0 < a"} rather than @{text "(a = b) \<Leftrightarrow> (0 < a)"}.

*}


no_notation (xsymbols)
  iff  (infixr "\<longleftrightarrow>" 25)

notation (xsymbols)
  iff  (infixr "\<Leftrightarrow>" 25)

typed_print_translation {*
let
  val iffT = boolT --> boolT --> boolT;
  fun trT' _ typ [a, b] = 
    if typ = iffT then
      Const(@{const_syntax "HOL.iff"}, typ) $ a $ b
    else
      raise Match;
in
  [(@{const_syntax "HOL.eq"}, trT')]
end;
*}

text {*

Prominent {\LaTeX} notations are introduced for
@{text "\<case>"} and @{text "\<let>"} (including a @{text "\<where>"} variant).  

*}

syntax (xsymbols)
  "_Let" :: "[letbinds, 'a] \<rightarrow> 'a" ("(\<let> (_)/ \<bullet> (_))" [0, 10] 10)

syntax (xsymbols)
  "_xHOL_Syntax\<ZZ>Where" :: "['a, letbinds] \<rightarrow> 'a" ("((_)//\<where>//   (_))" [10,10] 10)

translations
  "_xHOL_Syntax\<ZZ>Where x p" \<rightharpoonup> "_Let p x"

no_syntax
  "_case_syntax" :: "['a, cases_syn] \<rightarrow> 'b"  ("(case _ of/ _)" 10)
  "_case1" :: "['a, 'b] \<rightarrow> case_syn"  ("(2_ =>/ _)" 10)

syntax
  "_case_syntax" :: "['a, cases_syn] \<rightarrow> 'b"  ("(case _ of/ _ esac)")
  "_case1" :: "['a, 'b] \<rightarrow> case_syn"  ("(2_ -->/ _)" 10)

no_syntax (xsymbols)
  "_case1" :: "['a, 'b] \<rightarrow> case_syn"  ("(2_ \<Rightarrow>/ _)" 10)

syntax (xsymbols)
  "_case1" :: "['a, 'b] \<rightarrow> case_syn" ("(2_ \<longrightarrow>/ _)" 10)

syntax (xsymbols)
  "_case_syntax" :: "['a, cases_syn] \<rightarrow> 'b" ("(\<case> _ \<of>/ _ \<esac>)")

text {*

We introduce Z-like notations for the @{text "if _ then _"} operator, 
including an @{text "elif"} form.

*}

nonterminal
  alts

syntax (xsymbols)
  "_xHOL_Syntax\<ZZ>alts" :: "[logic, alts] \<rightarrow> logic" ("(\<if> _//   _//\<fi>)" [0, 0] 1000)
  "_xHOL_Syntax\<ZZ>altn" :: "[logic, logic, alts] \<rightarrow> alts" ("\<then> _//\<elif> _//   _")
  "_xHOL_Syntax\<ZZ>alt1" :: "[logic, logic] \<rightarrow> alts" ("\<then> _//   \<else> _")

translations
  "_xHOL_Syntax\<ZZ>alts a (_xHOL_Syntax\<ZZ>altn x b y)" \<rightharpoonup> "CONST HOL.If a x (_xHOL_Syntax\<ZZ>alts b y)"
  "_xHOL_Syntax\<ZZ>alts a (_xHOL_Syntax\<ZZ>alt1 x y)" \<rightharpoonup> "CONST HOL.If a x y"

print_translation {*
let
  fun 
    alts_tr x (Const(@{const_syntax "HOL.If"}, _) $ a $ y $ z) = 
      (Const("_xHOL_Syntax\<ZZ>altn", dummyT) $ x $ a $ (alts_tr y z))
  | alts_tr x y = 
      (Const("_xHOL_Syntax\<ZZ>alt1", dummyT) $ x $ y);
  fun If_tr _ [a, x, y] = Const("_xHOL_Syntax\<ZZ>alts", dummyT) $ a $ alts_tr x y;
in
  [(@{const_syntax "HOL.If"}, If_tr)]
end
*}

text {*

We introduce pretty notation for the undefined value.

*}

notation (zed)
  "HOL.undefined" ("\<arb>")

section {* @{theory Set} Notations *}

text {*

\label{sec:schematext}
The standard Isabelle set notation is unsatisfactory, including use before declaration
and the weak dot separator. We change it
to a Z-like notation, where the bound variables are declared
before use and a schema-text form is adopted.

*}


definition
  "eind Pf = (\<olambda> z \<bullet> Ex (\<olambda> x \<bullet> z = snd (Pf x) \<and> fst (Pf x)))"

declare 
  eind_def [THEN fun_cong, simp] 

no_syntax
  "_Coll" :: "pttrn \<rightarrow> bool \<rightarrow> 'a set"    ("(1{_./ _})")

no_syntax
  "_Collect" :: "idt \<rightarrow> 'a set \<rightarrow> bool \<rightarrow> 'a set"    ("(1{_ :/ _./ _})")

no_syntax (xsymbols)
  "_Collect" :: "idt \<rightarrow> 'a set \<rightarrow> bool \<rightarrow> 'a set"    ("(1{_ \<in>/ _./ _})")

no_syntax
  "_Setcompr" :: "'a \<rightarrow> idts \<rightarrow> bool \<rightarrow> 'a set"    ("(1{_ |/_./ _})")

nonterminal
  schematext

syntax ("" output)
  "_xHOL_Syntax\<ZZ>SchemaQ"  :: "[idt, logic] \<rightarrow> schematext" ("(1_ |/ _)")
  "_xHOL_Syntax\<ZZ>SchemaQT" :: "[idts, logic, logic] \<rightarrow> schematext" ("(1_ |/ _ ./ _)")
  "_xHOL_Syntax\<ZZ>SchemaT"  :: "[idts, logic, logic] \<rightarrow> schematext" ("(1_ ./ _)")

syntax (xsymbols)
  "_xHOL_Syntax\<ZZ>SchemaQ"  :: "[idt, logic] \<rightarrow> schematext" ("(_ |/ _)" [0, 10] 10)
  "_xHOL_Syntax\<ZZ>SchemaQT" :: "[idts, logic, logic] \<rightarrow> schematext" ("(_ |/ _ \<bullet>/ _)" [0, 10, 10] 10)
  "_xHOL_Syntax\<ZZ>SchemaT"  :: "[idts, logic] \<rightarrow> schematext" ("(_ \<bullet>/ _)" [0, 10] 10)

ML {*

local
  val ex_tr = snd (Syntax_Trans.mk_binder_tr ("prod_case ", @{const_syntax prod_case}));
 
  fun schemaQ_tr (idt, b) =
    let
      val exP = (Syntax_Trans.abs_tr [idt, b]);
    in exP end;


  fun schemaQT_tr ctxt (idts, b, e) =
    let
      val P = absdummy (Type(@{type_name "unit"}, [])) (Syntax.const @{const_syntax Pair} $ b $ e);
      val exP = ex_tr ctxt [idts, P];
    in Syntax.const @{const_syntax "eind"} $ exP end;
 
  fun schemaT_tr ctxt (idts, e) =
    let
      val P 
        = absdummy (Type(@{type_name "unit"}, []))
            (Syntax.const @{const_syntax Pair} $ Syntax.const @{const_syntax True} $ e);
      val exP = ex_tr ctxt [idts, P];
    in Syntax.const @{const_syntax "eind"} $ exP end;

in

fun 
  schematext_tr opr _ 
    [Const(@{syntax_const "_xHOL_Syntax\<ZZ>SchemaQ"}, _) $ idt $ b] 
  = opr $ schemaQ_tr (idt, b)
| schematext_tr opr ctxt 
    [Const(@{syntax_const "_xHOL_Syntax\<ZZ>SchemaQT"}, _) $ idts $ b $ e] 
  = opr $ schemaQT_tr ctxt (idts, b, e)
|  schematext_tr opr ctxt 
     [Const(@{syntax_const "_xHOL_Syntax\<ZZ>SchemaT"}, _) $ idts $ e] 
   = opr $ schemaT_tr ctxt (idts, e);

end;

*}

ML {*

  val ex_tr' = snd (Syntax_Trans.mk_binder_tr' (@{const_syntax prod_case}, "DUMMY"));
  
  fun schemaQT_tr' ctxt 
        (Const(@{const_syntax prod_case}, _) $ abs) =
  let
    val (_ $ idts $ Abs (_, _, Q_T)) = ex_tr' ctxt [abs];
  in
    case Q_T of 
      Const(@{const_syntax Pair}, _) $ Const(@{const_syntax True}, _) $ T =>
        (Syntax.const @{syntax_const "_xHOL_Syntax\<ZZ>SchemaT"} $ idts $ T)
    | Const(@{const_syntax Pair}, _) $ Q $ T =>
        (Syntax.const @{syntax_const "_xHOL_Syntax\<ZZ>SchemaQT"} $ idts $ Q $ T)

  end;

  fun schematext_tr' opr _ [Abs abs] = 
    let
      val (v, p) = Syntax_Trans.atomic_abs_tr' abs;
    in 
      opr $ (Syntax.const @{syntax_const "_xHOL_Syntax\<ZZ>SchemaQ"} $ v $ p) 
    end
   |  schematext_tr' opr ctxt [Const(@{const_syntax eind}, _) $ t] 
        = opr $ (schemaQT_tr' ctxt t);
  
*}

syntax (xsymbols output)
  "_xHOL_Defs\<ZZ>eindapply" :: "logic \<rightarrow> schematext \<rightarrow> logic" ("[ _ \<TTurnstile> _ ]")

print_translation {*

let

fun eindB_tr' ctxt [st, fa] 
  = schematext_tr' (Const(@{syntax_const "_xHOL_Defs\<ZZ>eindapply"}, dummyT) $ fa) ctxt 
      [Const(@{const_syntax eind}, dummyT) $ st]

in
  [(@{const_syntax "eind"}, eindB_tr')]
end

*}

syntax
  "_xHOL_Syntax\<ZZ>coll" :: "schematext \<rightarrow> logic" ("(1{ _ })" [10] 1000)

parse_translation {*

  [(@{syntax_const "_xHOL_Syntax\<ZZ>coll"}, 
     schematext_tr (Syntax.const @{const_syntax Collect}))]
  
*}

print_translation {*

  [(@{const_syntax "Collect"}, 
     schematext_tr' (Const(@{syntax_const "_xHOL_Syntax\<ZZ>coll"}, dummyT)))] 
*}  

text {*

We introduce an Eindhoven style of boolean quantification as well.

*}

no_notation (xsymbols)
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1  (binder "\<exists>!" 10)

no_notation (HTML output)
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1  (binder "\<exists>!" 10)

no_notation (HOL)
  All  (binder "! " 10) and
  Ex  (binder "? " 10) and
  Ex1  (binder "?! " 10)

text {* 

It seems removing any binder notation looses track of the associated binder name, so we redeclare
ASCII versions for the quantifiers.

*}

notation (HOL)
  All  (binder "! " 10) and
  Ex  (binder "? " 10) and
  Ex1  (binder "?! " 10)

text {* 

We use schematext versions of the boolean quantifiers.

*}

syntax
  "_xHOL_Syntax\<ZZ>all" :: "schematext \<rightarrow> logic" ("(1\<forall> _)" [10] 10)

translations
  "(\<forall> xs | q \<bullet> t)" \<rightharpoonup> "(! xs. q \<Rightarrow> t)"
  "(\<forall> xs \<bullet> t)" \<rightleftharpoons> "(! xs. t)"

syntax
  "_xHOL_Syntax\<ZZ>ex" :: "schematext \<rightarrow> logic" ("(1\<exists> _)" [10] 10)

translations
  "(\<exists> xs | q \<bullet> t)" \<rightharpoonup> "(? xs. q \<and> t)"
  "(\<exists> xs \<bullet> t)" \<rightleftharpoons> "(? xs. t)"

syntax
  "_xHOL_Syntax\<ZZ>ex1" :: "schematext \<rightarrow> logic" ("(1\<exists>\<subone> _)" [10] 10)

translations
  "(\<exists>\<subone> xs | q \<bullet> t)" \<rightharpoonup> "(?! xs. q \<and> t)"
  "(\<exists>\<subone> xs \<bullet> t)" \<rightleftharpoons> "(?! xs. t)"

text {*

It may be worth including an ability to declare bounded variables i.e. 
@{text "x \<in> X | P \<bullet> t"} in the declaration part rather than
@{text "x::'a | x \<in> X \<and> P \<bullet> t"} spread across declaration and predicate parts. 
This would translate to a bounded collect 
@{text "BCollect X (\<olambda> _uu \<bullet> (\<exists> x | P \<bullet> _uu = t)) 
\<equiv> X \<inter> Collect (\<olambda> _uu \<bullet> (\<exists> x | P \<bullet> _uu = t))"} 
and may allow more targetted reasoning rules about variable bounds. 
On the other hand this form is natural to the full scale 
HiVe Z-like modelling environment, so may be a waste of time at the HOL level.

*}

lemma eCollectI: "(\<exists> x \<bullet> z = snd (Pf x) \<and> fst (Pf x)) \<turnstile> z \<in> Collect (eind Pf)"
  by (auto simp add: eind_def)

lemma eCollectD: "z \<in> Collect (eind Pf) \<turnstile> (\<exists> x \<bullet> z = snd (Pf x) \<and> fst (Pf x))"
  by (auto simp add: eind_def)

lemma mem_eCollect_eq [iff]:
  "z \<in> Collect (eind Pf) \<Leftrightarrow> (\<exists> x \<bullet> z = snd (Pf x) \<and> fst (Pf x))"
  by (auto simp add: eind_def)

text {*

Having set up this schema text infrastructure it is now easy to defined new schema 
text based syntax operators.

*}


no_syntax
  "_INF1"     :: "pttrns \<rightarrow> 'b \<rightarrow> 'b"           ("(3INF _./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b"  ("(3INF _:_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<rightarrow> 'b \<rightarrow> 'b"           ("(3SUP _./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b"  ("(3SUP _:_./ _)" [0, 0, 10] 10)

no_syntax (xsymbols)
  "_INF1"     :: "pttrns \<rightarrow> 'b \<rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<rightarrow> 'b \<rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_INF"      :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b"  ("(3\<Sqinter> _ \<in> _ \<bullet>/ _)" [0, 0, 10] 10)
  "_SUP"      :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b"  ("(3\<Squnion> _ \<in> _ \<bullet>/ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_xHOL_Syntax\<ZZ>st_Sup" :: "schematext \<rightarrow> logic" ("\<Squnion> _" 0)
  "_xHOL_Syntax\<ZZ>st_Inf" :: "schematext \<rightarrow> logic" ("\<Sqinter> _" 0)

translations
  "_xHOL_Syntax\<ZZ>st_Sup S" \<rightleftharpoons> "CONST Sup (_xHOL_Syntax\<ZZ>coll S)"
  "_xHOL_Syntax\<ZZ>st_Inf S" \<rightleftharpoons> "CONST Inf (_xHOL_Syntax\<ZZ>coll S)"

no_syntax
  "_INTER1"     :: "pttrns => 'b set => 'b set"           ("(3INT _./ _)" [0, 10] 10)
  "_INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3INT _:_./ _)" [0, 0, 10] 10)

no_syntax (xsymbols)
  "_INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>_./ _)" [0, 10] 10)
  "_INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>_\<in>_./ _)" [0, 0, 10] 10)

no_syntax (latex output)
  "_INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "_INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 0, 10] 10)

no_syntax
  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3UN _./ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3UN _:_./ _)" [0, 0, 10] 10)

no_syntax (xsymbols)
  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>_./ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 0, 10] 10)

no_syntax (latex output)
  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 0, 10] 10)

syntax (xsymbols output)
  "_UNION"      :: "[pttrn, 'a set, 'b set] \<rightarrow> 'b set" ("(3\<Union> _ \<in> _ \<bullet>/ _)" 10)
  "_INTER"      :: "[pttrn, 'a set, 'b set] \<rightarrow> 'b set" ("(3\<Inter> _ \<in> _ \<bullet>/ _)" 10)

syntax (xsymbols)
  "_xHOL_Syntax\<ZZ>st_Union" :: "schematext \<rightarrow> logic" ("\<Union> _" 0)
  "_xHOL_Syntax\<ZZ>st_Inter" :: "schematext \<rightarrow> logic" ("\<Inter> _" 0)

translations
  "_xHOL_Syntax\<ZZ>st_Union S" \<rightleftharpoons> "CONST Union (_xHOL_Syntax\<ZZ>coll S)"
  "_xHOL_Syntax\<ZZ>st_Inter S" \<rightleftharpoons> "CONST Inter (_xHOL_Syntax\<ZZ>coll S)"

text {*

Several standard HOL operators are most naturally defined on sets, but have remained defined on predicates in Isabelle 2013.

We remove the binder syntax for definite and indefinite choice operator, so as to allow the introduction of set based versions elsewhere~(Sec~\ref{sec:set_choice}).

*}

no_syntax 
  "_The" :: "[pttrn, bool] \<rightarrow> 'a"  ("(3THE _./ _)" [0, 10] 10)

no_syntax (epsilon)
  "_Eps"        :: "[pttrn, bool] => 'a"    ("(3\<some>_./ _)" [0, 10] 10)
no_syntax (HOL)
  "_Eps"        :: "[pttrn, bool] => 'a"    ("(3@ _./ _)" [0, 10] 10)
no_syntax
  "_Eps"        :: "[pttrn, bool] => 'a"    ("(3SOME _./ _)" [0, 10] 10)

text {*

We introduce schematext versions of unique and arbitrary choice.

*}

syntax ("" output)
  "_xHOL_Defs\<ZZ>st_The" :: "schematext \<rightarrow> logic" ("THE _" 0)

syntax (xsymbols)
  "_xHOL_Defs\<ZZ>st_The" :: "schematext \<rightarrow> logic" ("\<mu> _" 0)

syntax (xsymbols output)
  "_xHOL_Defs\<ZZ>st_TheQ" :: "[idt, logic] \<rightarrow> logic" ("(3THE _ |/ _)")

parse_translation {*

  [(@{syntax_const "_xHOL_Defs\<ZZ>st_The"}, 
     schematext_tr (Syntax.const @{const_syntax The}))]
  
*}

print_translation {*

  [(@{const_syntax "The"}, 
     schematext_tr' (Const(@{syntax_const "_xHOL_Defs\<ZZ>st_The"}, dummyT)))] 
*}

syntax ("" output)
  "_xHOL_Defs\<ZZ>st_Eps" :: "schematext \<rightarrow> logic" ("SOME _" 0)

syntax (xsymbols)
  "_xHOL_Defs\<ZZ>st_Eps" :: "schematext \<rightarrow> logic" ("\<some> _" 0)

syntax (xsymbols output)
  "_xHOL_Defs\<ZZ>st_EpsQ" :: "[idt, logic] \<rightarrow> logic" ("(3EPS _ |/ _)")

parse_translation {*

  [(@{syntax_const "_xHOL_Defs\<ZZ>st_Eps"}, 
     schematext_tr (Syntax.const @{const_syntax Eps}))]
  
*}

print_translation {*

  [(@{const_syntax "Eps"}, 
     schematext_tr' (Const(@{syntax_const "_xHOL_Defs\<ZZ>st_Eps"}, dummyT)))] 
*}

(*
definition
  set_Eps :: "'a set \<rightarrow> 'a"
where
  set_Eps_def: "set_Eps \<defs> (\<olambda> X \<bullet> Eps (\<olambda> x \<bullet> x \<in> X))"

syntax ("" output)
  "_xHOL_Defs\<ZZ>st_Eps" :: "schematext \<rightarrow> logic" ("SOME _" 0)

syntax (xsymbols)
  "_xHOL_Defs\<ZZ>st_Eps" :: "schematext \<rightarrow> logic" ("\<some> _" 0)

syntax (zed)
  "_xHOL_Defs\<ZZ>st_Eps" :: "schematext \<rightarrow> logic" ("\<ssome> _" 10)

translations
  "_xHOL_Defs\<ZZ>st_Eps S" \<rightleftharpoons> "CONST xHOL_Defs.set_Eps (_xHOL_Syntax\<ZZ>coll S)"

lemma set_the_equality: 
  assumes prema: "a \<in> X"
      and premx: "\<And> x \<bullet> x \<in> X \<turnstile> x = a"
  shows "set_The X = a"
  apply (unfold set_The_def)
  apply (rule the_equality)
  apply (rule prema)
  apply (rule premx)
  apply (assumption)
  done

lemma collect_the_equality: 
  assumes prema: "P a"
      and premx: "\<And> x \<bullet> P x \<turnstile> x = a"
  shows "set_The (Collect P) = a"
  apply (rule set_the_equality)
  apply (simp add: prema)
  apply (rule premx)
  apply (simp)
  done

lemma set_theI:
  assumes "a \<in> X" and "\<And> x \<bullet> x \<in> X \<turnstile> x = a"
  shows "set_The X \<in> X"
  by (iprover intro: assms set_the_equality [THEN ssubst])

lemma collect_theI:
  assumes "P a" and "\<And> x \<bullet> P x \<turnstile> x = a"
  shows "P (set_The (Collect P))"
  by (iprover intro: assms collect_the_equality [THEN ssubst])

lemma set_theI': "(\<exists>\<subone> x \<bullet> x \<in> X) \<turnstile> set_The X \<in> X"
  apply (erule ex1E)
  apply (erule set_theI)
  apply (erule allE)
  apply (erule mp)
  apply assumption
  done

lemma collect_theI': "(\<exists>\<subone> x \<bullet> P x) \<turnstile> P (set_The (Collect P))"
  apply (erule ex1E)
  apply (erule collect_theI)
  apply (erule allE)
  apply (erule mp)
  apply assumption
  done

lemma set_theI2:
  assumes "a \<in> X" "\<And> x \<bullet> x \<in> X \<turnstile> x = a" "\<And> x \<bullet> x \<in> X \<turnstile> Q x"
  shows "Q (set_The X)"
  by (iprover intro: assms set_theI)

lemma collect_theI2:
  assumes "P a" "\<And> x \<bullet> P x \<turnstile> x = a" "\<And> x \<bullet> P x \<turnstile> Q x"
  shows "Q (set_The (Collect P))"
  by (iprover intro: assms collect_theI)

lemma set_the1_equality: "\<lbrakk> (\<exists>\<subone> x \<bullet> x \<in> X); a \<in> X \<rbrakk> \<turnstile> set_The X = a"
  apply (rule set_the_equality)
  apply  assumption
  apply (erule ex1E)
  apply (erule all_dupE)
  apply (drule mp)
  apply  assumption
  apply (erule ssubst)
  apply (erule allE)
  apply (erule mp)
  apply assumption
  done 

lemma collect_the1_equality: "\<lbrakk> (\<exists>\<subone> x \<bullet> P x); P a \<rbrakk> \<turnstile> set_The (Collect P) = a"
  apply (rule collect_the_equality)
  apply  assumption
  apply (erule ex1E)
  apply (erule all_dupE)
  apply (drule mp)
  apply  assumption
  apply (erule ssubst)
  apply (erule allE)
  apply (erule mp)
  apply assumption
  done 

lemma set_the_singleton [simp]: "set_The {x} = x"
  apply (rule set_the_equality)
  apply (auto)
  done

lemma set_someI: 
  "x \<in> X \<turnstile> set_Eps X \<in> X"
  apply (simp add: set_Eps_def)
  apply (erule someI)
  done 

lemma collect_someI: 
  "P x \<turnstile> P (set_Eps (Collect P))"
  apply (simp add: set_Eps_def)
  apply (erule someI)
  done 

lemma set_someI_ex [elim?]: "\<exists> x \<bullet> x \<in> X \<turnstile> set_Eps X \<in> X"
  apply (erule exE)
  apply (erule set_someI)
  done 

lemma collect_someI_ex [elim?]: "(\<exists> x \<bullet> P x) \<turnstile> P (set_Eps (Collect P))"
  apply (erule exE)
  apply (erule collect_someI)
  done 

lemma set_someI_nempty [elim?]: 
    "X \<noteq> \<emptyset> \<turnstile> set_Eps X \<in> X"
  apply (rule set_someI_ex)
  apply (auto)
  done

lemma set_someI2: "\<lbrakk> a \<in> X;  (\<And> x \<bullet> x \<in> X \<turnstile> Q x) \<rbrakk> \<turnstile> Q (set_Eps X)"
  by (blast intro: set_someI)

lemma collect_someI2: "\<lbrakk> P a;  (\<And> x \<bullet> P x \<turnstile> Q x) \<rbrakk> \<turnstile> Q (set_Eps (Collect P))"
  by (blast intro: collect_someI)

lemma set_some_equality: "\<lbrakk> a \<in> X; (\<And> x \<bullet> x \<in> X \<turnstile> x = a) \<rbrakk> \<turnstile> set_Eps X = a"
  by (blast intro: set_someI)

lemma collect_some_equality: "\<lbrakk> P a; (\<And> x \<bullet> P x \<turnstile> x = a) \<rbrakk> \<turnstile> set_Eps (Collect P) = a"
  by (blast intro: collect_someI)

lemma set_some1_equality: "\<lbrakk> (\<exists>\<subone> x \<bullet> x \<in> X); a \<in> X \<rbrakk> \<turnstile> set_Eps X = a"
  by (blast intro: set_some_equality)

lemma collect_some1_equality: "\<lbrakk> (\<exists>\<subone> x \<bullet> P x); P a  \<rbrakk> \<turnstile> set_Eps (Collect P) = a"
  by (blast intro: collect_some_equality)

lemma set_some_eq_ex: "(set_Eps X) \<in> X \<Leftrightarrow> (\<exists> x \<bullet> x \<in> X)"
  by (blast intro: set_someI)

lemma collect_some_eq_ex: "P (set_Eps (Collect P)) \<Leftrightarrow> (\<exists> x \<bullet> P x)"
  by (blast intro: collect_someI)

lemma set_some_eq_singleton [simp]: "set_Eps {a} = a"
  apply (rule set_some_equality)
  apply (auto)
  done
*)

text {*

Some Z-style syntax for the @{term Least} operator.

*}

no_notation
  Least (binder "LEAST " 10)

no_notation
  Greatest (binder "GREATEST " 10)

syntax (xsymbols output)
  "_xHOL_Syntax\<ZZ>st_Least" :: "schematext \<rightarrow> logic" ("\<mu> _" 0)
  "_xHOL_Syntax\<ZZ>st_Greatest" :: "schematext \<rightarrow> logic" ("\<nu> _" 0)

syntax (zed)
  "_xHOL_Syntax\<ZZ>st_Least" :: "schematext \<rightarrow> logic" ("\<LEAST> _" 0)
  "_xHOL_Syntax\<ZZ>st_Greatest" :: "schematext \<rightarrow> logic" ("\<GREATEST> _" 0)

parse_translation {*

  [ (@{syntax_const "_xHOL_Syntax\<ZZ>st_Least"}, 
       schematext_tr (Syntax.const @{const_syntax Least})),
    (@{syntax_const "_xHOL_Syntax\<ZZ>st_Greatest"}, 
       schematext_tr (Syntax.const @{const_syntax Greatest}))]
  
*}

print_translation {*

  [(@{const_syntax "Least"}, 
     schematext_tr' (Const(@{syntax_const "_xHOL_Syntax\<ZZ>st_Least"}, dummyT))),
   (@{const_syntax "Greatest"}, 
     schematext_tr' (Const(@{syntax_const "_xHOL_Syntax\<ZZ>st_Greatest"}, dummyT)))] 
*}

no_syntax
  "_LeastM" :: "[pttrn, 'a => 'b::ord, bool] => 'a"    ("LEAST _ WRT _. _" [0, 4, 10] 10)

no_syntax
  "_GreatestM" :: "[pttrn, 'a => 'b::ord, bool] => 'a" ("GREATEST _ WRT _. _" [0, 4, 10] 10)

no_syntax
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3ALL _:_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3EX _:_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3EX! _:_./ _)" [0, 0, 10] 10)
  "_Bleast"     :: "id => 'a set => bool => 'a"           ("(3LEAST _:_./ _)" [0, 0, 10] 10)

no_syntax (HOL)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3! _:_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3? _:_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3?! _:_./ _)" [0, 0, 10] 10)

no_syntax (xsymbols)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3\<forall>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3\<exists>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3\<exists>!_\<in>_./ _)" [0, 0, 10] 10)
  "_Bleast"     :: "id => 'a set => bool => 'a"           ("(3LEAST_\<in>_./ _)" [0, 0, 10] 10)

no_syntax (HTML output)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3\<forall>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3\<exists>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3\<exists>!_\<in>_./ _)" [0, 0, 10] 10)

syntax (xsymbols output)
  "_Ball"       :: "[pttrn, 'a set, \<bool>] \<rightarrow> \<bool>" ("(3\<forall> _ \<in> _ \<bullet>/ _)" [0, 0, 10] 10)
  "_Bex"        :: "[pttrn, 'a set, \<bool>] \<rightarrow> \<bool>" ("(3\<exists> _ \<in> _ \<bullet>/ _)" [0, 0, 10] 10)

no_syntax
  "_Sigma" :: "[pttrn, 'a set, 'b set] => ('a * 'b) set"  ("(3SIGMA _:_./ _)" [0, 0, 10] 10)

syntax (xsymbols output)
  "_Sigma" :: "[pttrn, 'a set, 'b set] => ('a * 'b) set"  ("(3SIGMA _ \<in> _ \<bullet>/ _)" [0, 0, 10] 10)

text {*

We introduce Z-like notation for various set operators.

*}

notation (xsymbols)
  Pow ("\<pset>")

notation (zed)
  insert ("\<^ins>{:_:}{:_:}")

notation (xsymbols)
  "Finite_Set.card" ("\<card>_" [1000] 1000)

notation (xsymbols)
  Set.UNIV ("\<univ>") and
  Set.empty ("\<emptyset>")

text {*

The big operators have various binder-like notations that we remove, so as to replace them with 
schema notations below. Currently, these are not suitable for schematext formulations, similar to the graph lambda operator, but we need to give some thought to unitfying these forms in the full HiVe notation.

*}

no_syntax
  "_setsum" :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b::comm_monoid_add"    ("(3SUM _:_. _)" [0, 51, 10] 10)
no_syntax (xsymbols)
  "_setsum" :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b::comm_monoid_add"    ("(3\<Sum>_\<in>_. _)" [0, 51, 10] 10)
no_syntax (HTML output)
  "_setsum" :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b::comm_monoid_add"    ("(3\<Sum>_\<in>_. _)" [0, 51, 10] 10)

syntax (xsymbols)
  "_setsum" :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b::comm_monoid_add"    ("(3\<Sum> _ \<in> _ \<bullet> _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setsum" :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b::comm_monoid_add"    ("(3\<Sum> _ \<in> _ \<bullet> _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "\<Sum> i \<in> A \<bullet> b" \<rightleftharpoons> "CONST setsum (\<olambda> i \<bullet> b) A"

no_syntax
  "_qsetsum" :: "pttrn \<rightarrow> bool \<rightarrow> 'a \<rightarrow> 'a" ("(3SUM _ |/ _./ _)" [0,0,10] 10)
no_syntax (xsymbols)
  "_qsetsum" :: "pttrn \<rightarrow> bool \<rightarrow> 'a \<rightarrow> 'a" ("(3\<Sum>_ | (_)./ _)" [0,0,10] 10)
no_syntax (HTML output)
  "_qsetsum" :: "pttrn \<rightarrow> bool \<rightarrow> 'a \<rightarrow> 'a" ("(3\<Sum>_ | (_)./ _)" [0,0,10] 10)

syntax (xsymbols)
  "_xHOL_Syntax\<ZZ>setsum" :: "schematext \<rightarrow> logic" ("\<Sum> _" 0)

translations
  "_xHOL_Syntax\<ZZ>setsum S" \<rightleftharpoons> "CONST Setsum (_xHOL_Syntax\<ZZ>coll S)"

no_syntax
  "_setprod" :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b::comm_monoid_mult"  ("(3PROD _:_. _)" [0, 51, 10] 10)
no_syntax (xsymbols)
  "_setprod" :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b::comm_monoid_mult"  ("(3\<Prod>_\<in>_. _)" [0, 51, 10] 10)
no_syntax (HTML output)
  "_setprod" :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b::comm_monoid_mult"  ("(3\<Prod>_\<in>_. _)" [0, 51, 10] 10)

syntax (xsymbols)
  "_setprod" :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b::comm_monoid_mult"  ("(3\<Prod> _ \<in> _ \<bullet> _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setprod" :: "pttrn \<rightarrow> 'a set \<rightarrow> 'b \<rightarrow> 'b::comm_monoid_mult"  ("(3\<Prod> _ \<in> _ \<bullet> _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "\<Prod> i \<in> A \<bullet> b" \<rightleftharpoons> "CONST setprod (\<olambda> i \<bullet> b) A" 

no_syntax
  "_qsetprod" :: "pttrn \<rightarrow> bool \<rightarrow> 'a \<rightarrow> 'a" ("(3PROD _ |/ _./ _)" [0,0,10] 10)
no_syntax (xsymbols)
  "_qsetprod" :: "pttrn \<rightarrow> bool \<rightarrow> 'a \<rightarrow> 'a" ("(3\<Prod>_ | (_)./ _)" [0,0,10] 10)
no_syntax (HTML output)
  "_qsetprod" :: "pttrn \<rightarrow> bool \<rightarrow> 'a \<rightarrow> 'a" ("(3\<Prod>_ | (_)./ _)" [0,0,10] 10)

syntax (xsymbols)
  "_xHOL_Syntax\<ZZ>setprod" :: "schematext \<rightarrow> logic" ("\<Pi> _" 0)

translations
  "_xHOL_Syntax\<ZZ>setprod S" \<rightleftharpoons> "CONST Setprod (_xHOL_Syntax\<ZZ>coll S)"

section {* @{theory Orderings} notations *}

text {*

The bounded quantifier notation is removed in favour of constrained quantifications.

*}

no_syntax
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3EX _<=_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3ALL _>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3EX _>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3ALL _>=_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3EX _>=_./ _)" [0, 0, 10] 10)

no_syntax (xsymbols)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

no_syntax (HOL)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3? _<=_./ _)" [0, 0, 10] 10)

no_syntax (HTML output)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

translations 
  "(\<forall> x | x \<le> y \<bullet> t)" \<leftharpoondown> "_All_less_eq x y t"
  "(\<forall> x | x < y \<bullet> t)" \<leftharpoondown> "_All_less x y t"
  "(\<exists> x | x \<le> y \<bullet> t)" \<leftharpoondown> "_Ex_less_eq x y t"
  "(\<exists> x | x < y \<bullet> t)" \<leftharpoondown> "_Ex_less x y t"
  "(\<forall> x | y \<le> x \<bullet> t)" \<leftharpoondown> "_All_greater_eq x y t"
  "(\<forall> x | y < x \<bullet> t)" \<leftharpoondown> "_All_greater x y t"
  "(\<exists> x | y \<le> x \<bullet> t)" \<leftharpoondown> "_Ex_greater_eq x y t"
  "(\<exists> x | y < x \<bullet> t)" \<leftharpoondown> "_Ex_greater x y t"

section {* Products *}

text {*

We introduce more prominent notations for tuple operators.

*}

(*
notation (xsymbols output)
  fst  ("\<^bold>f\<^bold>s\<^bold>t") and
  snd  ("\<^bold>s\<^bold>n\<^bold>d")
*)

notation (zed)
  fst  ("\<fst>") and
  snd  ("\<snd>")

section {* Functions *}

text {*

Remove crazy co-opting of 'o' character to operator composition.

*}

no_notation
   comp (infixl "o" 55)

text {*

We define some Z-like infix notation for functional image.

*}

no_notation
  image (infixr "`" 90)

no_notation
   vimage (infixr "-`" 90)

notation ("" output)
  image ("_'(|_|')" [1000,0] 1000) and
  vimage ("_-'(|_|')" [1000,0] 1000)

notation (xsymbols)
  image ("_\<lparr>_\<rparr>" [1000,0] 1000) and
  vimage ("_-\<zlImg>_\<zrImg>" [1000,0] 1000)

text {*

Multiplicative powers.

*}

no_notation
  power (infixr "^" 80)

notation (xsymbols)
  Power.power_class.power ("_\<xexp>\<^bzup>_\<^ezup>" [80, 0] 80)

abbreviation
  power0 :: "'a::{zero,power} \<rightarrow> 'a" ("_\<supzero>")
where
  "x\<supzero> \<defs> power x 0"

abbreviation
  power1 :: "'a::{zero,power} \<rightarrow> 'a" ("_\<supone>")
where
  "x\<supone> \<defs> power x 1"

abbreviation
  power2 :: "'a::{zero,power} \<rightarrow> 'a" ("_\<suptwo>")
where
  "x\<suptwo> \<defs> power x 2"
 
section {* Options *}

text {*

Some extra notations for dealing with optional data.

*}

type_notation (xsymbols)
  "Option.option" ("_\<option>" [1000] 1000)

notation (xsymbols)
  "Option.option.None" ("\<None>") and
  "Option.option.Some" ("_\<option>" [1000] 1000) and
  "Option.the" ("\<mu>\<option>")

section {* Numeric type notation *}

text {*

The usual blackboard bold type symbols are introduced for some
of the standard types.

*}

type_notation (xsymbols)
  bool ("\<bool>") and
  nat ("\<nat>") and
  "Int.int" ("\<int>") and
  "Real.real" ("\<real>")

notation (xsymbols)
  abs ("\<abs>_\<abs>")

end 
