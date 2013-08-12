(* Formalisation of Operational Transformation *)
(* author: Martin Ring, DFKI Bremen *)

theory Operation
imports Main List Option
begin

section {* Formalisation of Operational Transformation *}

subsection {* Actions, Operations and Documents *}

text {* 
A document is a list of elements. An operation is a list of actions, that
is processed sequentially. An action can either alter the document at the
current position, move the virtual cursor on the document forward or both.

There are three types of actions of which an operation is composed:
\texttt{Retain}, \texttt{Insert} and \texttt{Delete}. An operation is
a list of actions.

\begin{itemize}
\item \texttt{Retain} moves the cursor by one step
\item \texttt{Insert} inserts an element at the position of the cursor and moves the
cursor behind that elment
\item \texttt{Delete} removes the element at the current position not moving the cursor 
\end{itemize}
*}

datatype 'char action = Retain | Insert 'char | Delete

type_synonym 'char operation = "'char action list"

type_synonym 'char document = "'char list"

text {*
An operation as an input length and an output length:

The input length is the length of a document on which the operation can
be applied yielding a result.

The output length is the length of the result of the application on a
document on which the operation is defined.
*}

primrec lengthBeforeAction :: "'char action \<Rightarrow> nat" where
  "lengthBeforeAction Retain     = 1"
| "lengthBeforeAction Delete     = 1"
| "lengthBeforeAction (Insert _) = 0"

primrec lengthAfterAction :: "'char action \<Rightarrow> nat" where
  "lengthAfterAction Retain     = 1"
| "lengthAfterAction Delete     = 0"
| "lengthAfterAction (Insert _) = 1"

fun lengthBeforeOp :: "'char operation \<Rightarrow> nat" where
  "lengthBeforeOp as = listsum (map lengthBeforeAction as)"

fun lengthAfterOp :: "'char operation \<Rightarrow> nat"
where
  "lengthAfterOp as = listsum (map lengthAfterAction as)"

lemma lengthBeforeCombines [simp]: "lengthBeforeOp a + lengthBeforeOp b = lengthBeforeOp (a@b)"
  by (induct a, auto)

lemma lengthAfterCombines [simp]: "lengthAfterOp a + lengthAfterOp b = lengthAfterOp (a@b)"
  by (induct a, auto)

inductive_set validOperations :: "('char operation \<times> 'char document \<times> 'char document) set" where
  emptyDoc[intro!]: "([],[],[]) \<in> validOperations"
| retain[intro!]:   "(a,d,d') \<in> validOperations \<Longrightarrow> (Retain#a,c#d,c#d')   \<in> validOperations"
| delete[intro!]:   "(a,d,d') \<in> validOperations \<Longrightarrow> (Delete#a,c#d,d')     \<in> validOperations"
| insert[intro!]:   "(a,d,d') \<in> validOperations \<Longrightarrow> ((Insert c)#a,d,c#d') \<in> validOperations"

lemma lengthOfValidInput: "(a,d,d') \<in> validOperations \<Longrightarrow> lengthBeforeOp a = length d"
  by (erule validOperations.induct, auto)

lemma lengthOfValidOutput: "(a,d,d') \<in> validOperations \<Longrightarrow> lengthAfterOp a = length d'"
  by (erule validOperations.induct, auto)

(* TODO: Completeness of validOperations *)

fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document option"
where
  "applyOp ([])            ([])        = Some []"
| "applyOp (Retain#next)   (head#tail) = Option.map (\<lambda>a. head#a) (applyOp next tail)"
| "applyOp (Insert c#next) (d)         = Option.map (\<lambda>a. c#a) (applyOp next d)"
| "applyOp (Delete#next)   (head#tail) = applyOp next tail"
| "applyOp (Retain#next)   ([])        = None"
| "applyOp (Delete#next)   ([])        = None"
| "applyOp ([])            (head#tail) = None"

text {* the application of an operation \texttt{a} to a document \texttt{d}
        yields a result iff the base length of the operation is equal to the
        length of the document *}

lemma validOperationApplyOp: "(a,d,d') \<in> validOperations \<Longrightarrow> applyOp a d = Some d'"
  by (erule validOperations.induct, auto)

(* TODO: applyOp = None => \<notin> validOperations ? *)

subsection {* Composition of Operations *}

fun addDeleteOp :: "'char operation \<Rightarrow> 'char operation"
where
  "addDeleteOp (Insert c#next) = (Insert c)#(addDeleteOp next)"
| "addDeleteOp as = Delete#as"

fun compose :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation option"
where
  "compose [] []                        = Some []"
| "compose (Delete#as)    (bs)          = Option.map (addDeleteOp) (compose as bs)"
| "compose (as)           (Insert c#bs) = Option.map (\<lambda>a. Insert(c)#a) (compose as bs)"
| "compose (Retain#as)    (Retain#bs)   = Option.map (\<lambda>a. Retain#a) (compose as bs)"
| "compose (Retain#as)    (Delete#bs)   = Option.map (addDeleteOp) (compose as bs)"
| "compose (Insert(c)#as) (Retain#bs)   = Option.map (\<lambda>a. Insert(c)#a) (compose as bs)"
| "compose (Insert(_)#as) (Delete#bs)   = compose as bs"
| "compose _              _             = None"

lemma composeValidOperations: "(a,d,d') \<in> validOperations \<Longrightarrow> (b,d',d'') \<in> validOperations \<Longrightarrow> compose a b = Some ab"

subsection {* Operation Transformation *}

fun transform :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> ('char operation \<times> 'char operation) option"
where
  "transform []             []             = Some ([],[])"
| "transform (Insert(c)#as) b              = Option.map (\<lambda>(at,bt). (Insert(c)#at,Retain#bt)) (transform as b)"
| "transform a              (Insert(c)#bs) = Option.map (\<lambda>(at,bt). (Retain#at,Insert(c)#bt)) (transform a bs)"
| "transform (Retain#as)    (Retain#bs)    = Option.map (\<lambda>(at,bt). (Retain#at,Retain#bt)) (transform as bs)"
| "transform (Delete#as)    (Delete#bs)    = transform as bs"
| "transform (Retain#as)    (Delete#bs)    = Option.map (\<lambda>(at,bt). (at,addDeleteOp(bt))) (transform as bs)"
| "transform (Delete#as)    (Retain#bs)    = Option.map (\<lambda>(at,bt). (addDeleteOp(at),bt)) (transform as bs)"
| "transform _              _              = None"

text {* the transformation of two operations yields a result iff they have an equal input length *}
lemma transform_complete: "(transform a b) = None \<longleftrightarrow> lengthBeforeOp a \<noteq> lengthBeforeOp b"
  oops

(* convergence property TP1 *)
lemma transform_convergence: "Option.bind (transform a b) (\<lambda>(at,bt). compose a bt)
                            = Option.bind (transform a b) (\<lambda>(at,bt). compose b at)"
  oops

export_code applyOp addDeleteOp compose transform in Scala
  module_name Operation

end
