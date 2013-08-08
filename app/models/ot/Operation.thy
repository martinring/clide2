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

datatype 'char Action = Retain | Insert 'char | Delete 

text {*
An operation as an input length and an output length:

The input length is the length of a document on which the operation can
be applied yielding a result.

The output length is the length of the result of the application on a
document on which the operation is defined.
*}

fun lengthBeforeOp :: "'char Action list \<Rightarrow> nat"
where
  "lengthBeforeOp [] = 0"
| "lengthBeforeOp (Retain#next)    = Suc (lengthBeforeOp next)"
| "lengthBeforeOp (Delete#next)    = Suc (lengthBeforeOp next)"
| "lengthBeforeOp (Insert(_)#next) = lengthBeforeOp next"

fun lengthAfterOp :: "'char Action list \<Rightarrow> nat"
where
  "lengthAfterOp [] = 0"
| "lengthAfterOp (Retain#next)    = Suc (lengthAfterOp next)"
| "lengthAfterOp (Delete#next)    = lengthAfterOp next"
| "lengthAfterOp (Insert(_)#next) = Suc (lengthAfterOp next)"

fun applyOp :: "'char Action list \<Rightarrow> 'char list \<Rightarrow> 'char list option"
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

lemma apply_complete: "(applyOp a d) = None \<longleftrightarrow> (lengthBeforeOp a) \<noteq> (length d)"
  oops

subsection {* Composition of Operations *}

fun addDeleteOp :: "'char Action list \<Rightarrow> 'char Action list"
where
  "addDeleteOp (Insert c#next) = (Insert c)#(addDeleteOp next)"
| "addDeleteOp as = Delete#as"

fun compose :: "'char Action list \<Rightarrow> 'char Action list \<Rightarrow> 'char Action list option"
where
  "compose [] [] = Some []"
| "compose (Delete#as)    (bs)          = Option.map (addDeleteOp) (compose as bs)"
| "compose (as)           (Insert c#bs) = Option.map (\<lambda>a. Insert(c)#a) (compose as bs)"
| "compose (Retain#as)    (Retain#bs)   = Option.map (\<lambda>a. Retain#a) (compose as bs)"
| "compose (Retain#as)    (Delete#bs)   = Option.map (addDeleteOp) (compose as bs)"
| "compose (Insert(c)#as) (Retain#bs)   = Option.map (\<lambda>a. Insert(c)#a) (compose as bs)"
| "compose (Insert(_)#as) (Delete#bs)   = compose as bs"
| "compose _ _ = None"

lemma compose_complete: "\<forall> a b. (lengthAfterOp a) = (lengthBeforeOp b) \<longleftrightarrow> isSome (compose a b)"  
  oops

lemma compose_inv: "\<forall> a b d. Option.bind (compose a b) (\<lambda>op'. applyOp op' d) 
                           = Option.bind (applyOp a d) (\<lambda>d'. applyOp b d')"
  oops

subsection {* Operation Transformation *}

fun transform :: "'char Action list \<Rightarrow> 'char Action list \<Rightarrow> (('char Action list) \<times> ('char Action list)) option"
where
  "transform [] [] = Some ([],[])"
| "transform (Insert(c)#as) b        = Option.map (\<lambda>(at,bt). (Insert(c)#at,Retain#bt)) (transform as b)"
| "transform a (Insert(c)#bs)        = Option.map (\<lambda>(at,bt). (Retain#at,Insert(c)#bt)) (transform a bs)"
| "transform (Retain#as) (Retain#bs) = Option.map (\<lambda>(at,bt). (Retain#at,Retain#bt)) (transform as bs)"
| "transform (Delete#as) (Delete#bs) = transform as bs"
| "transform (Retain#as) (Delete#bs) = Option.map (\<lambda>(at,bt). (at,addDeleteOp(bt))) (transform as bs)"
| "transform (Delete#as) (Retain#bs) = Option.map (\<lambda>(at,bt). (addDeleteOp(at),bt)) (transform as bs)"
| "transform _ _ = None"

(* convergence property TP1 *)
lemma transform_convergence: "\<forall> a b. Option.bind (transform a b) (\<lambda>(at,bt). compose a bt)
                                   = Option.bind (transform a b) (\<lambda>(at,bt). compose b at)"
  oops

export_code applyOp addDeleteOp compose transform in Scala
  module_name Operation

end
