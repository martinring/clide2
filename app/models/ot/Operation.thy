(* Formalisation of Operational Transformation *)
(* author: Martin Ring, DFKI Bremen *)

theory Operation
imports Main List
begin

section {* Formalisation of Operational Transformation *}

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

function lengthBeforeOp :: "'char Action list \<Rightarrow> nat"
where
  "lengthBeforeOp [] = 0"
| "lengthBeforeOp (Retain#next)    = 1 + lengthBeforeOp next"
| "lengthBeforeOp (Delete#next)    = 1 + lengthBeforeOp next"
| "lengthBeforeOp (Insert(_)#next) = 0 + lengthBeforeOp next"
by pat_completeness auto

fun lengthAfterOp :: "'char Action list \<Rightarrow> nat"
where
  "lengthAfterOp [] = 0"
| "lengthAfterOp (Retain#next)    = 1 + lengthAfterOp next"
| "lengthAfterOp (Delete#next)    = 0 + lengthAfterOp next"
| "lengthAfterOp (Insert(_)#next) = 1 + lengthAfterOp next"

fun applyOp :: "'char Action list \<Rightarrow> 'char list \<Rightarrow> 'char list option"
where
  "applyOp [] [] = Some []"
| "applyOp (Retain#next)   (head#tail) = Option.map (\<lambda>a. head#a) (applyOp next tail)"
| "applyOp (Insert c#next) (head#tail) = Option.map (\<lambda>a. c#a) (applyOp next (head#tail))"
| "applyOp (Delete#next)   (head#tail) = applyOp next tail"
| "applyOp _ _ = None"

text {* the application of an operation \texttt{a} to a document \texttt{d}
        yields a result iff the base length of the operation is equal to the
        length of the document *}

lemma apply_complete: "(lengthBeforeOp a) = (size d) \<longleftrightarrow> isSome (applyOp a d)"  
proof (induct a)
  show "lengthBeforeOp [] = size d \<longleftrightarrow> isSome (applyOp [] d)"
  proof (auto)
    have "lengthBeforeOp [] = 0" by simp
    have "lengthBeforeOp [] = size d \<longleftrightarrow> d = []" by simp
    also have "isSome (applyOp [] d) \<longrightarrow> d = []" by simp
    finally show ?thesis.

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
