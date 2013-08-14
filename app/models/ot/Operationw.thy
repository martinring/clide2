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

inductive_set operationLengths :: "('char operation \<times> nat \<times> nat) set" where
  empty[intro!]: "([],0,0) \<in> operationLengths"
| step[intro!]:  "\<And>a. (as,m,n)  \<in> operationLengths \<Longrightarrow> (a#as,m + lengthBeforeAction a, n + lengthAfterAction a) \<in> operationLengths"

fun lengthBeforeOp :: "'char operation \<Rightarrow> nat" where
  "lengthBeforeOp as = listsum (map lengthBeforeAction as)"

fun lengthAfterOp :: "'char operation \<Rightarrow> nat"
where
  "lengthAfterOp as = listsum (map lengthAfterAction as)"
           
inductive_set outputs :: "('char operation \<times> 'char document \<times> 'char document) set" where
  emptyDoc[intro!]: "([],[],[]) \<in> outputs"
| retain[intro!]:   "\<And>c. (a,d,d') \<in> outputs \<Longrightarrow> (Retain#a,c#d,c#d')   \<in> outputs"
| delete[intro!]:   "\<And>c. (a,d,d') \<in> outputs \<Longrightarrow> (Delete#a,c#d,d')     \<in> outputs"
| insert[intro!]:   "\<And>c. (a,d,d') \<in> outputs \<Longrightarrow> ((Insert c)#a,d,c#d') \<in> outputs"

fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document option"
where
  "applyOp ([])          ([])     = Some []"
| "applyOp (Retain#as)   (d#ds)   = Option.map (\<lambda>ds. d#ds) (applyOp as ds)"
| "applyOp (Insert c#as) (ds)     = Option.map (\<lambda>ds. c#ds) (applyOp as ds)"
| "applyOp (Delete#as)   (_#ds)   = applyOp as ds"
| "applyOp (_)           (_)      = None"

inductive_set inputs :: "('char operation \<times> 'char document) set" where
  emptyDoc[intro!]: "([],[]) \<in> inputs"
| retain[intro!]:   "\<And>c. (a,d) \<in> inputs \<Longrightarrow> (Retain#a,c#d)   \<in> inputs"
| delete[intro!]:   "\<And>c. (a,d) \<in> inputs \<Longrightarrow> (Delete#a,c#d)   \<in> inputs"
| insert[intro!]:   "\<And>c. (a,d) \<in> inputs \<Longrightarrow> ((Insert c)#a,d) \<in> inputs"
   
lemma outputsDeterministic: "\<And>a d. (a, d, d') \<in> outputs \<Longrightarrow> (a, d, e') \<in> outputs \<Longrightarrow> d' = e'"
  apply (induct d')
  sorry

lemma lengthValidInput [simp]: "(a,d,d') \<in> outputs \<Longrightarrow> lengthBeforeOp a = length d"
  by (erule outputs.induct, auto)

lemma lengthValidOutput [simp]: "(a,d,d') \<in> outputs \<Longrightarrow> lengthAfterOp a = length d'"
  by (erule outputs.induct, auto)

text {* the application of an operation \texttt{a} to a document \texttt{d}
        yields a result iff the base length of the operation is equal to the
        length of the document *}

lemma validOperationApplyOp[simp]: "(a,d,d') \<in> outputs \<Longrightarrow> applyOp a d = Some d'"
  apply (erule outputs.induct)
  apply (auto)
  done 

(* TODO *)

fun addDeleteOp :: "'char operation \<Rightarrow> 'char operation"
where
  "addDeleteOp (Insert c#next) = (Insert c)#(addDeleteOp next)"
| "addDeleteOp as = Delete#as"

lemma [simp]: "(a,d,d') \<in> outputs \<Longrightarrow> \<forall>c. (addDeleteOp a,c#d,d') \<in> outputs"
  apply (rule outputs.induct)
  apply (auto)

fun normalize :: "'char operation \<Rightarrow> 'char operation" where
  "normalize [] = []"
| "normalize (Retain#a) = Retain#(normalize a)"
| "normalize (Insert c#a) = Insert c#(normalize a)"
| "normalize (Delete#a) = addDeleteOp (normalize a)"

lemma [simp]: "(a,d,d') \<in> outputs \<Longrightarrow> (normalize a,d,d') \<in> outputs"
  by (rule outputs.induct, auto)

(* todo: (a,d,d') \<in> outputs \<Longrightarrow> (b,d,d') \<in> outputs \<Longrightarrow> normalize a = normalize b *)


lemma validOperationLength: "(a,d,d') \<in> validOperations \<Longrightarrow> (a,length d, length d') \<in> operationLengths"
  by (erule validOperations.induct, auto)

(* TODO: applyOp = None => \<notin> validOperations ? *)

subsection {* Composition of Operations *}

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

inductive_set composedOperations :: "('char operation \<times> 'char operation \<times> 'char operation \<times> 'char document \<times> 'char document \<times> 'char document) set" where
  nil[intro!]:  "([],[],[],[],[],[]) \<in> composedOperations"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composedOperations \<Longrightarrow> (addDeleteOp a,b,addDeleteOp ab,c#d,d',d'') \<in> composedOperations"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composedOperations \<Longrightarrow> (a,Insert c#b,Insert c#ab,d,d',c#d'') \<in> composedOperations"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composedOperations \<Longrightarrow> (Retain#a,Retain#b,Retain#ab,c#d,c#d',c#d'') \<in> composedOperations"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composedOperations \<Longrightarrow> (Retain#a,addDeleteOp b,addDeleteOp ab,c#d,d',d'') \<in> composedOperations"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composedOperations \<Longrightarrow> (Insert c#a,Retain#b,Insert c#ab,d,c#d',c#d'') \<in> composedOperations"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composedOperations \<Longrightarrow> (Insert c#a,Delete#b,ab,d,c#d',d'') \<in> composedOperations"

lemma "(a,b,ab,d,d',d'') \<in> composedOperations \<Longrightarrow> (ab,d,d'') \<in> validOperations 
                                                \<and> (a,d,d') \<in> validOperations
                                                \<and> (b,d',d'') \<in> validOperations"
  by (erule composedOperations.induct, auto)

lemma "(a,b,ab,d,d',d'') \<in> composedOperations \<Longrightarrow> compose a b = Some ab"
  by (erule composedOperations.induct, auto)

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

export_code applyOp addDeleteOp compose transform in JavaScript
  module_name Operation

end
