(* Formalisation of Operational Transformation *)
(* author: Martin Ring, DFKI Bremen *)

header {* Formalisation of Operational Transformation *}

theory Operation
imports Main List Option
begin

section {* Actions, Operations and Documents *}

text {* A document is a list of elements. An operation is a list of actions, that
        is processed sequentially. An action can either alter the document at the
        current position, move the virtual cursor on the document forward or both.

        There are three types of actions of which an operation is composed:
        \texttt{Retain}, \texttt{Insert} and \texttt{Delete}. An operation is
        a list of actions.

        \begin{itemize}
          \item \texttt{Retain} moves the cursor by one step
          \item \texttt{Insert} inserts an element at the position of the cursor and moves the
                                cursor behind that elment
          \item \texttt{Delete} removes the element at the current position
        \end{itemize} *}

datatype 'char action = Retain | Insert 'char | Delete

type_synonym 'char operation = "'char action list"

type_synonym 'char document = "'char list"

text {* An operation has an input length and an output length:

        \begin{itemize}
          \item The input length is the length of a document on which the operation can
                be applied yielding a result.
          \item The output length is the length of the result of the application on a
                document on which the operation is defined.
        \end{itemize} *}

fun inputLength :: "'char operation \<Rightarrow> nat" where
  "inputLength [] = 0"
| "inputLength (Retain#as) = Suc (inputLength as)"
| "inputLength (Delete#as) = Suc (inputLength as)"
| "inputLength (Insert _#as)  = inputLength as"

fun outputLength :: "'char operation \<Rightarrow> nat" where
  "outputLength [] = 0"
| "outputLength (Retain#as)   = Suc (outputLength as)"
| "outputLength (Insert _#as) = Suc (outputLength as)"
| "outputLength (Delete#as)   = outputLength as"

subsection {* Valid Operations *}
           
text {* We define an inductive set of all valid pairs of operations and documents as well as their
        resulting output document .*}

inductive_set outputs :: "('char operation \<times> 'char document \<times> 'char document) set" where
  empty[intro!]:    "([],[],[]) \<in> outputs"
| retain[intro!]:   "(a,d,d') \<in> outputs \<Longrightarrow> (Retain#a,c#d,c#d')   \<in> outputs"
| delete[intro!]:   "(a,d,d') \<in> outputs \<Longrightarrow> (Delete#a,c#d,d')     \<in> outputs"
| insert[intro!]:   "(a,d,d') \<in> outputs \<Longrightarrow> ((Insert c)#a,d,c#d') \<in> outputs"

lemma undoRetain: "(Retain#a,c#d,c#d') \<in> outputs \<Longrightarrow> (a,d,d') \<in> outputs"
  by (smt action.distinct(1) action.distinct(3) list.distinct(1) list.inject outputs.cases)

lemma undoDelete: "(Delete#a,c#d,d') \<in> outputs \<Longrightarrow> (a,d,d') \<in> outputs"
  by (smt action.distinct(3) action.distinct(5) list.distinct(1) list.inject outputs.cases)

lemma undoInsert: "((Insert c)#a,d,c#d') \<in> outputs \<Longrightarrow> (a,d,d') \<in> outputs"
  by (smt action.distinct(1) action.distinct(5) list.distinct(1) list.inject outputs.simps)

text {* the application of operations on documents has to be deterministic *}

lemma emptyInput: "([],[],d) \<in> outputs \<Longrightarrow> d = []"  
  by (erule outputs.cases, auto)  

lemma emptyInput2: "([],[],d#ds) \<notin> outputs"
  by (auto, erule outputs.cases, auto)  

lemma emptyOutput: "(a#as,d,[]) \<in> outputs \<Longrightarrow> a = Delete"
  by (erule outputs.cases, auto)  

lemma "(a,d,d') \<in> outputs \<Longrightarrow> \<forall>c. (a,d,c#d') \<notin> outputs"  
  apply (clarify, erule outputs.cases, simp_all)
  apply (drule emptyInput, simp)
  

(*lemma emptyOutput: "(a,d,[]) \<in> outputs \<Longrightarrow> *)

lemma outputsDeterministic: "(a,d,d') \<in> outputs \<Longrightarrow> (a,d,d'') \<in> outputs \<longrightarrow> d' = d''"
  apply (erule outputs.induct)
  apply (auto)
  apply (erule sym [OF emptyInput])
  apply (induct d'')  
  apply (drule emptyOutput)
  apply (simp)
  apply (drule undoRetain)
  sorry

text {* An operation $a$ is a valid operation on document $d$ iff the input length of $a$ equals 
        the length of $d$ *} 

lemma validLengths: "(a,d,d') \<in> outputs \<longleftrightarrow> inputLength a = length d \<and> outputLength a = length d'"
  apply (auto)
  apply (erule outputs.induct, auto)
  apply (erule outputs.induct, auto)
  
  sorry  



fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document option"
where
  "applyOp ([])            ([])        = Some []"
| "applyOp (Retain#next)   (head#tail) = Option.map (\<lambda>d. head#d) (applyOp next tail)"
| "applyOp (Insert c#next) (d)         = Option.map (\<lambda>d. c#d)    (applyOp next d)"
| "applyOp (Delete#next)   (_#tail)    = applyOp next tail"
| "applyOp _               _           = None"

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
  by (rule outputs.induct, auto)

fun normalize :: "'char operation \<Rightarrow> 'char operation" where
  "normalize [] = []"
| "normalize (Retain#a) = Retain#(normalize a)"
| "normalize (Insert c#a) = Insert c#(normalize a)"
| "normalize (Delete#a) = addDeleteOp (normalize a)"

lemma [simp]: "(a,d,d') \<in> outputs \<Longrightarrow> (normalize a,d,d') \<in> outputs"
  by (rule outputs.induct, auto)

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
