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

text {* if an operation $a$ has input lenght 0, a must be empty or is consists only of insert 
        actions *}

lemma emptyInputInsert: "inputLength a = 0 \<Longrightarrow> a = [] \<or> (\<exists>c as. a = Insert c#as)"
  apply (induct a, auto)
  by (metis Suc_neq_Zero action.exhaust inputLength.simps(2) inputLength.simps(3))

fun outputLength :: "'char operation \<Rightarrow> nat" where
  "outputLength [] = 0"
| "outputLength (Retain#as)   = Suc (outputLength as)"
| "outputLength (Insert _#as) = Suc (outputLength as)"
| "outputLength (Delete#as)   = outputLength as"

text {* if an operation $a$ has output lenght 0, a must be empty or is consists only of delete 
        actions *}

lemma emptyOutputDelete: "outputLength a = 0 \<Longrightarrow> a = [] \<or> (\<exists>as. a = Delete#as)"
  apply (induct a, auto)
  by (metis Suc_neq_Zero action.exhaust outputLength.simps(2) outputLength.simps(3))

text {* if an operation $a$ has output and input lenght of 0, the operation must be empty *}

lemma emptyInOutOp: "inputLength a = 0 \<and> outputLength a = 0 \<Longrightarrow> a = []"
  apply (induct a, auto)
  by (metis Zero_not_Suc emptyOutputDelete inputLength.simps(3) list.distinct(1))

subsection {* Valid Operations *}
           
text {* We define an inductive set of all valid pairs of operations and documents as well as their
        resulting output document .*}

inductive_set outputs :: "('char operation \<times> 'char document \<times> 'char document) set" where
  empty[intro!]:    "([],[],[]) \<in> outputs"
| retain[intro!]:   "(a,d,d') \<in> outputs \<Longrightarrow> (Retain#a,c#d,c#d')   \<in> outputs"
| delete[intro!]:   "(a,d,d') \<in> outputs \<Longrightarrow> (Delete#a,c#d,d')     \<in> outputs"
| insert[intro!]:   "(a,d,d') \<in> outputs \<Longrightarrow> ((Insert c)#a,d,c#d') \<in> outputs"

text {* if an operation $a$ is empty it can only be applied to the empty document and the
        result is also the empty document *}

lemma emptyInput: "([],d,d') \<in> outputs \<Longrightarrow> d = [] \<and> d' = []"
  by (erule outputs.cases, auto)

lemma emptyInput3: "([],d,d'#ds') \<notin> outputs"
  by (auto, erule outputs.cases, auto)  

lemma emptyInput4: "([],d#ds,d') \<notin> outputs"
  by (auto, erule outputs.cases, auto) 

text {* if the output of an operation applied to a document is empty, the operation can only consist
        of delete actions *}

lemma emptyOutput: "(a#as,d,[]) \<in> outputs \<Longrightarrow> a = Delete"
  by (erule outputs.cases, auto)

text {* an operation applied to the empty document can only consist of insert operations *}

lemma emptyDoc: "(a#as,[],d') \<in> outputs \<Longrightarrow> \<exists>c. a = Insert c"
  by (erule outputs.cases, auto)

text {* Reverse induction rules *}

lemma undoRetain: "(Retain#a,c#d,c#d') \<in> outputs \<Longrightarrow> (a,d,d') \<in> outputs"
  by (smt action.distinct(1) action.distinct(3) list.distinct(1) list.inject outputs.cases)

lemma undoDelete: "(Delete#a,c#d,d') \<in> outputs \<Longrightarrow> (a,d,d') \<in> outputs"
  by (smt action.distinct(3) action.distinct(5) list.distinct(1) list.inject outputs.cases)

lemma undoInsert: "((Insert c)#a,d,c#d') \<in> outputs \<Longrightarrow> (a,d,d') \<in> outputs"
  by (smt action.distinct(1) action.distinct(5) list.distinct(1) list.inject outputs.simps)

lemma retainOut: "(Retain#a,c#cs,d') \<in> outputs \<Longrightarrow> \<exists>c' cs'. d' = c'#cs' \<and> (a,cs,cs') \<in> outputs"
  apply (cases d', simp_all)
  apply (drule emptyOutput, simp)
  apply (rule undoRetain, clarify)
  by (smt action.distinct(1) action.distinct(3) list.distinct(1) list.inject outputs.cases)
  
lemma insertOut: "(Insert c#as,d,d') \<in> outputs \<Longrightarrow> \<exists>cs'. d' = c#cs' \<and> (a,d,cs') \<in> outputs"
  apply (cases d', simp_all)
  apply (drule emptyOutput, simp)
  sorry

text {* the application of operations on documents has to be deterministic *}

lemma outputsSurjective: "\<exists>a d. (a,d,d') \<in> outputs"
  by (induct_tac d', auto)

lemma outputsDeterministic: "(a,d,d') \<in> outputs \<Longrightarrow> (a,d,d'') \<in> outputs \<longrightarrow> d' = d''"    
  apply (erule outputs.induct)
  apply (clarify)
  apply (drule emptyInput, simp)
  apply (clarify)
  defer defer
  apply (clarify)
  apply (metis action.distinct(5) emptyDoc emptyInput insertOut)
  
  sorry

subsection {* Input and Output Lenght of Valid Operations *}

text {* An operation $a$ is a valid operation on document $d$ iff the input length of $a$ equals 
        the length of $d$ *} 

lemma validInputLength: "(a,d,d') \<in> outputs \<Longrightarrow> inputLength a = length d"
  apply (erule outputs.induct)
  apply (auto)
  done

lemma lengthValidInput: "inputLength a = length (d) \<longleftrightarrow> (a,d,f d) \<in> outputs"
  sorry

lemma sucLength [rule_format]: 
  shows "Suc (n) = length d \<longrightarrow> (\<exists>c cs. d = c#cs \<and> length cs = n)"
  by (induct_tac d, auto)  
  
lemma validInputLength2 [rule_format]:
  shows "\<exists>d'. inputLength a = length d \<longrightarrow> (a,d,d') \<in> outputs"
  apply (induct_tac d, auto)  

  sorry

text {* if an operation $a$ is a valid operation on any document $d$ the length of the resulting 
        document $d'$ is equal to the output lenght of $a$ *}

lemma validOutputLength: "(a,d,d') \<in> outputs \<Longrightarrow> outputLength a = length d'"
  by (erule outputs.induct, auto)

subsection {* Application of operations *}

text {* The $applyOp$ function applies an operation $a$ to document $d$ and yields either $None$ if
        the input length of $a$ does not match the length of $d$ or $Some d'$ where d' is the result
        of a valid application *}

fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document option"
where
  "applyOp ([])            ([])        = Some []"
| "applyOp (Retain#next)   (head#tail) = Option.map (\<lambda>d. head#d) (applyOp next tail)"
| "applyOp (Insert c#next) (d)         = Option.map (\<lambda>d. c#d)    (applyOp next d)"
| "applyOp (Delete#next)   (_#tail)    = applyOp next tail"
| "applyOp _               _           = None"
 
text {* We need to show the equality of the inductively defined set $outputs$ and the partial
        function $applyOp$ in order to use the inductive set for further correctness proofs
        involving $applyOp$ *}

lemma validOperationApplyOp: "(a,d,d') \<in> outputs \<Longrightarrow> applyOp a d = Some d'"
  apply (erule outputs.induct)
  apply (auto)
  done 

lemma applyOpValidOperation: "applyOp a d = Some d' \<Longrightarrow> (a,d,d') \<in> outputs"
  
  sorry

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
lemma transform_convergence:   
  shows "Option.bind (transform a b) (\<lambda>(at,bt). compose a bt)
       = Option.bind (transform a b) (\<lambda>(at,bt). compose b at)"
  

export_code applyOp addDeleteOp compose transform in JavaScript
  module_name Operation

end
