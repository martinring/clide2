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
           
text {* We define an inductive set, describing the relation of all valid pairs of operations and 
        documents and their resulting output document .*}

inductive_set application :: "(('char operation \<times> 'char document) \<times> 'char document) set" where
  empty[intro!]:    "(([],[]),[]) \<in> application"
| retain[intro!]:   "((a,d),d') \<in> application \<Longrightarrow> ((Retain#a,c#d),c#d')   \<in> application"
| delete[intro!]:   "((a,d),d') \<in> application \<Longrightarrow> ((Delete#a,c#d),d')     \<in> application"
| insert[intro!]:   "((a,d),d') \<in> application \<Longrightarrow> (((Insert c)#a,d),c#d') \<in> application"

text {* iff an operation $a$ is empty it can only be applied to the empty document and the
        result is also the empty document *}

lemma emptyInput: "(([],d),d') \<in> application \<longleftrightarrow> d = [] \<and> d' = []"
  apply (auto)
  apply (erule application.cases, auto)
  apply (erule application.cases, auto)
  done

lemma emptyInputDomain: "([],d) \<in> Domain application \<longleftrightarrow> d = []"
  by (auto simp add: emptyInput)

lemma emptyDocInsert: "(a#as,[]) \<in> Domain application \<Longrightarrow> \<exists>c. a = Insert c"
  by (clarify, erule application.cases, auto)

lemma emptyDocLength: "(a,[]) \<in> Domain application \<longrightarrow> inputLength a = 0"
  apply (induct_tac a)
  apply (force)
  apply (clarify)
  apply (case_tac a)
  sorry  

lemma remRetain: "((Retain # list, d) \<in> Domain application) = 
                  (\<exists>c cs. d = c#cs \<and> (list,cs) \<in> Domain application)"  
  apply (auto)
  by (smt Domain.DomainI 
          action.distinct(1) 
          application.simps 
          list.distinct(1) 
          list.inject)
  
lemma remInsert: "((Insert c#list,d) \<in> Domain application) =
                  ((list,d) \<in> Domain application)"
  apply (auto)
  by (smt Domain.simps 
          action.distinct(1) 
          action.distinct(5) 
          application.simps 
          list.distinct(1) 
          list.inject)

lemma remDelete: "((Delete # list, d) \<in> Domain application) = 
                  (\<exists>c cs. d = c#cs \<and> (list,cs) \<in> Domain application)"  
  apply (auto)
  by (smt Domain.DomainI 
          action.distinct(5) 
          application.simps 
          list.distinct(1) 
          list.inject)

text {* every possible output document can be reached by the application of operations to documents *}

lemma applicationRange: "d' \<in> Range application"  
  apply (induct_tac d')
  apply (auto)
  done

subsection {* Input and Output Lenght of Valid Operations *}

text {* All pairs of operations and documents are contained in the domain of the application
        iff the inputLength of the operation matches the length of the document *}

lemma applicationDomain [rule_format]: 
  "\<forall>d. (a,d) \<in> Domain application \<longleftrightarrow> inputLength a = length d"
  apply (induct_tac a)  
  apply (simp, clarify, rule emptyInputDomain)
  apply (clarify, case_tac a)
  apply (auto simp add: remRetain remInsert remDelete)
  apply (metis length_Suc_conv)
  apply (metis length_Suc_conv)
  done
  
text {* if an operation $a$ is a valid operation on any document $d$ the length of the resulting 
        document $d'$ is equal to the output lenght of $a$ *}

lemma validOutputLength: "((a,d),d') \<in> application \<Longrightarrow> outputLength a = length d'"
  by (erule application.induct, auto)

subsection {* Application function *}

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
 
text {* We need to show the equality of the inductively defined set $application$ and the partial
        function $applyOp$ in order to use the inductive set for further correctness proofs
        involving $applyOp$ *}

lemma applyOpApplication1 [rule_format]: 
  "\<forall>d'. applyOp a d = Some d' \<longrightarrow> ((a,d),d') \<in> application"
  by (rule applyOp.induct, auto)

lemma applyOpApplication2 [rule_format]: 
  "((a,d),d') \<in> application \<Longrightarrow> applyOp a d = Some d'"
  by (erule application.induct, auto)

lemma applyOpApplication: "applyOp a d = Some d' \<longleftrightarrow> ((a,d),d') \<in> application"
  by (force intro: applyOpApplication1 applyOpApplication2)

text {* this also implicitly prooves that the relation $application$ is deterministic *}

subsection {* Normalization *}

fun addDeleteOp :: "'char operation \<Rightarrow> 'char operation"
where
  "addDeleteOp (Insert c#next) = (Insert c)#(addDeleteOp next)"
| "addDeleteOp as = Delete#as"

lemma addDeleteOpValid: "((a,d),d') \<in> application \<Longrightarrow> \<forall>c. ((addDeleteOp a,c#d),d') \<in> application"
  by (rule application.induct, auto)

lemma addDeleteOpValid2: "((Delete#as,d),d') \<in> application \<Longrightarrow> ((addDeleteOp as,d),d') \<in> application"
  by (smt action.distinct(3) action.distinct(5) addDeleteOpValid application.cases list.distinct(1) list.inject)
    
fun normalize :: "'char operation \<Rightarrow> 'char operation" where
  "normalize [] = []"
| "normalize (Retain#a) = Retain#(normalize a)"
| "normalize (Insert c#a) = Insert c#(normalize a)"
| "normalize (Delete#a) = addDeleteOp (normalize a)"

text {* if an operation $a$ can be applied to a document $d$ yielding the resulting document $d'$,
        the normalized operation $a$ can also be applied to the document $d$ yielding the same 
        result *}

lemma normalizeValid: "((a,d),d') \<in> application \<Longrightarrow> ((normalize a,d),d') \<in> application"
  apply (erule application.induct)
  apply (auto intro: addDeleteOpValid2)
  done

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

inductive_set composition :: "('char operation \<times> 'char operation \<times> 'char operation \<times> 'char document \<times> 'char document \<times> 'char document) set" where
  nil[intro!]:  "([],[],[],[],[],[]) \<in> composition"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composition \<Longrightarrow> (addDeleteOp a,b,addDeleteOp ab,c#d,d',d'') \<in> composition"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composition \<Longrightarrow> (a,Insert c#b,Insert c#ab,d,d',c#d'') \<in> composition"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composition \<Longrightarrow> (Retain#a,Retain#b,Retain#ab,c#d,c#d',c#d'') \<in> composition"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composition \<Longrightarrow> (Retain#a,Delete#b,addDeleteOp ab,c#d,d',d'') \<in> composition"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composition \<Longrightarrow> (Insert c#a,Retain#b,Insert c#ab,d,c#d',c#d'') \<in> composition"
| [intro!]: "(a,b,ab,d,d',d'') \<in> composition \<Longrightarrow> (Insert c#a,Delete#b,ab,d,c#d',d'') \<in> composition"

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
  sorry
  

export_code applyOp addDeleteOp compose transform in JavaScript
  module_name Operation

end
