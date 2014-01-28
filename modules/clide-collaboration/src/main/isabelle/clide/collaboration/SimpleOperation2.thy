(* Formalisation of Operational Transformation *)
(* author: Martin Ring, DFKI Bremen *) (*<*) 

theory SimpleOperation
imports Main List Option Set
begin (*>*)

section {* Actions, Operations and Documents *}

text {* A @{term document} is a list of elements. *}

type_synonym 'char document = "'char list"

text {* An @{term action} can either alter the document at the current position, move the virtual 
        cursor on the document forward or both. *}

datatype 'char action = Retain | Insert 'char | Delete

text {* An @{term operation} is a list of actions. *}

type_synonym 'char operation = "'char action list"

text {* There are three types of actions of which an operation is composed:
        @{term Retain}, @{term "Insert c"} and @{term Delete}. An operation is
        a list of actions.

        \begin{itemize}
          \item @{term Retain} moves the cursor to the next position
          \item @{term "Insert c"} inserts element @{term c} at the position of the cursor and moves 
                                 the cursor behind that elment
          \item @{term Delete} removes the element at the current position
        \end{itemize} *}
 
subsection {* In- and Output Lengths of Operations *}

text {* An operation has an input length and an output length:

        \begin{itemize}
          \item The input length is the length of a document on which the operation can
                be applied.
          \item The output length is the length of the result of the application on a
                document on which the operation is defined.
        \end{itemize} *}

fun inputLength :: "'char operation \<Rightarrow> nat" where
  "inputLength [] = 0"
| "inputLength (Retain#as) = Suc (inputLength as)"
| "inputLength (Delete#as) = Suc (inputLength as)"
| "inputLength (Insert _#as)  = inputLength as"

text {* if an operation @{term a} has input lenght 0, a must be empty or is consists only of insert 
        actions *}

lemma emptyInputInsert [rule_format]: "inputLength a = 0 \<longrightarrow> a = [] \<or> (\<exists>as c. a = Insert c#as)"
  by (induct_tac a rule: inputLength.induct, auto)  

fun outputLength :: "'char operation \<Rightarrow> nat" where
  "outputLength [] = 0"
| "outputLength (Retain#as)   = Suc (outputLength as)"
| "outputLength (Insert _#as) = Suc (outputLength as)"
| "outputLength (Delete#as)   = outputLength as"

text {* if an operation @{term a} has output lenght 0, a must be empty or is consists only of delete 
        actions *}

lemma emptyOutputDelete [rule_format]: "outputLength a = 0 \<longrightarrow> a = [] \<or> (\<exists>as. a = Delete#as)"
  by (induct_tac a rule: outputLength.induct, auto)

text {* if an operation @{term a} has output and input lenght of 0, the operation must be empty *}

lemma emptyInOutOp [rule_format]: "inputLength a = 0 \<and> outputLength a = 0 \<longrightarrow> a = []"
  by (induct_tac a rule: inputLength.induct, auto)

subsection {* Application function *}

text {* The @{term applyOp} function applies an operation @{term a} to document @{term d} and yields 
        either @{term None} if the input length of @{term a} does not match the length of @{term d} 
        or @{term "Some d'"} where @{term d'} is the result of a valid application *}

fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document option"
where
  "applyOp ([])            ([])        = Some []"
| "applyOp (Retain#next)   (head#tail) = Option.map (\<lambda>d. head#d) (applyOp next tail)"
| "applyOp (Insert c#next) (d)         = Option.map (\<lambda>d. c#d)    (applyOp next d)"
| "applyOp (Delete#next)   (_#tail)    = applyOp next tail"
| "applyOp (_)             (_)         = None"
           
text {* We also define an inductive set, describing the relation of all valid pairs of operations and 
        documents and their resulting output document .*}

inductive_set application :: "(('char operation \<times> 'char document) \<times> 'char document) set" where
  empty[intro!]:  "(([],[]),[]) \<in> application"
| retain[intro!]: "((a,d),d') \<in> application \<Longrightarrow> ((Retain#a,c#d),c#d')   \<in> application"
| delete[intro!]: "((a,d),d') \<in> application \<Longrightarrow> ((Delete#a,c#d),d')     \<in> application"
| insert[intro!]: "((a,d),d') \<in> application \<Longrightarrow> (((Insert c)#a,d),c#d') \<in> application"

text {* We need to show the equality of the inductively defined set @{term application} and the partial
        function @{term applyOp} in order to use the inductive set for further correctness proofs
        involving @{term applyOp} *}

lemma applyOpSet1 [rule_format]: 
  "\<forall>d'. applyOp a d = Some d' \<longrightarrow> ((a,d),d') \<in> application"
  by (rule applyOp.induct, auto)

lemma applyOpSet2: 
  "((a,d),d') \<in> application \<Longrightarrow> applyOp a d = Some d'"
  by (erule application.induct, auto)

lemma applyOpSet: "applyOp a d = Some d' \<longleftrightarrow> ((a,d),d') \<in> application"
  by (force intro: applyOpSet1 applyOpSet2)

text {* this also implicitly proves that the relation @{term application} is deterministic *}

subsection {* Valid Operations *}

text {* iff an operation @{term a} is empty it can only be applied to the empty document and the
        result is also the empty document *}

lemma emptyInput: "applyOp [] d = Some d' \<longleftrightarrow> d = [] \<and> d' = []"
  by (induct_tac d, auto)

lemma emptyDocInsert: "(\<exists>d'. applyOp (a#as) [] = Some d') \<longrightarrow> (\<exists>c. a = Insert c)"
  by (case_tac a, auto)
  
lemma remRetain: "(((Retain#as,d),d') \<in> application) =
                   (\<exists>c cs cs'. d = c#cs \<and> d'=c#cs' \<and> ((as,cs),cs') \<in> application)"
  apply (auto)
  by (smt action.distinct(3) application.cases inputLength.simps(2) inputLength.simps(4) list.distinct(1) list.inject)

lemma remInsert: "(((Insert c# as, d),d') \<in> application) =
                   (\<exists>cs. d' = c#cs \<and> ((as,d),cs) \<in> application)"
  apply (auto)
  by (smt action.distinct(1) action.distinct(5) action.inject application.simps list.distinct(1) list.inject)

lemma remDelete: "(((Delete # list, d),d') \<in> application) = 
                  (\<exists>c cs. d = c#cs \<and> ((list,cs),d') \<in> application)"  
  apply (auto)
  by (smt action.distinct(3) application.cases inputLength.simps(3) inputLength.simps(4) list.distinct(1) list.inject)

text {* every document can be produced by the application of an operation to a document *}

lemma applicationRange: "\<exists>a d. ((a,d),d') \<in> application"
  by (induct_tac d', auto)

lemma applyOpRange: "\<exists>a d. applyOp a d = Some d'"
  by (simp add: applicationRange applyOpSet)

subsection {* In- and Output Lenghts of Valid Operations *}

text {* All pairs of operations and documents are contained in the domain of the application
        iff the inputLength of the operation matches the length of the document *}

lemma applicationDomain: "(\<exists>d'. applyOp a d = Some d') \<longleftrightarrow> (inputLength a = length d)"
  by (induct_tac a d rule: applyOp.induct, auto)
  
text {* if an operation @{term a} is a valid operation on any document @{term d} the length of the 
        resulting document @{term d'} is equal to the output lenght of @{term a} *}

lemma validOutputLength: "((a,d),d') \<in> application \<Longrightarrow> outputLength a = length d'"
  by (erule application.induct, auto)

subsection {* Normalization *}

fun addDeleteOp :: "'char operation \<Rightarrow> 'char operation"
where
  "addDeleteOp (Insert c#next) = (Insert c)#(addDeleteOp next)"
| "addDeleteOp as = Delete#as"

lemma addDeleteOpValid11: "((a,d),d') \<in> application \<Longrightarrow> \<forall>c. ((addDeleteOp a,c#d),d') \<in> application"
  by (rule application.induct, auto)

lemma addDeleteOpValid1: "((Delete#as,d),d') \<in> application \<Longrightarrow> ((addDeleteOp as,d),d') \<in> application"
  by (smt action.distinct(3) action.distinct(5) addDeleteOpValid11 application.cases list.distinct(1) list.inject)

lemma addDeleteOpValid: "applyOp a d = Some d' \<Longrightarrow> \<forall>c. applyOp (addDeleteOp a) (c#d) = Some d'"
  by (simp add: applyOpSet addDeleteOpValid11)

lemma addDeleteOutputLenght[simp]: "outputLength (addDeleteOp as) = outputLength as"
  by (rule addDeleteOp.induct, auto)

text {* The @{term normalize} function sorts all sequences within an operation that do not contain
        {@term Retain} actions, such that all @{term Insert} actions occur before the @{term Delete}
        actions *}

fun normalize :: "'char operation \<Rightarrow> 'char operation" where
  "normalize [] = []"
| "normalize (Retain#a) = Retain#(normalize a)"
| "normalize (Insert c#a) = Insert c#(normalize a)"
| "normalize (Delete#a) = addDeleteOp (normalize a)"

value "normalize [Delete, Insert a, Delete, Insert b, Retain, Insert c]"

text {* For @{term normalize} to be useful it must not change the effect of an operation:

        if an operation $a$ can be applied to a document $d$ yielding the resulting document $d'$,
        the normalized operation $a$ can also be applied to the document $d$ yielding the same 
        result *}

lemma normalizeValid: "((a,d),d') \<in> application \<Longrightarrow> ((normalize a,d),d') \<in> application"
  apply (erule application.induct)
  apply (auto intro: addDeleteOpValid1)
  done

text {* if @{term addDeleteOp} is called on a normalized operation the resulting operation is also
        normalized *}

lemma normalizeAddDeleteOp[rule_format]: "normalize a = a \<longrightarrow> addDeleteOp a = normalize (addDeleteOp a)"
  apply (induct_tac a)
  apply (simp)
  apply (case_tac a, simp_all)
  done

lemma normalizeAddDeleteOp2[rule_format]: "normalize a = a \<longrightarrow> addDeleteOp a = normalize (Delete#a)"
  apply (induct_tac a)
  apply (simp)
  apply (case_tac a, simp_all)
  done

section {* Composition of Operations *}

text {* The @{term compose} function composes two operations @{term a} and @{term b}, in such a way
        that the composed operation @{term ab} has the same effect upon application as operations
        @{term a} and @{term b} executed sequentially. *}

fun compose :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation option"
where
  "compose [] []                        = Some []"
| "compose (Delete#as)    (bs)          = Option.map addDeleteOp (compose as bs)"
| "compose (as)           (Insert c#bs) = Option.map (Cons (Insert c)) (compose as bs)"
| "compose (Retain#as)    (Retain#bs)   = Option.map (Cons Retain) (compose as bs)"
| "compose (Retain#as)    (Delete#bs)   = Option.map addDeleteOp (compose as bs)"
| "compose (Insert(c)#as) (Retain#bs)   = Option.map (Cons (Insert c)) (compose as bs)"
| "compose (Insert(_)#as) (Delete#bs)   = compose as bs"
| "compose _              _             = None"

subsection {* Normalized Output *}

text {* the result of @{term compose} is always normalized *}

lemma composeNormalized[rule_format]: "\<forall>ab. compose a b = Some ab \<longrightarrow> ab = normalize ab"
  apply (rule compose.induct, auto)  
  apply (rule normalizeAddDeleteOp, simp)+
  done

subsection {* Inductive Set *}

text {* Again we define an inductive set describing the composition relation. *}

inductive_set composition :: "(('char operation \<times> 'char operation) \<times> 'char operation) set" where
  empty[intro!]:  "(([],[]),[]) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((Delete#a,b),addDeleteOp ab) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((a,Insert c#b),Insert c#ab) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((Retain#a,Retain#b),Retain#ab) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((Retain#a,Delete#b),addDeleteOp ab) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((Insert c#a,Retain#b),Insert c#ab) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((Insert _#a,Delete#b),ab) \<in> composition"

text {* And again we have to prove equivalence of the inductively defined relation and the 
        recursive function: *}

lemma composeSet11 [rule_format]: 
  "\<forall>ab c. compose a b = Some ab \<longrightarrow> compose a (Insert c # b) = Some (Insert c # ab)"
  by (rule compose.induct, auto)

lemma composeSet1: "((a,b),ab) \<in> composition \<Longrightarrow> compose a b = Some (ab)"
  by (erule composition.induct, auto intro: composeSet11)

lemma composeSet2 [rule_format]: "\<forall>ab. compose a b = Some ab \<longrightarrow> ((a,b),ab) \<in> composition"
  apply (rule compose.induct)
  apply (auto)
  done

lemma composeSet: "((a,b),ab) \<in> composition \<longleftrightarrow> compose a b = Some (ab)"
  by (auto intro: composeSet1 composeSet2)

subsection {* Domain *}

text {* The operations @{term a} and @{term b} can be composed iff the output length of @{term a} 
        matches the input length of @{term b} *}

lemma composeDomain1 [rule_format]: "(\<exists>ab. compose a b = Some ab) \<longrightarrow> outputLength a = inputLength b"
  by (rule compose.induct, auto)

lemma composeDomain21 [rule_format]: "compose a b = None \<longrightarrow> outputLength a \<noteq> inputLength b"
  by (rule compose.induct, auto)

lemma composeDomain2: "outputLength a = inputLength b \<Longrightarrow> (\<exists>ab. compose a b = Some ab)"
  apply (erule contrapos_pp)
  by (simp add: composeDomain21)

lemma composeDomain: "(\<exists>ab. compose a b = Some ab) \<longleftrightarrow> outputLength a = inputLength b"
  by (auto intro: composeDomain1 composeDomain2)

subsection {* Range *}

text {* Every operation $ab$ can be produced in its normalized form by composition of two 
        operations  *}

lemma compositionRange: "(normalize ab) \<in> Range composition"
  by (rule normalize.induct, auto)

subsection {* Invariant of the composition *}

text {* Finally we show that the @{term compose} function does actually compose operations *}

lemma compositionInv [rule_format]: "((a,b),ab) \<in> composition \<Longrightarrow> \<forall>d d' d''. ((a,d),d') \<in> application \<longrightarrow> ((b,d'),d'') \<in> application \<longrightarrow> ((ab,d),d'') \<in> application"
  apply (erule composition.induct)
  apply (auto simp add: emptyInput addDeleteOpValid11 remDelete remInsert remRetain)
  by (metis applyOpSet emptyInput)
  
lemma composeInv: "compose a b = Some ab \<Longrightarrow> applyOp a d = Some d' \<Longrightarrow> applyOp b d' = Some d'' \<Longrightarrow> applyOp ab d = Some d''"
  by (simp add: composeSet applyOpSet compositionInv)

section {* Operation Transformation *}

text {* The transformation function is the basis of operational transformation. For a pair of 
        operations @{term "(a,b)"} it computes an output pair of transformed operations 
        @{term "(a',b')"}. The convergence property @{term "compose a b' = compose b a'"} enables
        the OT system to execute operations in different order at different sites while the 
        documents do not diverge *}

fun transform :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> ('char operation \<times> 'char operation) option"
where
  "transform []             []             = Some ([],[])"
| "transform (Insert(c)#as) b              = Option.map (\<lambda>(at,bt). (Insert(c)#at,Retain#bt)) (transform as b)"
| "transform a              (Insert(c)#bs) = Option.map (\<lambda>(at,bt). (Retain#at,Insert(c)#bt)) (transform a bs)"
| "transform (Retain#as)    (Retain#bs)    = Option.map (\<lambda>(at,bt). (Retain#at,Retain#bt)) (transform as bs)"
| "transform (Delete#as)    (Delete#bs)    = transform as bs"
| "transform (Retain#as)    (Delete#bs)    = Option.map (\<lambda>(at,bt). (at,Delete#bt)) (transform as bs)"
| "transform (Delete#as)    (Retain#bs)    = Option.map (\<lambda>(at,bt). (Delete#at,bt)) (transform as bs)"
| "transform _              _              = None"

text {* the transformation of two operations yields a result iff they have an equal input length *}

lemma transformDomain: "(\<exists>ab. transform a b = Some ab) \<longleftrightarrow> inputLength a = inputLength b"
  by (induct_tac a b rule: transform.induct, auto)  

text {* Yet again we define an inductive set to describe the transform relation. Again we omit all
        applications of @{term addDeleteOp} and replace them by @{term Delete} *}

inductive_set transformation :: "(('c operation \<times> 'c operation) \<times> ('c operation \<times> 'c operation)) set" where
  empty[intro!]: "(([],[]),([],[])) \<in> transformation"
| [intro!]: "((a,b),(a',b')) \<in> transformation \<Longrightarrow> ((Insert c#a,b),(Insert c#a',Retain#b')) \<in> transformation"
| [intro!]: "(([],b),(a',b')) \<in> transformation \<Longrightarrow> (([],Insert c#b),(Retain#a',Insert c#b')) \<in> transformation"
| [intro!]: "((Retain#a,b),(a',b')) \<in> transformation \<Longrightarrow> ((Retain#a,Insert c#b),(Retain#a',Insert c#b')) \<in> transformation"
| [intro!]: "((Delete#a,b),(a',b')) \<in> transformation \<Longrightarrow> ((Delete#a,Insert c#b),(Retain#a',Insert c#b')) \<in> transformation"
| [intro!]: "((a,b),(a',b')) \<in> transformation \<Longrightarrow> ((Retain#a,Retain#b),(Retain#a',Retain#b')) \<in> transformation"
| [intro!]: "((a,b),(a',b')) \<in> transformation \<Longrightarrow> ((Delete#a,Delete#b),(a',b')) \<in> transformation"
| [intro!]: "((a,b),(a',b')) \<in> transformation \<Longrightarrow> ((Retain#a,Delete#b),(a',Delete#b')) \<in> transformation"
| [intro!]: "((a,b),(a',b')) \<in> transformation \<Longrightarrow> ((Delete#a,Retain#b),(Delete#a',b')) \<in> transformation"

text {* we need to show, that the above relation is a superset of the @{term transform} function *}

lemma transformSubset[rule_format]: "\<forall>a' b'. transform a b = Some (a',b') \<longrightarrow> ((a,b),(a',b')) \<in> transformation"
  by (rule transform.induct, auto)  

text {* And finally we show the convergence property for the set ... *}

lemma transformationConvergence: "((a,b),(a',b')) \<in> transformation \<Longrightarrow>
                                   (\<exists>ab. ((a,b'),ab) \<in> composition \<and> ((b,a'),ab) \<in> composition)"
  by (erule transformation.induct, auto)  

text {* ... and this also for the @{term transform} function *}

lemma tp1: "transform a b = Some (a',b') \<Longrightarrow> compose a b' \<noteq> None \<and> compose a b' = compose b a'"  
  apply (drule transformSubset)
  apply (drule transformationConvergence)
  by (auto simp add: composeSet)  
  
(*export_code applyOp addDeleteOp compose transform in Scala
  module_name Operation*)

end
