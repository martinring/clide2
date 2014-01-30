(* Formalisation of Operational Transformation *)
(* author: Martin Ring, DFKI Bremen *) (*<*) 

theory Operation
imports Main List Option Set
begin (*>*)

section {* Actions, Operations and Documents *}

subsection{* Basic Types *}

text {* 
 A @{term document} is a list of arbitrary elements.
 *}

type_synonym 'char document = "'char list"

text {* 
  An operation is a sequence of elementary actions. 
  We can think of actions as moving through a document, processing each element of the
  document in turn to produce some output. The actions can be:
  \begin{itemize}
      \item @{term Retain} copies the current element to the output document;
      \item @{term "Insert c"} inserts element @{term c} into the output document;
      \item @{term Delete} removes the current element 
        (i.e. does not copy it to the output document).
   \end{itemize}
*}

datatype 'char action = Retain | Insert 'char | Delete
type_synonym 'char operation = "'char action list"


subsection {* The Application Function *}

text {* 
  The @{term applyOp} function is partial, and only defined for documents of appropriate input length.
  *}

fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document option"
where
  "applyOp [] []                       = Some []"
| "applyOp (Retain# as) (b# bs) = Option.map (\<lambda>ds. b# ds) (applyOp as bs)"
| "applyOp (Insert c# as) bs       = Option.map (\<lambda>ds. c# ds) (applyOp as bs)"
| "applyOp (Delete# as) (_# bs)  = applyOp as bs"
| "applyOp _  _                        = None"
           
text {* 
  Here is an example of an operation, and how it is being applied:
  \[ @{lemma "applyOp [Retain, Delete, Insert b, Retain] [a, x, c] = Some [a, b, c]" by simp} \]

  We now define the graph of the function @{term applyOp} as an inductive set; this makes
  inductive reasoning about @{term applyOp} easier.
  *}

inductive_set application :: "(('char operation \<times> 'char document) \<times> 'char document) set" where
  empty[intro!]:  "(([],[]),[]) \<in> application"
| retain[intro!]: "((a,d),d') \<in> application \<Longrightarrow> ((Retain#a,c#d),c#d')   \<in> application"
| delete[intro!]: "((a,d),d') \<in> application \<Longrightarrow> ((Delete#a,c#d),d')     \<in> application"
| insert[intro!]: "((a,d),d') \<in> application \<Longrightarrow> (((Insert c)#a,d),c#d') \<in> application"

text {* 
  We need to show the equality of the inductively defined set @{term application} and the partial
  function @{term applyOp} in order to use the inductive set for further proofs. We prove the 
  required eqivalence in both directions separately. 
  *}

lemma applyOpSet1 [rule_format]: 
  "\<forall>d'. applyOp a d = Some d' \<longrightarrow> ((a,d),d') \<in> application"
  by (rule applyOp.induct, auto)

lemma applyOpSet2: 
  "((a,d),d') \<in> application \<Longrightarrow> applyOp a d = Some d'"
  by (erule application.induct, auto)

lemma applyOpSet: "applyOp a d = Some d' \<longleftrightarrow> ((a,d),d') \<in> application"
  by (force intro: applyOpSet1 applyOpSet2)
  
subsection {* Input and Output Lengths *}

text{*
  Operations are partial, and can only be applied to documents of a specific length, 
  called the inputLength. The output length is the length of the result
  of the application on a document on which the operation is defined.
  
  The input length is the number of @{term Retain} and @{term Delete} actions, whereas
  the output length is the number of @{term Retain} and @{term Insert} actions.
*}

fun inputLength :: "'char operation \<Rightarrow> nat" where
  "inputLength [] = 0"
| "inputLength (Retain# as) = Suc (inputLength as)"
| "inputLength (Delete# as) = Suc (inputLength as)"
| "inputLength (Insert _# as)  = inputLength as"

fun outputLength :: "'char operation \<Rightarrow> nat" where
  "outputLength [] = 0"
| "outputLength (Retain# as)   = Suc (outputLength as)"
| "outputLength (Insert _# as) = Suc (outputLength as)"
| "outputLength (Delete# as)   = outputLength as"

text {* 
 Some lemmas to characterise operations by their length. If an operation @{term b} has input lenght 0, 
 @{term b} must contain only insert actions (or be empty); if an operation @{term b} has output
 length 0, @{term b} must contain only delete actions (or be empty); and if both input and 
 output length are 0, then @{term a} must be empty.
 *}

lemma emptyInputLength [rule_format]: "inputLength b = 0 \<longrightarrow> (\<forall> a \<in> set b. \<exists>c. a = Insert c)"
  by (induct_tac b rule: inputLength.induct,  force+)
  
lemma emptyOutputLength [rule_format]: "outputLength b = 0 \<longrightarrow> (\<forall> a \<in> set b. a = Delete)"
  by (induct_tac b rule: outputLength.induct, force+)

lemma emptyInOutLength [rule_format]: "inputLength a = 0 \<and> outputLength a = 0 \<longrightarrow> a = []"
  by (induct_tac a rule: inputLength.induct, auto)

text{*
 The following two lemmas show that @{term validInputLength} and @{term outputLength} really do
 as advertised. 
 *}

lemma validInputLength: "(\<exists>d'. applyOp a d = Some d') \<longleftrightarrow> (inputLength a = length d)"
  by (induct_tac a d rule: applyOp.induct, auto)
  
lemma validOutputLength: "(applyOp a d = Some d') \<Longrightarrow> (outputLength a= length d')"
  apply (simp add: applyOpSet)
  apply (erule application.induct, auto)
  done

subsection{* Semantics of Actions *}

text {* 
  A preliminary: an operation is empty iff it can only be applied to the empty document 
  and the result is also the empty document. The empty operation is, of course, the empty list. *}

lemma emptyInput: "applyOp [] d = Some d' \<longleftrightarrow> d = [] \<and> d' = []"
  by (induct_tac d, auto)

text{*
  The following three lemmas characterise the semantics of the basic actions in terms of
  the @{term application} set; e.g. the first one says that @{term Retain} copies the 
  character @{term c} from the input document to the output document.
  *}
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
  
section{* Composition *}

subsection{* The Function @{term addDeleteOp} *}

text{*
  The function @{term addDeleteOp} is an optimisation. It starts from the observation that 
  @{term Delete} and @{term "Insert c"} actions commute, i.e. we can exchange them and still get
  the same operation:
  \[ @{lemma "applyOp [Delete, Insert c] [x] = applyOp [Insert c, Delete] [x]" by simp } \]
  Hence, it makes sense to sort sequences of @{term Delete} and @{term Insert} actions in such
  a way that we get sequences contiguous @{term Delete} and @{term Insert} actions; we can then
  compress into one parameterised delelte action, or an insert action which takes a string as 
  argument.The @{term addDeleteOp} fuction adds a delete action, but commutes it as far back 
  into the argument as possible.
  *}  

fun addDeleteOp :: "'char operation \<Rightarrow> 'char operation"
where
  "addDeleteOp (Insert c# next) = Insert c# addDeleteOp next"
| "addDeleteOp as = Delete# as"


text{* 
  After two auxiliary lemmas  we will show that @{term addDeleteOp} really adds a delete action,
  in the sense that if we apply it then it removes the first element of the document.
  *}
 
lemma addDeleteOpValid11[rule_format]: "((a,d),d') \<in> application \<Longrightarrow> \<forall>c. ((addDeleteOp a,c#d),d') \<in> application"
  by (rule application.induct, auto)

lemma addDeleteOpValid1: "((Delete#as,d),d') \<in> application \<Longrightarrow> ((addDeleteOp as,d),d') \<in> application"
  by (smt action.distinct(3) action.distinct(5) addDeleteOpValid11 application.cases list.distinct(1) list.inject)

lemma addDeleteOpValid: "applyOp (addDeleteOp a) (c#d) = applyOp a d"
  by (rule addDeleteOp.induct, auto)

text{* 
  As can be expected, @{term addDeleteOp} does not change the @{term outputLength}. 
  This lemma is actually not needed in the following.
  *}
lemma addDeleteOutputLength: "outputLength (addDeleteOp as) = outputLength as"
  by (rule addDeleteOp.induct, auto)

subsection {* Composition of Operations *}

text {* 
  The @{term compose} function composes two operations @{term a} and @{term b}, in such a way
  that the composed operation @{term ab} has the same effect upon application as operations
  @{term a} and @{term b} executed sequentially.  
*}

fun compose :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation option"
where
  "compose [] []                              = Some []"
| "compose (Delete# as) bs               = Option.map addDeleteOp (compose as bs)"
| "compose as (Insert c# bs)             = Option.map (Cons (Insert c)) (compose as bs)"
| "compose (Retain# as) (Retain# bs) = Option.map (Cons Retain) (compose as bs)"
| "compose (Retain# as) (Delete# bs)  = Option.map addDeleteOp (compose as bs)"
| "compose (Insert c# as) (Retain# bs) = Option.map (Cons (Insert c)) (compose as bs)"
| "compose (Insert _# as) (Delete# bs) = compose as bs"
| "compose _ _                                = None"
 
text{* 
  Here is an example of how compose works:
  \[ @{lemma "compose [Retain, Delete, Insert b, Retain] [Retain, Retain, Insert c, Delete] 
               = Some [Retain, Insert b, Insert c, Delete, Delete]" by simp } \]
  Note how the @{term Insert} and @{term Delete} actions are grouped together.
  
  Following the approach from above, we define the graph of @{term compose} as an inductive set.
  *}

inductive_set composition :: "(('char operation \<times> 'char operation) \<times> 'char operation) set" where
  empty[intro!]:  "(([],[]),[]) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((Delete# a,b), addDeleteOp ab) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((a, Insert c#b), Insert c# ab) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((Retain# a, Retain#b), Retain# ab) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((Retain# a, Delete#b), addDeleteOp ab) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((Insert c# a, Retain# b),Insert c# ab) \<in> composition"
| [intro!]: "((a,b),ab) \<in> composition \<Longrightarrow> ((Insert _# a, Delete# b),ab) \<in> composition"

text {* 
  And again we prove that this set is graph of @{term compose}.
  We first need three lemmas, then the main lemma.
  *}

lemma composeSet11 [rule_format]: 
  "\<forall>ab c. compose a b = Some ab \<longrightarrow> compose a (Insert c # b) = Some (Insert c # ab)"
  by (rule compose.induct, auto)

lemma composeSet1: "((a,b),ab) \<in> composition \<Longrightarrow> compose a b = Some (ab)"
  by (erule composition.induct, auto intro: composeSet11)

lemma composeSet2 [rule_format]: "\<forall>ab. compose a b = Some ab \<longrightarrow> ((a,b),ab) \<in> composition"
  apply (rule compose.induct)
  apply (auto)
  done

lemma composeSet: "((a,b), ab) \<in> composition \<longleftrightarrow> compose a b = Some ab"
  by (auto intro: composeSet1 composeSet2)

subsection {* Composable Operations. *}

text {* 
  The operations @{term a} and @{term b} can be composed iff the output length of @{term a} 
  is the input length of @{term b}. We need three lemmas before the main result. 
  *}

lemma composeDomain1 [rule_format]: "(\<exists>ab. compose a b = Some ab) \<longrightarrow> outputLength a = inputLength b"
  by (rule compose.induct, auto)

lemma composeDomain21 [rule_format]: "compose a b = None \<longrightarrow> outputLength a \<noteq> inputLength b"
  by (rule compose.induct, auto)

lemma composeDomain2: "outputLength a = inputLength b \<Longrightarrow> (\<exists>ab. compose a b = Some ab)"
  apply (erule contrapos_pp)
  by (simp add: composeDomain21)

lemma composeDomain: "(\<exists>ab. compose a b = Some ab) \<longleftrightarrow> outputLength a = inputLength b"
  by (auto intro: composeDomain1 composeDomain2)
    
subsection{* Correctness of the Composition *}

text {* 
  Finally, we show that the @{term compose} function does actually compose operations, in the 
  sense that applying the composed operation is the same as applying the two arguments consecutively.
  We first show this using the graph @{term composition}, then transfer this to the function using the 
  conversion theorems @{text applyOpSet} and @{text composeSet}.
  *}

lemma compositionInv [rule_format]: "((a,b),ab) \<in> composition \<Longrightarrow> \<forall>d d' d''. ((a,d),d') \<in> application \<longrightarrow> ((b,d'),d'') \<in> application \<longrightarrow> ((ab,d),d'') \<in> application"
  apply (erule composition.induct)
  apply (auto simp add: emptyInput addDeleteOpValid11 remDelete remInsert remRetain)
  by (metis applyOpSet emptyInput)
  
theorem composeCorrect: 
  "\<lbrakk> compose a b = Some ab; applyOp a d = Some d'; applyOp b d' = Some d'' \<rbrakk> 
   \<Longrightarrow> applyOp ab d = Some d''"
  by (simp add: composeSet applyOpSet compositionInv)

section{* Transforming Operations *}

text {* 
  The transformation function is the basis of operational transformation. For a pair of 
  operations @{term "(a,b)"} it computes an output pair of transformed operations 
  @{term "(a',b')"}, such that @{term "compose a b' = compose b a'"}; this is the 
  main correctness property of operational transformation.
  *}

fun transform :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> ('char operation \<times> 'char operation) option"
where
  "transform [] []                 = Some ([], [])"
| "transform (Insert c#as) bs  = 
              Option.map (\<lambda>(at, bt). (Insert c# at, Retain# bt)) (transform as bs)"
| "transform as (Insert c# bs) = 
              Option.map (\<lambda>(at, bt). (Retain# at, Insert c# bt)) (transform as bs)"
| "transform (Retain# as) (Retain# bs) = 
              Option.map (\<lambda>(at, bt). (Retain# at, Retain# bt)) (transform as bs)"
| "transform (Delete# as) (Delete# bs) = transform as bs"
| "transform (Retain# as) (Delete# bs) = 
              Option.map (\<lambda>(at, bt). (at, Delete# bt)) (transform as bs)"
| "transform (Delete# as) (Retain# bs) = 
              Option.map (\<lambda>(at, bt). (Delete# at, bt)) (transform as bs)"
| "transform _ _                           = None"

text {* 
  The transformation of two operations yields a result iff they have an equal input length.
  *}

lemma transformDomain: "(\<exists>ab. transform a b = Some ab) \<longleftrightarrow> inputLength a = inputLength b"
  by (induct_tac a b rule: transform.induct, auto)  

text {* 
  Again, we define its graph inductively.
  *}

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

text{*
  Here, it is enough to show that this set is a superset of the function graph.
  *}

lemma transformSubset[rule_format]: "\<forall>a' b'. transform a b = Some (a',b') \<longrightarrow> ((a,b),(a',b')) \<in> transformation"
  by (rule transform.induct, auto)  

text {* 
  We can now show the main correctness property, first for the set @{term transformation}. 
  *}

lemma transformationConvergence: "((a,b), (a',b')) \<in> transformation \<Longrightarrow>
                                   (\<exists>ab. ((a,b'), ab) \<in> composition \<and> ((b,a'), ab) \<in> composition)"
  by (erule transformation.induct, auto)  

text {* 
  We now show the correctness of the @{term transform} function. Because the equality involving
  @{term transform} occurs only in the precondition, we only need that @{term transformation} is a 
  superset of the function graph to reduce that precondition to the one of @{text transformationConvergence}.
  *}

theorem transformCorrect: "transform a b = Some (a',b')
  \<Longrightarrow> compose a b' \<noteq> None \<and> compose a b' = compose b a'"  
  apply (drule transformSubset)
  apply (drule transformationConvergence)
  by (auto simp add: composeSet)  

text{*  
  This concludes the main development. 
  *}
  
section{* Normalization *}

text {*
 Normalisation is what occurs during composition. We say an operation is normalised if 
 there is no @{term Delete} operation followed by an @{term Insert}. (We could do this the other
 way around, but have to pick on one order.)  
 *}
 
fun normalized :: "'char operation \<Rightarrow> bool"
where
  "normalized [] = True"
| "normalized (Delete# (Insert _# _))= False"
| "normalized (_ # as) = normalized as"

text{*
 The @{term normalize} function sorts all those subsequences not containing @{term Retain} actions,
 such that all @{term Insert} actions occur before the @{term Delete} actions.
 *}

fun normalize :: "'char operation \<Rightarrow> 'char operation" where
  "normalize [] = []"
| "normalize (Retain#a) = Retain#(normalize a)"
| "normalize (Insert c#a) = Insert c#(normalize a)"
| "normalize (Delete#a) = addDeleteOp (normalize a)"

text{*
  Here is an example of how normalize works:
  \[ @{lemma "normalize [Delete, Insert a, Delete, Insert b, Retain, Insert c] = [Insert a, Insert b, Delete, Delete, Retain, Insert c]" by simp} \]

  To show correctness of @{term normalizes}, we first need lemma that @{term addDeletOp} preserves
  normalisation. 
  *}

lemma addDeleteOpNormalized[rule_format]: "normalized a \<longrightarrow> normalized (addDeleteOp a)"
  by (induct a rule: addDeleteOp.induct, simp_all)

lemma normalizes: "normalized (normalize a)"
  by (induct a rule: normalize.induct, simp_all add: addDeleteOpNormalized)

text{*
  We also show that normalized operations are fixpoints of the @{term normalize} function,
  or in more elementary terms, normalizing once is enough.
  *}
  
lemma normalized_fix: "normalized a \<longleftrightarrow> (normalize a= a)"
  apply (rule iffI)
  apply (induct a rule: normalize.induct)
  apply (simp_all)
  apply (case_tac "a", simp)
  apply (case_tac "aa", simp_all)
  apply (rule subst [where P="normalized"]) --{* Strange, we have to do this by hand. *}
  apply (assumption, rule normalizes)
  done

text {* 
 @{term normalize} should not change the effect of an operation:
 if an operation $a$ can be applied to a document $d$ yielding the resulting document $d'$,
 the normalized operation $a$ can also be applied to the document $d$ yielding the same 
 result.
*}

lemma normalizeValid1: "((a,d),d') \<in> application \<Longrightarrow> ((normalize a,d),d') \<in> application"
  apply (erule application.induct)
  apply (auto intro: addDeleteOpValid1)
  done

lemma normalizeValid: "applyOp a d = Some d' \<Longrightarrow> applyOp(normalize a) d= Some d'"
  apply (fast intro: applyOpSet2 applyOpSet1 normalizeValid1)
  done


text{* The result of @{term compose} is always normalized. *}

lemma composeNormalized[rule_format]: "\<forall>ab. compose a b = Some ab \<longrightarrow> normalized ab"
  by (rule compose.induct, auto intro:  addDeleteOpNormalized)

section{* Identities *}

text{*
  The identity operation consists of only @{term Retain} actions. In fact, the identity
  operation is parameterised over the length of the argument, so there is one identity
  for each document length.
  *}

fun ident :: "nat=> 'char operation"
where
  "ident n = replicate n Retain"

text{*
  @{term ident} has exactly the input and output lengths that we expect.
  *}

lemma identInputLength: "inputLength (ident n)= n"
 by (induct n, auto)

lemma identOutputLength: "outputLength (ident n)= n"
 by (induct n, auto)

text{*
  Moreover, @{term ident} behaves as a left and right unit to the composition, but 
  note that it is only equal up to normalisation, as composition normalises its result.
  *}
 
lemma composeIdL: "compose (ident (inputLength b)) b = Some (normalize b)"
  apply (induct_tac b, simp)
  apply (case_tac "inputLength list")
  apply (case_tac a, simp_all)
  by (case_tac a, simp_all)

lemma composeIdR: "compose b (ident (outputLength b))= Some (normalize b)"
  apply (induct_tac b, simp)
  apply (case_tac "inputLength list")
  apply (case_tac a, simp_all)
  by (case_tac a, simp_all)

text{*
  Transforming against @{term ident} does not change the operation (it does not 
  even normalize), and @{term ident} transformed gives the identity again.
  *}
  
lemma transformIdL: 
  "transform (ident (inputLength b)) b = Some (ident (outputLength b), b)"
  apply (induct_tac b, simp)
  apply (case_tac "inputLength list")
  apply (case_tac a, simp_all)
  by (case_tac a, simp_all)

lemma transformIdR: 
  "transform b (ident (inputLength b))= Some (b, ident (outputLength b))"
  apply (induct_tac b, simp)
  apply (case_tac "inputLength list")
  apply (case_tac a, simp_all)
  by (case_tac a, simp_all)
  
export_code applyOp compose transform in Scala
  module_name Operation

end
