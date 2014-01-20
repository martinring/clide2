theory Operation
imports Main List Option Set SimpleOperation 
begin

section {* Aggregated Actions *}

lemma retainN: "((a,d),d') \<in> application \<longrightarrow> (((replicate (length init) Retain)@a,init@d),init@d') \<in> application"
  by (induct_tac init, auto)

lemma insertN: "((a,d),d') \<in> application \<longrightarrow> (((map Insert init)@a,d),init@d') \<in> application"
  by (induct_tac init, auto)

lemma deleteN: "((a,d),d') \<in> application \<longrightarrow> (((replicate (length init) Delete)@a,init@d),d') \<in> application"
  by (induct_tac init, auto)

datatype 'char action = Retain nat | Insert "'char list" | Delete nat

type_synonym 'char operation = "'char action list"

text {* We define an inductive set of all operations and their equivalent simple operations *}

inductive_set operations :: "('char SimpleOperation.operation \<times> 'char operation) set" where
  empty[intro!]:  "([],[]) \<in> operations"
| retain[intro!]: "(a,b) \<in> operations \<Longrightarrow> ((List.replicate n SimpleOperation.Retain) @ a, Retain n#b) \<in> operations"
| insert[intro!]: "(a,b) \<in> operations \<Longrightarrow> ((List.map SimpleOperation.Insert s) @ a,       Insert s#b) \<in> operations"
| delete[intro!]: "(a,b) \<in> operations \<Longrightarrow> ((List.replicate n SimpleOperation.Delete) @ a, Delete n#b) \<in> operations"

lemma retain1: "SimpleOperation.Retain#a   = append (List.replicate 1 SimpleOperation.Retain) a" by (auto)
lemma insert1: "SimpleOperation.Insert c#a = append (List.map SimpleOperation.Insert [c]) a" by (auto)
lemma delete1: "SimpleOperation.Delete#a   = append (List.replicate 1 SimpleOperation.Delete) a" by (auto)

lemma operationsComplete1: "\<exists>b. (a,b) \<in> operations"
  apply (induct_tac a, force)
  apply (case_tac a, auto)
  apply (subst retain1, metis operations.retain)
  apply (subst insert1, metis operations.insert)
  apply (subst delete1, metis operations.delete)
  done

lemma operationsComplete2: "\<exists>a. (a,b) \<in> operations"
  apply (induct_tac b, force)
  apply (case_tac a, auto)
  done

lemma emptyOperations: "(a,[]) \<in> operations \<Longrightarrow> a = []"
  sorry

fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document"
where
  "applyOp ([])            ([])  = []"
| "applyOp (Retain n#next) (doc) = append (take n doc) (applyOp next (drop n doc))"
| "applyOp (Insert s#next) (doc) = append s (applyOp next doc)"
| "applyOp (Delete n#next) (doc) = applyOp next (drop n doc)"

inductive_set application :: "(('char SimpleOperation.operation \<times> 'char operation \<times> 'char document) \<times> 'char document) set" where
  empty[intro!]:  "(([],[],[]),[]) \<in> application"
| retain[intro!]: "((a,b,d),d') \<in> application \<Longrightarrow> (((List.replicate (length init) SimpleOperation.Retain) @ a,Retain (length init)#b,init@d),init@d') \<in> application"
| insert[intro!]: "((a,b,d),d') \<in> application \<Longrightarrow> (((List.map SimpleOperation.Insert init) @ a,Insert init#b,d),init@d') \<in> application"
| delete[intro!]: "((a,b,d),d') \<in> application \<Longrightarrow> (((List.replicate (length init) SimpleOperation.Delete) @ a,Delete (length init)#b,init@d),d') \<in> application"

lemma applicationEq1: "((a,b,d),d') \<in> application \<Longrightarrow> ((a,d),d') \<in> SimpleOperation.application"
  by (erule application.induct, auto simp add: retainN insertN deleteN)

lemma applyOpSet1: "((a,b,d),d') \<in> application \<Longrightarrow> applyOp b d = d'"
  by (erule application.induct, auto)

lemma applyOpCompl: "(a,b) \<in> operations \<Longrightarrow> \<exists>d d'. ((a,b,d),d') \<in> application"
  apply (erule operations.induct, auto)  
  apply (metis Ex_list_of_length application.retain)
  apply (metis Ex_list_of_length application.delete)
  done

lemma applaOpCompl': "((a,b,d),d') \<in> application \<Longrightarrow> (a,b) \<in> operations"
  by (erule application.induct, auto)

text {* something missing here... *}

fun addRetain :: "nat \<Rightarrow> 'char operation \<Rightarrow> 'char operation" where
  "addRetain n (Retain m#xs) = (Retain (n + m))#xs"
| "addRetain n xs            = (Retain n)#xs"

fun addInsert :: "'char list \<Rightarrow> 'char operation \<Rightarrow> 'char operation" where
  "addInsert s (Delete d#xs) = (Delete d)#addInsert s xs"
| "addInsert s (Insert t#xs) = (Insert (append t s))#xs"
| "addInsert s xs            = (Insert s)#xs"

fun addDelete :: "nat \<Rightarrow> 'char operation \<Rightarrow> 'char operation" where
  "addDelete n (Delete m#xs) = (Delete (n + m))#xs"
| "addDelete n xs            = (Delete n)#xs"

fun composeRec :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation" where
  "composeRec [] [] xs  = xs" 
| "composeRec ((Delete n)#as) (bb) xs = composeRec as bb (addDelete n xs)"
| "composeRec (aa) ((Insert s)#bs) xs = composeRec aa bs (addInsert s xs)"
| "composeRec ((Retain n)#as) ((Retain m)#bs) xs =
   (if      (n < m) then composeRec as (Retain(m - n)#bs) (addRetain n xs)
    else if (n = m) then composeRec as bs (addRetain n xs)
    else                 composeRec (Retain(n - m)#as) bs (addRetain n xs))"
| "composeRec ((Retain n)#as) ((Delete m)#bs) xs =
   (if      (n < m) then composeRec as (Delete(m - n)#bs) (addDelete n xs)
    else if (n = m) then composeRec as bs (addDelete n xs)
    else                 composeRec (Retain(n - m)#as) bs (addDelete n xs))"
| "composeRec ((Insert s)#as) ((Retain m)#bs) xs =
   (if      (length s < m) then composeRec as (Delete(m - length s)#bs) (addInsert s xs)
    else if (length s = m) then composeRec as bs (addInsert s xs)
    else                        composeRec (Insert(drop m s)#as) bs (addInsert (take m s) xs))"
| "composeRec ((Insert s)#as) ((Delete m)#bs) xs =
   (if      (length s < m) then composeRec as (Delete(m - length s)#bs) xs
    else if (length s = m) then composeRec as bs xs
    else                        composeRec (Insert(drop m s)#as) bs xs)"

definition compose :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation" where
  "compose a b = composeRec a b []"

lemma composeEq: "(a, b) \<in> operations \<Longrightarrow> 
                  (a', b') \<in> operations \<Longrightarrow> 
                  SimpleOperation.compose a a' = Some a'' \<Longrightarrow> 
                  (a'', Operation.compose b b') \<in> operations"
  sorry

fun transformRec :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation \<times> 'char operation" where
  "transformRec [] [] xs ys = (xs,ys)"
| "transformRec (Insert s#as) bs xs ys = transformRec as bs (addInsert s xs) (addRetain (length s) ys)"
| "transformRec as (Insert s#bs) xs ys = transformRec as bs (addRetain (length s) xs) (addInsert s ys)"
| "transformRec (Retain n#as) (Retain m#bs) xs ys = 
   (if      (n < m) then transformRec as ((Retain (m - n))#bs) (addRetain n xs) (addRetain n ys)
    else if (n = m) then transformRec as bs (addRetain n xs) (addRetain n ys)
    else                 transformRec ((Retain (n - m))#as) bs (addRetain m xs) (addRetain m ys))"
| "transformRec (Delete n#as) (Delete m#bs) xs ys = 
   (if      (n < m) then transformRec as ((Delete (m - n))#bs) xs ys
    else if (n = m) then transformRec as bs xs ys
    else                 transformRec ((Delete (n - m))#as) bs xs ys)"
| "transformRec (Retain n#as) (Delete m#bs) xs ys = 
   (if      (n < m) then transformRec as ((Delete (m - n))#bs) xs (addDelete n ys)
    else if (n = m) then transformRec as bs xs (addDelete m ys)
    else                 transformRec ((Retain (n - m))#as) bs xs (addDelete m ys))"
| "transformRec (Delete n#as) (Retain m#bs) xs ys = 
   (if      (n < m) then transformRec as ((Retain (m - n))#bs) (addDelete n xs) ys
    else if (n = m) then transformRec as bs (addDelete n xs) ys
    else                 transformRec ((Delete (n - m))#as) bs (addDelete m xs) ys)"

definition transform :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> ('char operation \<times> 'char operation)" where
  "transform a b = transformRec a b [] []"

lemma transformEq: "(a, a') \<in> operations \<Longrightarrow>
                    (b, b') \<in> operations \<Longrightarrow>
                    SimpleOperation.transform a b = Some (c,d) \<Longrightarrow> 
                    (c, fst (Operation.transform a' b')) \<in> operations \<and>
                    (d, snd (Operation.transform a' b')) \<in> operations"
  apply (auto)
  sorry

export_code applyOp compose transform in Scala
  module_name Operation

end
