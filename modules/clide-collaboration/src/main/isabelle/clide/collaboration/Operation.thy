theory Operation
imports Main List Option Set SimpleOperation 
begin

datatype 'char action = Retain nat | Insert "'char list" | Delete nat

type_synonym 'char operation = "'char action list"

text {* We define an inductive set of all operations and their equivalent simple operations *}

inductive_set operations :: "('char SimpleOperation.operation \<times> 'char operation) set" where
  empty[intro!]:  "([],[]) \<in> operations"
| retain[intro!]: "(a,b) \<in> operations \<Longrightarrow> (append (List.replicate n SimpleOperation.Retain) a, Retain n#b) \<in> operations"
| insert[intro!]: "(a,b) \<in> operations \<Longrightarrow> (append (List.map SimpleOperation.Insert s) a, Insert s#b) \<in> operations"
| delete[intro!]: "(a,b) \<in> operations \<Longrightarrow> (append (List.replicate n SimpleOperation.Delete) a, Delete n#b) \<in> operations"

lemma singleRetain: "a \<in> Domain operations \<Longrightarrow> SimpleOperation.Retain#a \<in> Domain operations"
  sorry

lemma singleInsert: "a \<in> Domain operations \<Longrightarrow> SimpleOperation.Insert c#a \<in> Domain operations"
  sorry

lemma singleDelete: "a \<in> Domain operations \<Longrightarrow> SimpleOperation.Delete#a \<in> Domain operations"
  sorry


lemma operationsComplete1: "a \<in> Domain operations"
  apply (induct_tac a, force)
  apply (case_tac a, auto simp add: singleRetain singleInsert singleDelete)
  done

lemma operationsComplete2: "a \<in> Range operations"
  apply (induct_tac a, force)
  apply (case_tac a, auto)
  done

fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document"
where
  "applyOp ([])            ([])  = []"
| "applyOp (Retain n#next) (doc) = append (take n doc) (applyOp next (drop n doc))"
| "applyOp (Insert s#next) (doc) = append s (applyOp next doc)"
| "applyOp (Delete n#next) (doc) = applyOp next (drop n doc)"

lemma applyOpEq: "(a,b) \<in> operations \<Longrightarrow> \<forall> d'. SimpleOperation.applyOp a d = Some d' \<longrightarrow> applyOp b d = d'" 
  apply (rule operations.induct)
    apply (simp)    
  sorry

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

lemma composeEq: "(a, b) \<in> operations \<Longrightarrow> (a', b') \<in> operations \<Longrightarrow> SimpleOperation.compose a a' = Some a'' \<Longrightarrow> (a'', Operation.compose b b') \<in> operations"
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

end
