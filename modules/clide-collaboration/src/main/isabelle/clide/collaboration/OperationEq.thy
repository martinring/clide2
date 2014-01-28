theory OperationEq
imports Main List Option Set SimpleOperation 
begin

datatype 'char action = Retain nat | Insert "'char list" | Delete nat

type_synonym 'char operation = "'char action list"

text {* We define an inductive set of all operations and their equivalent simple operations *}

inductive_set operations :: "('char SimpleOperation.operation \<times> 'char operation) set" where
  empty[intro!]:  "([],[]) \<in> operations"
| retain1[intro!]: "(a,b) \<in> operations \<Longrightarrow> (SimpleOperation.Retain#a, Retain 1#b) \<in> operations"
| insert1[intro!]: "(a,b) \<in> operations \<Longrightarrow> (SimpleOperation.Insert c#a, Insert [c]#b) \<in> operations"
| delete1[intro!]: "(a,b) \<in> operations \<Longrightarrow> (SimpleOperation.Delete#a, Delete 1#b) \<in> operations"
| retainN[intro!]: "(a,Retain n#b) \<in> operations \<Longrightarrow> (SimpleOperation.Retain#a, Retain (n+1)#b) \<in> operations"
| insertN[intro!]: "(a,Insert s#b) \<in> operations \<Longrightarrow> (SimpleOperation.Insert c#a, Insert (c#s)#b) \<in> operations"
| deleteN[intro!]: "(a,Delete n#b) \<in> operations \<Longrightarrow> (SimpleOperation.Delete#a, Delete (n+1)#b) \<in> operations"

lemma operationsComplete: "a \<in> Domain operations"
  by (induct_tac a, auto, case_tac a, auto)

fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document"
where
  "applyOp ([])                  ([])   = []"
| "applyOp (Retain 0#next)       (d)    = applyOp next d"
| "applyOp (Insert s#next)       (d)    = append s (applyOp next d)"
| "applyOp (Delete 0#next)       (d)    = applyOp next d"
| "applyOp (Retain (Suc n)#next) (c#cs) = c#(applyOp (Retain n#next) cs)"
| "applyOp (Delete (Suc n)#next) (c#cs) =    applyOp (Delete n#next) cs"
| "applyOp (_)                   (_)    = undefined"

lemma applyOpEq: "(a,b) \<in> operations \<Longrightarrow> SimpleOperation.applyOp a d = Some d' \<Longrightarrow> applyOp b d = d'" 
  apply (drule SimpleOperation.applyOpSet1)
  apply (induct a b rule: operations.induct, auto)

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
  sorry

export_code applyOp compose transform in Scala
  module_name Operation

end
