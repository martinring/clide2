(* Formalisation of Operational Transformation *)
(* author: Martin Ring, DFKI Bremen *) (*<*) 

theory Operation
imports Main List Option Set
begin (*>*)

section {* Actions, Operations and Documents *}

text {* A @{term document} is a list of elements. *}

type_synonym 'char document = "'char list"

text {* An @{term action} can either alter the document at the current position or move the virtual 
        cursor on the document forward or do both. *}

datatype 'char action = Retain nat | Insert 'char "'char list" | Delete nat

text {* An @{term operation} is a list of actions. *}

type_synonym 'char operation = "'char action list"

text {* There are three types of actions of which an operation is composed:
        @{term Retain}, @{term "Insert c"} and @{term Delete}. An operation is
        a list of actions.

        \begin{itemize}
          \item @{term "Retain n"} moves the cursor @{term "n + 1"} positions forward, not altering 
                                   the text.
          \item @{term "Insert c cs"} inserts elements in @{term "c#cs"} at the position of the cursor 
                                      and moves the cursor behind these elements.
          \item @{term "Delete n"} deletes the next @{term "n + 1"} elements of the document, not 
                                   moving the cursor.
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
| "inputLength (Retain n#xs) = (1 + n) + inputLength xs"
| "inputLength (Insert c cs#xs) = inputLength xs"
| "inputLength (Delete n#xs) = (1 + n) + inputLength xs"

text {* if an operation @{term a} has input lenght 0, a must be empty or it consists only of insert 
        actions *}

lemma emptyInputInsert [rule_format]: "inputLength a = 0 \<longrightarrow> a = [] \<or> (\<exists>as c cs. a = Insert c cs#as)"
  apply (induct_tac a, safe)
  apply (case_tac a, auto)+
  done

fun outputLength :: "'char operation \<Rightarrow> nat" where
  "outputLength [] = 0"
| "outputLength (Retain n#xs) = (1 + n) + outputLength xs"
| "outputLength (Insert s ss#xs) = (1 + length ss) + outputLength xs"
| "outputLength (Delete _#xs) = outputLength xs"

text {* if an operation @{term a} has output lenght 0, @{term a} must be empty or is consists only 
        of delete actions *}

lemma emptyOutputDelete [rule_format]: "outputLength a = 0 \<longrightarrow> a = [] \<or> (\<exists>as n. a = Delete n#as)"
  apply (induct_tac a, auto)
  apply (case_tac a, auto)+
  done  

text {* if an operation @{term a} has output and input lenght of @{term 0}, the operation must be empty *}

lemma emptyInOutOp [rule_format]: "inputLength a = 0 \<and> outputLength a = 0 \<longrightarrow> a = []"
  apply (induct_tac a, auto)
  apply (case_tac a, auto)+
  done

section {* Application function *}

text {* The @{term applyOp} function applies an operation @{term a} to document @{term d} and yields 
        either @{term None} if the input length of @{term a} does not match the length of @{term d} 
        or @{term "Some d'"} where @{term d'} is the result of a valid application *}

fun splitRec :: "nat \<Rightarrow> 'char document \<Rightarrow> 'char document \<Rightarrow> ('char document \<times> 'char document) option" where
  "splitRec 0 (y#ys) xs = Some (append xs [y],ys)"
| "splitRec n (y#ys) xs = splitRec (n - 1) ys (append xs [y])"
| "splitRec _ _ _ = None"

definition split :: "nat \<Rightarrow> 'char document \<Rightarrow> ('char document \<times> 'char document) option" where
  "split n ys = splitRec n ys []"

fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document option"
where
  empty[intro!]:  "applyOp ([])               ([])  = Some []"
| retain[intro!]: "applyOp (Retain n#next)    (doc) = Option.bind (split n doc) (\<lambda>(l,r). Option.map (append l) (applyOp next r))"
| insert[intro!]: "applyOp (Insert c cs#next) (doc) = Option.map (append (c#cs)) (applyOp next doc)"
| delete[intro!]: "applyOp (Delete n#next)    (doc) = Option.bind (split n doc) (\<lambda>(_,r). applyOp next r)"
| "applyOp _                  _     = None"

subsection {* Valid Operations *}

text {* iff an operation @{term a} is empty it can only be applied to the empty document and the
        result is also the empty document *}

lemma emptyInput: "applyOp [] d = Some d' \<longleftrightarrow> d = [] \<and> d' = []"  
  by (case_tac d, auto)

lemma emptyInputDomain[rule_format]: "(\<exists> d'. applyOp [] d = Some d') \<longleftrightarrow> d = []"
  by (auto simp add: emptyInput)

lemma emptyDocInsert: "\<exists>d'. applyOp (a#as) [] = Some d' \<Longrightarrow> \<exists>c cs. a = Insert c cs"
  sorry

text {* every document can be produced by the application of an operation to a document *}

lemma applicationRange: "\<exists>a d. applyOp a d = Some d'"  
  apply (induct_tac d')
  apply (auto)
  by (metis Operation.empty Operation.insert append_Nil2 option_map_Some)

subsection {* In- and Output Lenghts of Valid Operations *}

text {* All pairs of operations and documents are contained in the domain of the application
        iff the inputLength of the operation matches the length of the document *}

lemma applicationDomain[rule_format]: 
  "(\<exists> d'. applyOp a d = Some d') \<longleftrightarrow> inputLength a = length d"
  apply (induct_tac a)
  apply (simp add: emptyInputDomain)
  apply (case_tac a) 
  apply (simp_all)
  oops

lemma validOutputLength: "applyOp a d = Some d' \<Longrightarrow> outputLength a = length d'"
  oops

section {* Composition of Operations *}

fun addRetain :: "nat \<Rightarrow> 'char operation \<Rightarrow> 'char operation" where  
  "addRetain n (Retain m#xs) = (Retain (n + m))#xs"
| "addRetain n xs            = (Retain n)#xs"

fun addInsert :: "'char \<Rightarrow> 'char list \<Rightarrow> 'char operation \<Rightarrow> 'char operation" where 
  "addInsert s ss (Delete d#xs)    = (Delete d)#addInsert s ss xs"
| "addInsert s ss (Insert c cs#xs) = (Insert c (append cs (s#ss)))#xs"
| "addInsert s ss xs               = (Insert s ss)#xs"

fun addDelete :: "nat \<Rightarrow> 'char operation \<Rightarrow> 'char operation" where  
  "addDelete n (Delete m#xs) = (Delete (n + m))#xs"
| "addDelete n xs            = (Delete n)#xs"

text {* The @{term compose} function composes two operations @{term a} and @{term b}, in such a way
        that the composed operation @{term ab} has the same effect upon application as operations
        @{term a} and @{term b} executed sequentially. *}

fun composeRec :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation" where
  "composeRec [] [] xs  = xs" 
| "composeRec ((Delete n)#as) (bb) xs = composeRec as bb (addDelete n xs)"
| "composeRec (aa) ((Insert c cs)#bs) xs = composeRec aa bs (addInsert c cs xs)"
| "composeRec ((Retain n)#as) ((Retain m)#bs) xs = 
   (if      (n < m) then composeRec as (Retain (m - n)#bs) (addRetain n xs)
    else if (n = m) then composeRec as bs (addRetain n xs)
    else                 composeRec (Retain (n - m)#as) bs (addRetain n xs))"
| "composeRec ((Retain n)#as) ((Delete m)#bs) xs =
   (if      (n < m) then composeRec as (Delete(m - n)#bs) (addDelete n xs)
    else if (n = m) then composeRec as bs (addDelete n xs)
    else                 composeRec (Retain(n - m)#as) bs (addDelete n xs))"
| "composeRec ((Insert c cs)#as) ((Retain m)#bs) xs =
   (if      (length cs < m) then composeRec as (Delete(m - length cs)#bs) (addInsert c cs xs)
    else if (length cs = m) then composeRec as bs (addInsert c cs xs)
    else                         composeRec (Insert c (drop m cs)#as) bs (addInsert c (take m cs) xs))"
| "composeRec ((Insert c cs)#as) ((Delete m)#bs) xs =
   (if      (length cs < m) then composeRec as (Delete(m - length cs)#bs) xs
    else if (length cs = m) then composeRec as bs xs
    else                         composeRec (Insert c (drop m cs)#as) bs xs)"
| "composeRec _ _ _ = undefined"

definition compose :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation" where
  "compose a b = composeRec a b []"

section {* Operation Transformation *}

text {* The transformation function is the basis of operational transformation. For a pair of 
        operations @{term "(a,b)"} it computes an output pair of transformed operations 
        @{term "(a',b')"}. The convergence property @{term "compose a b' = compose b a'"} enables
        the OT system to execute operations in different order at different sites while the 
        documents do not diverge *}

fun transformRec :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation \<times> 'char operation" where
  "transformRec [] [] xs ys = (xs,ys)"
| "transformRec (Insert c cs#as) bs xs ys = transformRec as bs (addInsert c cs xs) (addRetain (length cs) ys)"
| "transformRec as (Insert c cs#bs) xs ys = transformRec as bs (addRetain (length cs) xs) (addInsert c cs ys)"
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
| "transformRec _ _ _ _ = undefined"

definition transform :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> ('char operation \<times> 'char operation)" where
  "transform a b = transformRec a b [] []"

export_code applyOp compose transform in Scala
  module_name Operation

end
