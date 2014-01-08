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

lemma applyOpEq: "(a,b) \<in> operations \<Longrightarrow> SimpleOperation.applyOp a d = Some d' \<Longrightarrow> applyOp b d = d'" 
  sorry

(*fun compose :: "'char operation \<Rightarrow> 'char operation \<Rightarrow> 'char operation"
  "compose *)

end
