theory Operation
imports Main SimpleOperation
begin

datatype 'char action = Retain nat | Insert "'char list" | Delete nat

type_synonym 'char operation = "'char action list"

fun applyOp :: "'char operation \<Rightarrow> 'char document \<Rightarrow> 'char document option"
where
  "applyOp ([])            ([])  = Some []"
| "applyOp (Retain n#next) (doc) = Option.map (\<lambda>d. take n doc#d) (applyOp next (drop n doc))"
| "applyOp (Insert s#next) (doc) = Option.map (\<lambda>d. append s d) (applyOp next doc)"
| "applyOp (Delete n#next) (doc) = applyOp next (drop n doc)"
| "applyOp _               _     = None"

end
