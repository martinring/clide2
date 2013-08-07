theory Operation
imports Main List
begin

datatype 'char Action = Retain | Insert 'char | Delete 

function lengthBeforeOp :: "'char Action list \<Rightarrow> nat"
where
  "lengthBeforeOp [] = 0"
| "lengthBeforeOp (Retain#next)    = 1 + lengthBeforeOp next"
| "lengthBeforeOp (Delete#next)    = 1 + lengthBeforeOp next"
| "lengthBeforeOp (Insert(_)#next) = 0 + lengthBeforeOp next"
by pat_completeness auto

fun lengthAfterOp :: "'char Action list \<Rightarrow> nat"
where
  "lengthAfterOp [] = 0"
| "lengthAfterOp (Retain#next)    = 1 + lengthAfterOp next"
| "lengthAfterOp (Delete#next)    = 0 + lengthAfterOp next"
| "lengthAfterOp (Insert(_)#next) = 1 + lengthAfterOp next"

fun applyOp :: "'char Action list \<Rightarrow> 'char list \<Rightarrow> 'char list option"
where
  "applyOp [] [] = Some []"
| "applyOp (Retain#next)   (head#tail) = Option.map (\<lambda>a. head#a) (applyOp next tail)"
| "applyOp (Insert c#next) (head#tail) = Option.map (\<lambda>a. c#a) (applyOp next (head#tail))"
| "applyOp (Delete#next)   (head#tail) = applyOp next tail"
| "applyOp _ _ = None"

fun addDeleteOp :: "'char Action list \<Rightarrow> 'char Action list"
where
  "addDeleteOp (Insert c#next) = (Insert c)#(addDeleteOp next)"
| "addDeleteOp as = Delete#as"

fun compose :: "'char Action list \<Rightarrow> 'char Action list \<Rightarrow> 'char Action list option"
where
  "compose [] [] = Some []"
| "compose (Delete#as)    (bs)          = Option.map (addDeleteOp) (compose as bs)"
| "compose (as)           (Insert c#bs) = Option.map (\<lambda>a. Insert(c)#a) (compose as bs)"
| "compose (Retain#as)    (Retain#bs)   = Option.map (\<lambda>a. Retain#a) (compose as bs)"
| "compose (Retain#as)    (Delete#bs)   = Option.map (addDeleteOp) (compose as bs)"
| "compose (Insert(c)#as) (Retain#bs)   = Option.map (\<lambda>a. Insert(c)#a) (compose as bs)"
| "compose (Insert(_)#as) (Delete#bs)   = compose as bs"
| "compose _ _ = None"

lemma compose_complete: "\<forall> a b. (lengthAfterOp a) = (lengthBeforeOp b) \<longleftrightarrow> isSome (compose a b)"  
  oops

lemma compose_inv: "\<forall> a b d. Option.bind (compose a b) (\<lambda>op'. applyOp op' d) 
                           = Option.bind (applyOp a d) (\<lambda>d'. applyOp b d')"
  oops

fun transform :: "'char Action list \<Rightarrow> 'char Action list \<Rightarrow> (('char Action list) \<times> ('char Action list)) option"
where
  "transform [] [] = Some ([],[])"
| "transform (Insert(c)#as) b        = Option.map (\<lambda>(at,bt). (Insert(c)#at,Retain#bt)) (transform as b)"
| "transform a (Insert(c)#bs)        = Option.map (\<lambda>(at,bt). (Retain#at,Insert(c)#bt)) (transform a bs)"
| "transform (Retain#as) (Retain#bs) = Option.map (\<lambda>(at,bt). (Retain#at,Retain#bt)) (transform as bs)"
| "transform (Delete#as) (Delete#bs) = transform as bs"
| "transform (Retain#as) (Delete#bs) = Option.map (\<lambda>(at,bt). (at,addDeleteOp(bt))) (transform as bs)"
| "transform (Delete#as) (Retain#bs) = Option.map (\<lambda>(at,bt). (addDeleteOp(at),bt)) (transform as bs)"
| "transform _ _ = None"

lemma transform_inv: "\<forall> a b. Option.bind (transform a b) (\<lambda>(at,bt). compose a bt)
                           = Option.bind (transform a b) (\<lambda>(at,bt). compose b at)"
  oops

export_code applyOp addDeleteOp compose transform in Scala
  module_name Operation

end
