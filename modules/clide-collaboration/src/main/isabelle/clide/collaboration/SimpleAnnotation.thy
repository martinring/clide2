(* Formalization of Annotations in clide *)
(* author: Martin Ring, DFKI Bremen *) (*<*)

theory SimpleAnnotation
imports SimpleOperation Main
begin (*>*)

section {* Annotation and Annotations *}

text {* An @{term annotation} is either @{term Plain}, meaning that it does not annotate the current
        document position. Or @{term Annotate}, which annotates the current position with a set of 
        annotations *}

datatype 'a annotation = Plain | Annotate "'a set"

type_synonym 'a annotations = "'a annotation list"

text {* the length of the document an annotation annotates is equal to the length of the annotation *}

definition "docLength = length"

inductive_set application :: "(('a annotations \<times> ('char \<times> 'a set) document) \<times> ('char \<times> 'a set) document) set" where
  empty[intro!]:    "(([],[]),[]) \<in> application"
| plain[intro!]:    "((a,d),d') \<in> application \<Longrightarrow> ((Plain#a,x#d),x#d') \<in> application"
| annotate[intro!]: "((a,d),d') \<in> application \<Longrightarrow> (((Annotate as')#a,(c,as)#d),(c,as \<union> as')#d') \<in> application"

fun transform :: "'a annotations \<Rightarrow> 'char operation \<Rightarrow> 'a annotations option" where
  "transform ([])         ([])            = Some []"
| "transform (head#tail)  (Retain#next)   = Option.map (\<lambda>a. head#a) (transform tail next)"
| "transform (head#tail)  (Insert _#next) = Option.map (\<lambda>a. head#a) (transform (head#tail) next)"
| "transform (_#tail)     (Delete#next)   = transform tail next"
| "transform _            _               = None"

end
