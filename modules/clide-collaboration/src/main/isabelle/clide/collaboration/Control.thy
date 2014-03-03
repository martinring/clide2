theory Control
imports Main SimpleOperation
begin

datatype 'char message = Edit nat nat "'char operation"

datatype 'char client = Synchronized nat nat "'char operation list"
                      | Pending nat nat "'char operation list" "'char operation"
                      | Buffering nat nat "'char operation list" "'char operation" "'char operation"

fun cid :: "'char client \<Rightarrow> nat" where
  "cid (Synchronized c _ _) = c"
| "cid (Pending c _ _ _) = c"
| "cid (Buffering c _ _ _ _) = c"

fun crev :: "'char client \<Rightarrow> nat" where
  "crev (Synchronized _ r _) = r"
| "crev (Pending _ r _ _) = r"
| "crev (Buffering _ r _ _ _) = r"

datatype 'char server = Server nat "'char operation list" "('char operation \<times> nat) list"

datatype 'char system = System "'char server" "'char client set"

inductive_set states :: "'char system set" where 
         "System (Server 0 [] []) {} \<in> states"
| join:  "System (Server r h inbox) clients \<in> states \<Longrightarrow> (\<nexists>x. x \<in> clients \<and> cid c = ncid) \<Longrightarrow> System (Server r h inbox) (insert (Synchronized ncid r h) clients) \<in> states"


end
