theory examples
  imports Main
begin
declare [[names_short]]

(* datatype nat = null | Suc nat *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
"add 0 n = n" |
"add (Suc n) m = Suc (add n m)"

lemma add_02: "add m 0 = m" 
  apply(induction m)
  apply(auto)
  done

lemma add_Suc: "Suc (add m n) = add m (Suc n)"
  apply (induction m)
  apply (auto)
  done 

theorem add_comm: "add n m = add m n"
  apply (induction n)
  apply (auto simp add: add_02 add_Suc)
  done

datatype 'a list = Nil | Cons 'a "'a list"

fun conc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"conc Nil ys = ys" |
"conc (Cons x xs) ys = Cons x (conc xs ys)"

lemma conc_nil: "conc xs Nil = xs"
  apply(induction xs)
  apply (auto)
  done

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = conc (rev xs) (Cons x Nil)"

lemma rev_rev: "rev (rev xs) = xs"
  apply (induction xs)
  oops

end