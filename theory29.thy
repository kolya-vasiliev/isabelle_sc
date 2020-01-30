theory theory29 imports Main begin

declare [[names_short]]

(* 3.1 *)

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N a) s = a" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N a) = N a" |
"asimp_const (V x) = V x" |
"asimp_const (Plus p q) = 
 (case (asimp_const p, asimp_const q) of 
  (N a, N b) \<Rightarrow> N (a+b) |
  (x, y) \<Rightarrow> Plus x y)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N a) (N b) = N (a+b)" |
"plus p (N i) = (if i = 0 then p else Plus p (N i))" |
"plus (N i) p = (if i = 0 then p else Plus (N i) p)" |
"plus p q = (Plus p q)"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N a) = N a" |
"asimp (V x) = V x" |
"asimp (Plus p q) = plus (asimp p) (asimp q)"

lemma plus_correct: "aval (plus e1 e2) s = aval e1 s + aval e2 s"
  apply(induction rule:plus.induct)
  apply(auto)
  done

theorem asimp_correct: "aval (asimp e) s = aval e s"
  apply (induction e)
  apply (auto simp add: plus_correct)
  done  

(* 3.2 *)

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And a b) s = (bval a s \<and> bval b s)" |
"bval (Less a b) s = (aval a s < aval b s)"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n) (N m) = Bc(n < m)" |
"less a b = Less a b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and a b = And a b"

lemma and_0: "bval (and a1 a2) s = (bval a1 s \<and> bval a2 s)"
  apply (induction rule: and.induct)
  apply (auto)
  done

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not(bsimp b)" |
"bsimp (And a b) = and (bsimp a) (bsimp b)" |
"bsimp (Less a b) = less (asimp a) (asimp b)"

(* 3.3  *)

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = n # stk" |
"exec1 (LOAD x) s stk = s(x) # stk" |
"exec1 ADD _ (x # y # stk) = (x+y) # stk"  

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)" 

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma exec_append: "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
apply (induction is1 arbitrary:stk)
apply (auto)
done

lemma "exec (comp a) s stk = aval a s # stk"
apply (induction a arbitrary:stk)
apply (auto  simp add: exec_append)
done

