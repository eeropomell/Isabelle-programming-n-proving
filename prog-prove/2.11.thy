


theory pol imports Main
begin



datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var x = x" |
  "eval (Const a) x = a" |
  "eval (Add a b) x = eval a x + eval b x" |
  "eval (Mult a b) x = eval a x * eval b x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] x = 0" |
  "evalp (a#as) x = a + x * evalp as x"

fun addcoef :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "addcoef xs [] = xs" |
  "addcoef [] xs = xs" |
  "addcoef (x#xs) (y#ys) = (x + y) # addcoef xs ys"

fun scalar_mult :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"scalar_mult k [] = []" |
"scalar_mult k (x # xs) = k * x # scalar_mult k xs"


fun multcoef :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "multcoef [] _ = []" |
  "multcoef (x#xs) ys = addcoef (scalar_mult x ys) (0 # multcoef xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0,1]" |
  "coeffs (Const n) = [n]" |
  "coeffs (Add e1 e2) = addcoef (coeffs e1) (coeffs e2)" |
  "coeffs (Mult e1 e2) = multcoef (coeffs e1) (coeffs e2)"


(* for addcoef_evalp *)
lemma [simp]: "addcoef [] xs = xs"
  apply(induction xs)
   apply(auto)
  done

lemma addcoef_evalp[simp]: "\<forall> x. evalp (addcoef xs ys) x = evalp xs x + evalp ys x"
  apply(induction xs rule: addcoef.induct)
    apply(simp_all add: algebra_simps)
  done

lemma mult_preservescalar[simp]: "evalp (scalar_mult x xs) y = x * evalp xs y"
  apply(induction xs)
   apply(auto simp add: Int.int_distrib)
  done

lemma multcoef_evalp[simp]: "ALL x ys. evalp (multcoef xs ys) x = evalp xs x * evalp ys x"
  apply(induction xs)
   apply(auto simp add: Int.int_distrib) 
  done

theorem "\<forall> x. evalp (coeffs e) x = eval e x"
  apply(induction e)
     apply(auto)
  done
  


end