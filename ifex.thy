theory ifex imports Main
begin


(* Exercise 2.5.2 in https://isabelle.in.tum.de/doc/tutorial.pdf#subsection.2.5.6 *)

datatype boolex = Const bool | Var nat | Neg boolex | And boolex boolex

thm boolex.split

primrec valuex :: "boolex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "valuex (Const x) env = x" |
  "valuex (Var x) env = env x" |
  "valuex (Neg x) env = (\<not>(valuex x env))" | 
  "valuex (And x y) env = ((valuex x env) \<and> (valuex y env))"

primrec envx :: "nat \<Rightarrow> bool" where
  "envx 0 = False" |
  "envx (Suc n) = True"

datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex

primrec valif :: "ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "valif (CIF b) env = b" |
  "valif (VIF b) env = env b" | 
  "valif (IF b t e) env = (if valif b env then valif t env else valif e env)"


value "valif ((IF (VIF 0) (CIF False) (CIF True))) envx"

primrec bool2if :: "boolex \<Rightarrow> ifex" where
  "bool2if (Const x) = CIF x" |
  "bool2if (Var x) = VIF x" | 
  "bool2if (Neg x) = IF (bool2if x) (CIF False) (CIF True)" |
  "bool2if (And x y) = IF (bool2if x) (bool2if y) (CIF False)"


value "valif (bool2if (And (Var 1) (Const True))) envx"

lemma "valif (bool2if b) env = valuex b env"
  apply(induct b)
     apply(auto)
  done

primrec normif :: "ifex => ifex => ifex => ifex" where
"normif (CIF b) t e = IF (CIF b) t e" |
"normif (VIF x) t e = IF (VIF x) t e" |
"normif (IF b t e) u f = normif b (normif t u f) (normif e u f)"

primrec norm :: "ifex => ifex" where
"norm (CIF b) = CIF b" |
"norm (VIF x) = VIF x" |
"norm (IF b t e) = normif b (norm t) (norm e)"


lemma [simp]: "ALL t e. valif (normif b t e) env = valif (IF b t e) env"
  apply(induction b) 
    apply(auto)
  done

theorem "valif (norm b) env = valif b env"
  apply(induction b)
    apply(auto)
  done

end