theory star_iter imports Main
begin


(* Exercises from chapter 3 and 4 implement an inductive datatype 'star', for reflexive transitive closures 
  
*)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

(* iter r n x y IFF there are x_0, ... , x_n such that x = x_0, x_n = y and r x_i x_{i+1} for all i < n *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  iter0: "r x x \<Longrightarrow> iter r 0 x x" |
  iterN: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n + 1) x z"


lemma "iter r n x y \<Longrightarrow> star r x y"
proof(induction rule: iter.induct)
  case (iter0 x)  
  show ?case by (rule refl)
next
  case (iterN x y)
  thus ?case by (auto intro: star.step)
qed

(* alternative way of defining reflexive transitive closure *)
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl': "star' r x x" |
  step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_trans: "star r a b \<Longrightarrow> star r b c \<Longrightarrow> star r a c"
  apply(induction rule: star.induct)
   apply assumption
  apply(metis step)
  done


lemma star_step_symm [intro]: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(rule step)
    apply(auto)
   apply(rule refl)
  apply(rule step)
   apply(auto)
  done

lemma star'_step'_symm [intro]: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
    apply(rule step')
     apply(auto)
    apply(rule refl')
  apply(rule step')
   apply(auto)
  done

lemma "star' r x y = star r x y"
  apply(rule)
  apply(induction rule: star'.induct)
    apply(rule refl)
   apply(auto)
  apply(induction rule: star.induct)
   apply(rule refl')
  apply(auto)
  done


lemma star_to_iter: " (\<forall>x. r x x) \<Longrightarrow> star r x y \<Longrightarrow> \<exists>n. iter r n x y"
proof -
  assume hx: "\<forall>x. r x x"
  assume hstar: "star r x y"
  then show ?thesis
  proof (induct rule: star.induct)
    case refl
    then show ?case using hx iter0 by blast
  next
    case (step x y z)
    then show ?case
    proof -
      obtain n where hn: "iter r n y z" using step.hyps(3) by blast
      have "iter r (n + 1) x z"
        using hn step.hyps(1) iterN by blast
      then show ?thesis by auto
    qed
  qed
qed


end