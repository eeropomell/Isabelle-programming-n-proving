theory cantor imports Main
begin

(* 4 versions of the Cantor theorem;
  Chapter 7 of How To Prove It handles Cantor theorem (set cardinalites in general)
*)
  

lemma "¬surj(f :: 'a ⇒ 'a set)"
proof
  assume 0: "surj f"
  from `surj f` have 1: "∀A. ∃a. A = f a" by (simp add:surj_def)
  hence "∃a. {x. x ∉ f x} = f a" by blast
  thus False by blast
qed

lemma "¬surj(f :: 'a ⇒ 'a set)"
proof
  assume "surj f"
  hence "∃a. {x. x ∉ f x} = f a" by blast
  thus False by blast
qed

lemma
  fixes f:: "'a ⇒ 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "∃a. {x. x ∉ f x} = f a" using s
    by blast
  thus ?thesis by blast
qed

lemma "¬surj(f :: 'a ⇒ 'a set)"
proof
  assume "surj f"
  hence "∃a. {x. x ∉ f x} = f a" by blast
  then obtain a where "{x. x ∉ f x} = f a" by blast
  hence "a ∈ f a ⟷ a ∉ f a" by blast
  thus False by blast
qed

end