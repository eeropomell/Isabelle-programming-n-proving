theory logic imports Main
begin

lemma neg_disj_to_conj:"\<not>(P \<or> Q) \<Longrightarrow> \<not>P \<and> \<not>Q"
  apply(rule conjI)
   apply(rule classical)
   apply(drule notnotD)
   apply(rotate_tac)
   apply(drule_tac Q="Q" in disjI1)
   apply(erule notE, assumption)
  apply(rule classical)
  apply(drule notnotD)
  apply(rotate_tac)
     apply(drule_tac P="P" in disjI2)
   apply(erule notE, assumption)
  done

lemma "\<not>P \<or> P"
proof (rule ccontr)
  assume not_disj: "\<not>(\<not>P \<or> P)"
  hence "\<not>\<not>P \<and> \<not>P" by (rule neg_disj_to_conj)
  hence "\<not>P \<and> P" by (simp) 
  thus False by simp
qed

lemma "\<not>(P \<or> Q) \<Longrightarrow> \<not>P \<and> \<not>Q"
  apply(rule conjI)
   apply(rule classical)
   apply(drule notnotD)
   apply(rotate_tac)
   apply(drule_tac Q="Q" in disjI1)
   apply(erule notE, assumption)
  apply(rule classical)
  apply(drule notnotD)
  apply(rotate_tac)
     apply(drule_tac P="P" in disjI2)
   apply(erule notE, assumption)
  done




lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
proof 
  assume h: "((P \<longrightarrow> Q) \<longrightarrow> P)"
  show "P"
  proof (rule ccontr)
    assume notP: "\<not>P"
    have pq: "P \<longrightarrow> Q"
    proof
      assume p: "P"
      from notP p have False ..
      from this show "Q" ..
    qed
    from notP h have "\<not>(P \<longrightarrow> Q)" by (auto)
    with pq show False by (auto)
  qed
qed
      
      

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<Longrightarrow> P"
  apply(rule classical)
  apply(frule_tac Q="P" and P="(P \<longrightarrow> Q)" in contrapos_nn)
   apply(erule mp, assumption) 
  apply(erule mp)
  apply(rule impI)
  apply(simp)
qed



lemma "(\<not> A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> A)"
proof (rule impI)
  assume notA_imp_B: "\<not> A \<longrightarrow> B"
  show "\<not> B \<longrightarrow> A"
  proof (rule impI)
    assume notB: "\<not> B"
    show "A"
    proof (rule classical)
      assume notA: "\<not> A"
      from notA_imp_B and notA have "B" by (rule mp)
      from this and notB show "A" by contradiction
    qed
  qed
qed


lemma "(\<not>A \<longrightarrow> B) \<Longrightarrow> (\<not>B \<longrightarrow> A)"
  apply(rule impI)  
  apply(rule classical)
  apply(drule mp)
   apply(auto)
  done
  


lemma nnA_imp_A: "\<not>\<not>A \<Longrightarrow> A"
  apply(rule classical)
  by (erule notE)

lemma "\<not>\<not>A \<longrightarrow> A"
proof 
  assume nnA: "\<not>\<not>A"
  show "A"
  proof (rule classical)
    assume nA: "\<not>A"
    from nnA nA show "A" by (rule notE)
  qed
qed

lemma "A \<Longrightarrow> \<not>\<not>A"
proof -
  assume a: "A"
  show "\<not>\<not>A"
  proof (rule notI)
    assume notA: "\<not>A"
    from notA a show False ..
  qed
qed

lemma "A \<Longrightarrow> \<not>\<not>A"
  apply(rule notI)
  by (erule notE)

thm cont



  



    

lemma "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
proof
  assume ab: "A \<longrightarrow> B"
  show "(B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C" 
  proof
    assume bc: "B \<longrightarrow> C"  
    show "A \<longrightarrow> C"  
    proof
      assume a: "A" 
      from ab a have b: "B" ..
      from bc b show c: "C" ..
    qed
  qed
qed


      


lemma "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
proof
  assume abc: "A \<longrightarrow> B \<longrightarrow> C"
  show "(A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
  proof
    assume ab: "A \<longrightarrow> B"
    show "A \<longrightarrow> C"
    proof
      assume a: "A"
      from ab a have b: "B" ..
      from abc a b show "C" by auto
    qed
  qed
qed





lemma "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
proof 
  assume impABC: "A \<longrightarrow> (B \<longrightarrow> C)"
  show "(A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
  proof
    assume ab: "A \<longrightarrow> B"
    show "A \<longrightarrow> C"
    proof
      assume a: "A"
      from ab and this have b: "B" by (rule mp)
      from impABC and a have "B \<longrightarrow> C" ..
      from this and b have "C" ..
      from this show "C" .
    qed
  qed
qed




lemma "(A \<or> A) = (A \<and> A)"
proof 
  assume "A \<and> A"
  from this have "A" by auto
  thus "A \<or> A" by auto
next
  assume "A \<or> A"
  then have "A \<and> A" by auto
  thus "A \<and> A" .
qed






  
lemma disjD_to_imp: "(\<not>P \<or> Q) \<Longrightarrow> (P \<longrightarrow> Q)"
  by blast

lemma "A \<longrightarrow> B \<longrightarrow> A"
proof
  assume a: "A"
  show "B \<longrightarrow> A"
  proof (rule disjD_to_imp)
    from a have "\<not>B \<or> A" ..
    from this show "\<not>B \<or> A" .
  qed
qed


    
    


lemma assumes h: "((P \<or> Q) \<or> R)"
  shows "P \<or> (Q \<or> R)"
proof -
  from h show ?thesis
  proof (rule disjE)
    assume pq: "P \<or> Q"
    from this show ?thesis by (rule disjE) (auto)
  next
    assume r: "R"
    from r show ?thesis by (auto)
  qed
qed

    
lemma assumes h: "((P \<or> Q) \<or> R)" 
  shows "P \<or> (Q \<or> R)"
proof -
  from h show ?thesis
  proof (rule disjE)
    assume pq: "P \<or> Q"
    from pq show ?thesis by (rule disjE) (auto)
  next
    assume r: "R"
    from r show ?thesis by auto
  qed
qed
    
  
  
  

lemma "(P \<and> Q) \<Longrightarrow> (P \<or> Q)"
proof 
  assume pq: "P \<and> Q"
  thus "P" ..
qed




lemma "P \<and> Q \<Longrightarrow> Q \<and> P"
proof -
  assume pq: "P \<and> Q"
  from pq show "Q \<and> P" by auto
qed


lemma "A \<Longrightarrow> A"
proof -
  assume A
  from this show "A" by (assumption)
qed

lemma "A \<Longrightarrow> A"
  by assumption

  

lemma assumes pq: "P \<or> Q" shows "Q \<or> P"
proof -
  assume "\<not>P"
  thm assms
  from pq show ?thesis
  proof
    assume P thus ?thesis..
  next
    assume Q thus ?thesis..
  qed
qed



lemma assumes pq: "P \<and> Q"
  shows "Q \<and> P" (is "?Q \<and> ?P")
proof -

qed



lemma "\<not>(P \<and> Q) \<longrightarrow> \<not>P \<or> \<not>Q"
proof
  assume h: "\<not>(P \<and> Q)"
  show "\<not>P \<or> \<not>Q"
  proof (rule ccontr)
    assume hh: "\<not>(\<not>P \<or> \<not>Q)"
    have "\<not>P"
    proof
      assume p: "P"
      have "\<not>Q"
      proof
        assume q: "Q"
        from p and q have "P \<and> Q" ..
        from h this show False by (rule notE)
      qed
      from this have "\<not>P \<or> \<not>Q" by (rule disjI2)
      with hh show False ..
    qed
    hence "\<not>P \<or> \<not>Q" ..
    with hh show False ..
  qed
qed

lemma "P \<and> Q \<Longrightarrow> Q \<and> P"
proof
  assume "P \<and> Q" from this show "Q" ..
next
  assume "P \<and> Q" thus "P" ..
qed

  


lemma "A \<longrightarrow> A"
proof(rule impI)
  assume a: "A"
  show "A" by (rule a)
qed

lemma "P \<and> Q \<longrightarrow> Q \<and> P"
proof
  assume P_n_Q: "P \<and> Q"
  thus "Q \<and> P"
  proof
    assume "Q" "P"
    thus ?thesis ..
  qed
qed

lemma "P \<and> Q \<longrightarrow> Q \<and> P"
proof
  assume pq: "P \<and> Q"
  from pq have p: "P" by (rule conjE)
  from pq have q: "Q" by (rule conjE)
  from q and p show "Q \<and> P" by (rule conjI)
qed

thm conjI




    


end
