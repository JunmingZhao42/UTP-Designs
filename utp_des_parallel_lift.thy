section \<open> Design Parallel with a Lifted State Merge \<close>

theory utp_des_parallel_lift
  imports utp_des_parallel_laws
begin

text \<open> Lifting a state merge to designs, and the design parallel operator. \<close>

subsection \<open> Lifting a State Merge \<close>

subsubsection \<open> Construction \<close>

text \<open> The raw lift applies the state merge and sets the output flag to the conjunction
  of the branch flags. \<close>

(* merge_des_raw j ((ok,s), (okL,sL), (okR,sR), (ok',s')) =
     (ok' = (okL \<and> okR)) \<and> j(s, sL, sR, s') *)
definition merge_des_raw :: "'s merge \<Rightarrow> 's des_merge" where
"merge_des_raw j \<equiv> (\<lambda>(m, z).
  des_vars.ok\<^sub>v z =
    (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
  merge_eval j (des_vars.more (mrg_prior\<^sub>v m))
    (des_vars.more (mrg_left\<^sub>v m))
    (des_vars.more (mrg_right\<^sub>v m))
    (des_vars.more z))"

text \<open> Design skip releases the final observation after divergence, but a merged state
  must still exist. \<close>

definition merge_des :: "'s merge \<Rightarrow> 's des_merge" ("M\<^sub>D") where
"merge_des j \<equiv> H3m (HDm (merge_des_raw j))"

text \<open> @{const skip_d} absorbs the $H2m$ part of $HDm$, since $J ;; II_D = II_D$. \<close>

lemma merge_des_alt_def: "merge_des j = H1m (merge_des_raw j) ;; II\<^sub>D"
  by (simp only: merge_des_def H3m_def HDm_def comp_apply H1m_H2m_commute')
     (simp add: H2m_def seqr_assoc skip_d_absorb_J_2)

subsubsection \<open> Evaluation \<close>

text \<open> Unfolding the merge: termination of both branches requires termination and the
  state merge; otherwise only some merged state must exist. \<close>

(* merge_des j ((ok,s), (okL,sL), (okR,sR), (ok',s')) =
     \<not>ok \<or> (((okL \<and> okR) \<longrightarrow> (ok' \<and> j(s, sL, sR, s'))) \<and>
            (\<exists>y. j(s, sL, sR, y))) *)
lemma merge_des_expand:
  "merge_eval (merge_des j) \<lparr>ok\<^sub>v = ok0, \<dots> = s\<rparr>
    \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
    \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr> \<longleftrightarrow>
    (\<not> ok0 \<or>
      ((okL \<and> okR \<longrightarrow> (ok' \<and> merge_eval j s sL sR s')) \<and> (\<exists>y. merge_eval j s sL sR y)))"
  by (simp add: merge_des_alt_def H1m_def merge_des_raw_def skip_d_def rdesign_def design_def;
      pred_auto; blast)

lemma HDm_merge_des_raw_eval:
  "merge_eval (HDm (merge_des_raw j)) x p q z \<longleftrightarrow>
    \<not> ok\<^sub>v x \<or> (((ok\<^sub>v p \<and> ok\<^sub>v q) \<longrightarrow> ok\<^sub>v z) \<and>
      merge_eval j (des_vars.more x) (des_vars.more p) (des_vars.more q) (des_vars.more z))"
  by (simp add: HDm_def H1m_def H2m_def merge_des_raw_def J_def; pred_auto)

lemma merge_des_ok_eval:
  assumes "ok\<^sub>v x \<longrightarrow> ok\<^sub>v p \<and> ok\<^sub>v q"
  shows "merge_eval (merge_des j) x p q z \<longleftrightarrow> merge_eval (HDm (merge_des_raw j)) x p q z"
  using assms
  by (cases x; cases p; cases q; cases z;
      simp add: merge_des_expand HDm_merge_des_raw_eval; blast)

subsubsection \<open> Healthiness, Symmetry and Associativity \<close>

lemma merge_des_is_HDm [closure]: "M\<^sub>D(j) is HDm"
  unfolding merge_des_alt_def
  by (rule HDm_seq[OF _ N_implies_H[OF skip_d_is_H1_H3]]; simp add: Healthy_def' H1m_Idempotent[unfolded Idempotent_def])

lemma merge_des_is_H1m [closure]: "merge_des j is H1m"
  by (rule HDm_healths(1)[OF merge_des_is_HDm])

lemma merge_des_is_H2m [closure]: "merge_des j is H2m"
  by (rule HDm_healths(2)[OF merge_des_is_HDm])

lemma merge_des_is_H3m [closure]: "merge_des j is H3m"
  by (simp add: Healthy_def' merge_des_def H3m_Idempotent[unfolded Idempotent_def])

lemma merge_des_raw_SymMerge:
  assumes "j is SymMerge"
  shows "merge_des_raw j is SymMerge"
  using assms by (simp add: Healthy_def' merge_des_raw_def fun_eq_iff; pred_auto; blast)

lemma merge_des_SymMerge [closure]:
  assumes "j is SymMerge"
  shows "M\<^sub>D(j) is SymMerge"
  using SymMerge_HDm[OF merge_des_raw_SymMerge[OF assms]]
  by (simp add: merge_des_def H3m_def Healthy_def' seqr_assoc[symmetric])

lemma HDm_merge_des_raw_AssocMerge:
  assumes "AssocMerge j"
  shows "AssocMerge (HDm (merge_des_raw j))"
proof -
  have ex_des: "(\<exists>u. F u) = (\<exists>b s. F \<lparr>ok\<^sub>v = b, \<dots> = s\<rparr>)" for F :: "'a des_vars_ext \<Rightarrow> bool"
    by (metis (full_types) des_vars.surjective)
  show ?thesis
    using assms unfolding AssocMerge_iff
    by (simp add: ex_des HDm_merge_des_raw_eval ex_bool_eq; blast)
qed

text \<open> With a mergeable state merge, the completed merge is associative on all branches. \<close>

lemma merge_des_AssocMerge:
  fixes j :: "'s merge"
  assumes am: "AssocMerge j" and mergeable: "mergeable j"
  shows "AssocMerge (merge_des j)"
proof -
  have ex_des: "(\<exists>x. F x) = (\<exists>b s. F \<lparr>ok\<^sub>v = b, \<dots> = s\<rparr>)"
    for F :: "'s des_vars_ext \<Rightarrow> bool"
    by pred_auto
  show ?thesis
    unfolding AssocMerge_iff
  proof (intro allI)
    fix x p q r z :: "'s des_vars_ext"
    show "(\<exists>u. merge_eval (merge_des j) x p q u \<and> merge_eval (merge_des j) x u r z) =
      (\<exists>u. merge_eval (merge_des j) x q r u \<and> merge_eval (merge_des j) x u p z)"
      by (cases x; cases p; cases q; cases r; cases z;
          rename_tac b s0 a u d v e w c s;
          simp only: ex_des merge_des_expand mergeable HOL.simp_thms;
          case_tac b; case_tac a; case_tac d; case_tac e;
          simp add: ex_bool_eq all_bool_eq mergeable conj_left_commute;
          use am[unfolded AssocMerge_iff] in blast)
  qed
qed

subsection \<open> Design Parallel \<close>

subsubsection \<open> Definition and Evaluation \<close>

abbreviation des_par ::
  "'s des_hrel \<Rightarrow> 's merge \<Rightarrow> 's des_hrel \<Rightarrow> 's des_hrel"
  ("_ \<parallel>\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q \<equiv> P \<parallel>\<^bsub>M\<^sub>D(j)\<^esub> Q"

(* (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q)((ok,s), (ok',s')) =
     \<exists>okL sL okR sR. P((ok,s), (okL,sL)) \<and> Q((ok,s), (okR,sR)) \<and>
       (\<not>ok \<or> (((okL \<and> okR) \<longrightarrow> (ok' \<and> j(s, sL, sR, s'))) \<and>
                 (\<exists>y. j(s, sL, sR, y)))) *)
lemma des_par_expand:
  fixes P Q :: "'s des_hrel"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) (\<lparr>ok\<^sub>v = ok0, \<dots> = s\<rparr>, \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>) \<longleftrightarrow>
   (\<exists>okL sL okR sR. P (\<lparr>ok\<^sub>v = ok0, \<dots> = s\<rparr>, \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>) \<and> Q (\<lparr>ok\<^sub>v = ok0, \<dots> = s\<rparr>, \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>) \<and>
    (\<not> ok0 \<or>
      ((okL \<and> okR \<longrightarrow> (ok' \<and> merge_eval j s sL sR s')) \<and> (\<exists>y. merge_eval j s sL sR y))))"
proof -
  have expand_result:
    "(\<exists>p :: 's des_vars_ext. F p) \<longleftrightarrow>
      (\<exists>b x. F \<lparr>ok\<^sub>v = b, \<dots> = x\<rparr>)" for F
    by pred_auto
  show ?thesis
    by (simp only: par_by_merge_eval expand_result merge_des_expand)
qed

subsubsection \<open> Healthiness Closure \<close>

lemma des_par_H_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) is \<^bold>H"
  by (rule H_par_by_merge[OF assms merge_des_is_HDm])

lemma des_par_H3_closure [closure]:
  "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) is H3"
  by (rule H3_par_by_merge[OF merge_des_is_H3m])

lemma des_par_N_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) is \<^bold>N"
  by (simp add: Healthy_def' Healthy_if[OF des_par_H3_closure]
      Healthy_if[OF H1_par_by_merge[OF assms merge_des_is_H1m]])

subsubsection \<open> Zero Laws \<close>

lemma des_par_chaos_chaos:
  fixes j :: "'s merge"
  assumes "\<And>s. \<exists>sL sR s'. merge_eval j s sL sR s'"
  shows "(\<bottom>\<^sub>D \<parallel>\<^sub>D\<^bsub>j\<^esub> \<bottom>\<^sub>D) = \<bottom>\<^sub>D"
  by (rule ext; case_tac x; rename_tac s t; case_tac s; case_tac t;
      simp add: des_par_expand bot_d_true true_pred_def ex_bool_eq assms)

lemma des_par_chaos:
  fixes P :: "'s des_hrel"
  assumes "P is H4" and mergeable: "mergeable j"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> \<bottom>\<^sub>D) = \<bottom>\<^sub>D"
        "(\<bottom>\<^sub>D \<parallel>\<^sub>D\<^bsub>j\<^esub> P) = \<bottom>\<^sub>D"
proof -
  have div: "merge_eval (merge_des j) x p q z"
    if "\<not> ok\<^sub>v p \<or> \<not> ok\<^sub>v q" for x p q z
    using that mergeable by (cases x; cases p; cases q; cases z; simp add: merge_des_expand; blast)
  show "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> \<bottom>\<^sub>D) = \<bottom>\<^sub>D"
    by (rule par_by_merge_chaos(1)[where M="merge_des j", OF assms(1) div])
  show "(\<bottom>\<^sub>D \<parallel>\<^sub>D\<^bsub>j\<^esub> P) = \<bottom>\<^sub>D"
    by (rule par_by_merge_chaos(2)[where M="merge_des j", OF assms(1) div])
qed

lemma des_par_miracle:
  assumes "P is H1"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> \<top>\<^sub>D) = \<top>\<^sub>D" 
        "(\<top>\<^sub>D \<parallel>\<^sub>D\<^bsub>j\<^esub> P) = \<top>\<^sub>D"
  by (rule par_by_merge_miracle[OF assms merge_des_is_H1m])+

subsubsection \<open> Commutativity \<close>

lemma des_par_comm:
  assumes "j is SymMerge"
  shows "P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>D\<^bsub>j\<^esub> P"
  by (rule par_by_merge_comm[OF merge_des_SymMerge[OF assms]])

subsubsection \<open> Associativity \<close>

lemma des_par_assoc:
  fixes P Q R :: "'s des_hrel" and j :: "'s merge"
  assumes sym: "j is SymMerge" and am: "AssocMerge j" and mergeable: "mergeable j"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>D\<^bsub>j\<^esub> R)"
  by (rule par_by_merge_assoc[OF merge_des_SymMerge[OF sym] merge_des_AssocMerge[OF am mergeable]])

end
