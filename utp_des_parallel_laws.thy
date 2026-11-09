section \<open> Design Parallel-by-Merge Laws \<close>

theory utp_des_parallel_laws
  imports utp_des_healths
begin

text \<open> Design merge healthiness and parallel-by-merge laws for any design merge. \<close>

type_synonym 's des_merge = "'s des_vars_ext merge"

subsection \<open> Design Merge Healthiness \<close>

text \<open> These merge conditions preserve design healthiness under parallel by merge.
  The prior, branch and output alphabets may differ, as needed for angelic designs. \<close>

subsubsection \<open> Definitions \<close>

(* H1m M((ok,s),p,q,z) = \<not>ok \<or> M((ok,s),p,q,z) *)
definition H1m where [pred]: "H1m M = (M \<or> (\<not> $<:ok\<^sup><)\<^sub>e)"

definition H2m where [pred]: "H2m M = M ;; J"

definition H3m where [pred]: "H3m M \<equiv> M ;; II\<^sub>D"

definition HDm where [pred]: "HDm \<equiv> H1m \<circ> H2m"

subsubsection \<open> Idempotence and Monotonicity \<close>

lemma H1m_H2m_commute:
  "(H1m \<circ> H2m) M = (H2m \<circ> H1m) M"
  by (simp add: comp_def; pred_auto)

lemmas H1m_H2m_commute' = H1m_H2m_commute[simplified comp_apply]

lemma H1m_Idempotent [closure]: "Idempotent H1m"
  by (rule IdempotentI, pred_auto)

lemma H2m_Idempotent [closure]: "Idempotent H2m"
  by (rule IdempotentI, simp add: H2m_def seqr_assoc J_idem)

lemma H3m_Idempotent [closure]: "Idempotent H3m"
  by (rule IdempotentI, simp add: H3m_def seqr_assoc)

lemma HDm_Idempotent [closure]: "Idempotent HDm"
  unfolding HDm_def
  by (rule Idempotent_comp[OF H1m_Idempotent H2m_Idempotent], rule ext, rule H1m_H2m_commute)

lemma H1m_Monotonic [closure]: "Monotonic H1m"
  by (rule MonotonicI, pred_auto)

lemma H2m_Monotonic [closure]: "Monotonic H2m"
  by (rule MonotonicI, simp add: H2m_def seqr_mono)

lemma H3m_Monotonic [closure]: "Monotonic H3m"
  by (rule MonotonicI, simp add: H3m_def seqr_mono)

lemma HDm_Monotonic [closure]: "Monotonic HDm"
  unfolding HDm_def
  by (rule monoI, simp add: monoD[OF H1m_Monotonic] monoD[OF H2m_Monotonic])

lemma HDm_fixed_iff:
  "M is HDm \<longleftrightarrow> (M is H1m) \<and> (M is H2m)"
  using H1m_Idempotent[unfolded Idempotent_def, rule_format, of "H2m M"] H1m_H2m_commute'[of "H2m M"]
  by (auto simp add: Healthy_def' HDm_def H2m_Idempotent[unfolded Idempotent_def])

lemma HDm_healths [closure]:
  assumes "M is HDm"
  shows "M is H1m" "M is H2m"
  using assms by (simp_all add: HDm_fixed_iff)

lemma HDm_intro:
  assumes "M is H1m" "M is H2m"
  shows "M is HDm"
  by (simp add: HDm_fixed_iff assms)

subsubsection \<open> Commutation \<close>

lemma H1m_H3m_commute:
  "H1m (H3m M) = H3m (H1m M)"
  by (simp add: H1m_def H3m_def; pred_auto; blast)

lemma H2m_H3m_commute:
  "H2m (H3m M) = H3m (H2m M)"
  by (simp add: H2m_def H3m_def seqr_assoc skip_d_absorb_J_1 skip_d_absorb_J_2)

lemma H1m_HDm_commute:
  "H1m (HDm M) = HDm (H1m M)"
  by (simp add: HDm_def H1m_H2m_commute' H1m_Idempotent[unfolded Idempotent_def])
lemma H2m_HDm_commute:
  "H2m (HDm M) = HDm (H2m M)"
  by (simp add: HDm_def H1m_H2m_commute' H2m_Idempotent[unfolded Idempotent_def])
lemma H3m_HDm_commute:
  "H3m (HDm M) = HDm (H3m M)"
  by (simp add: HDm_def H1m_H3m_commute H2m_H3m_commute)

subsubsection \<open> Disjunction and Conjunction \<close>

lemma H1m_disj: "H1m(M \<or> N) = (H1m M \<or> H1m N)"
  by pred_auto

lemma H1m_conj: "H1m(M \<and> N) = (H1m M \<and> H1m N)"
  by pred_auto

lemma H2m_disj: "H2m(M \<or> N) = (H2m M \<or> H2m N)"
  by (simp add: H2m_def seqr_or_distl)

lemma HDm_disj: "HDm(M \<or> N) = (HDm M \<or> HDm N)"
  by (simp add: HDm_def H1m_disj H2m_disj)

text \<open> H2m and HDm distribute over conjunction for H2m-healthy operands. \<close>

lemma H2m_conj:
  assumes "M is H2m" "N is H2m"
  shows "H2m(M \<and> N) = (H2m M \<and> H2m N)"
proof -
  have "H2m(H2m M \<and> H2m N) = (H2m M \<and> H2m N)"
    by (simp add: H2m_def J_split usubst; pred_auto)
  then show ?thesis
    by (simp only: Healthy_if[OF assms(1)] Healthy_if[OF assms(2)])
qed

lemma HDm_conj:
  assumes "M is H2m" "N is H2m"
  shows "HDm(M \<and> N) = (HDm M \<and> HDm N)"
  by (simp add: HDm_def H2m_conj assms H1m_conj)

lemma H1m_disj_closed [closure]:
  assumes "M is H1m" "N is H1m"
  shows "(M \<or> N) is H1m"
  by (rule Healthy_intro; simp add: H1m_disj Healthy_if assms)

lemma H1m_conj_closed [closure]:
  assumes "M is H1m" "N is H1m"
  shows "(M \<and> N) is H1m"
  by (rule Healthy_intro; simp add: H1m_conj Healthy_if assms)

lemma H2m_disj_closed [closure]:
  assumes "M is H2m" "N is H2m"
  shows "(M \<or> N) is H2m"
  by (rule Healthy_intro; simp add: H2m_disj Healthy_if assms)

lemma H2m_conj_closed [closure]:
  assumes "M is H2m" "N is H2m"
  shows "(M \<and> N) is H2m"
  by (rule Healthy_intro; simp add: H2m_conj Healthy_if assms)

lemma HDm_disj_closed [closure]:
  assumes "M is HDm" "N is HDm"
  shows "(M \<or> N) is HDm"
  by (rule Healthy_intro; simp add: HDm_disj Healthy_if assms)

lemma HDm_conj_closed [closure]:
  assumes "M is HDm" "N is HDm"
  shows "(M \<and> N) is HDm"
  by (rule HDm_intro; simp add: assms closure)

subsubsection \<open> Symmetry \<close>

lemma SymMerge_H1m [closure]:
  assumes "M is SymMerge"
  shows "H1m M is SymMerge"
  using assms by (pred_simp; blast)

lemma SymMerge_H2m [closure]:
  assumes "M is SymMerge"
  shows "H2m M is SymMerge"
  using assms by (simp add: Healthy_def' H2m_def seqr_assoc[symmetric])

lemma SymMerge_HDm [closure]:
  assumes "M is SymMerge"
  shows "HDm M is SymMerge"
  by (simp add: HDm_def assms closure)

subsubsection \<open> Sequential Composition \<close>

lemma H1m_seq [closure]:
  assumes "M is H1m" "P is H1"
  shows "M ;; P is H1m"
  using assms by (pred_simp; blast)

lemma H2m_seq [closure]:
  assumes "P is H2"
  shows "M ;; P is H2m"
  using assms by (simp add: Healthy_def' H2m_def H2_def seqr_assoc)

lemma HDm_seq [closure]:
  assumes "M is H1m" "P is \<^bold>H"
  shows "M ;; P is HDm"
  by (rule HDm_intro;
      simp add: assms closure H_implies_H1 H_implies_H2)

text \<open> An $H3m$-healthy merge that permits some divergent output permits every output. \<close>

lemma H3m_diverge:
  assumes "M is H3m" "merge_eval M x p q \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>"
  shows "merge_eval M x p q z"
  using assms(2)
  apply (subst Healthy_if[OF assms(1), symmetric])
  apply (subst (asm) Healthy_if[OF assms(1), symmetric])
  by (simp add: H3m_def skip_d_def rdesign_def design_def; pred_auto)

subsection \<open> Generic Design Parallel Laws \<close>

subsubsection \<open> Healthiness Closure \<close>

text \<open> The closure rules allow the operands to have different output alphabets. \<close>

lemma H1_par_by_merge [closure]:
  assumes "P is H1" "Q is H1" "M is H1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H1"
  using assms by (pred_simp; auto simp add: all_bool_eq ex_bool_eq)

lemma H2_par_by_merge [closure]:
  assumes "M is H2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H2"
  using assms
  by (simp add: Healthy_def' H2_def H2m_def par_by_merge_def seqr_assoc)

lemma H3_par_by_merge [closure]:
  assumes "M is H3m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H3"
  using assms
  by (simp add: Healthy_def' H3_def H3m_def par_by_merge_seq_add)

lemma H_par_by_merge [closure]:
  assumes "P is H1" "Q is H1" "M is HDm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is \<^bold>H"
  by (rule Healthy_intro;
      simp add: Healthy_if H1_par_by_merge H2_par_by_merge
        HDm_healths assms)

subsubsection \<open> Miracle and Chaos \<close>

lemma par_by_merge_miracle:
  assumes "P is H1" "M is H1m"
  shows "P \<parallel>\<^bsub>M\<^esub> \<top>\<^sub>D = \<top>\<^sub>D"
        "\<top>\<^sub>D \<parallel>\<^bsub>M\<^esub> P = \<top>\<^sub>D"
  using assms
  by (simp add: Healthy_def' H1_def H1m_def top_d_not_ok par_by_merge_eval;
      pred_auto; blast)+

text \<open> When a divergent branch lets the merge give any output,
  P \<parallel> Chaos = Chaos. \<close>

lemma par_by_merge_chaos:
  assumes "P is H4"
    and div: "\<And>x p q z. \<not> ok\<^sub>v p \<or> \<not> ok\<^sub>v q \<Longrightarrow> merge_eval M x p q z"
  shows "P \<parallel>\<^bsub>M\<^esub> \<bottom>\<^sub>D = \<bottom>\<^sub>D"
        "\<bottom>\<^sub>D \<parallel>\<^bsub>M\<^esub> P = \<bottom>\<^sub>D"
proof -
  have feasible: "\<exists>p. P (x, p)" for x
    using fun_cong[OF is_H4_alt_def[THEN iffD1, OF assms(1)], of "(x, x)"]
    by (simp add: seq_def true_pred_def)
  have q: "\<not> ok\<^sub>v \<lparr>ok\<^sub>v = False, \<dots> = undefined\<rparr>"
    by simp
  show "P \<parallel>\<^bsub>M\<^esub> \<bottom>\<^sub>D = \<bottom>\<^sub>D" "\<bottom>\<^sub>D \<parallel>\<^bsub>M\<^esub> P = \<bottom>\<^sub>D"
    by (rule ext, clarify; simp add: par_by_merge_eval bot_d_true true_pred_def;
        use feasible div q in blast)+
qed

end
