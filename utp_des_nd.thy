section \<open> Non-Divergent Designs \<close>

theory utp_des_nd
  imports utp_des_parallel_lift
begin

text \<open> We want design parallel to be associative without a mergeability premise.
  This holds for non-divergent designs: ok \<longrightarrow> ok'. \<close>

subsection \<open> Non-Divergent Designs \<close>

(* NDD P = P \<and> (ok \<longrightarrow> ok'). *)
definition NDD :: "('\<alpha>, '\<beta>) des_rel \<Rightarrow> ('\<alpha>, '\<beta>) des_rel" where
[pred]: "NDD P \<equiv> P \<squnion> (true \<turnstile> true)"

lemma NDD_healthy_iff:
  "P is NDD \<longleftrightarrow> pre\<^sub>D P = true"
  apply (subst preD_true_iff)
  unfolding Healthy_def' NDD_def conj_pred_def design_def
  by pred_auto

subsection \<open> Non-Divergent Merges \<close>

text \<open> $NDDm$ requires a started merge of terminating branches to terminate. \<close>

definition NDDm :: "'s des_merge \<Rightarrow> 's des_merge" where
  "NDDm M \<equiv> (\<lambda>(m,z). M (m,z) \<and>
    (des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and>
      des_vars.ok\<^sub>v (mrg_right\<^sub>v m) \<longrightarrow> des_vars.ok\<^sub>v z))"

(* NDDm M ((ok,s),(okL,sL),(okR,sR),(ok',s')) =
     M (...) \<and> (ok \<and> okL \<and> okR \<longrightarrow> ok') *)
lemma NDDm_eval:
  "merge_eval (NDDm M) x p q z =
    (merge_eval M x p q z \<and> (ok\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q \<longrightarrow> ok\<^sub>v z))"
  by (simp add: NDDm_def)

lemma NDDm_Idempotent [closure]: "Idempotent NDDm"
  by (rule IdempotentI, simp add: NDDm_def fun_eq_iff)

lemma NDDm_Monotonic [closure]: "Monotonic NDDm"
  by (auto simp: mono_def NDDm_def pred_refine_iff)

lemma NDDm_healthy_iff:
  "M is NDDm \<longleftrightarrow>
    (\<forall>x p q z. merge_eval M x p q z \<longrightarrow> ok\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q \<longrightarrow> ok\<^sub>v z)"
proof
  assume h: "M is NDDm"
  show "\<forall>x p q z. merge_eval M x p q z \<longrightarrow> ok\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q \<longrightarrow> ok\<^sub>v z"
  proof (intro allI impI)
    fix x p q z
    assume "merge_eval M x p q z" "ok\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q"
    then show "ok\<^sub>v z"
      using NDDm_eval[of M x p q z] Healthy_if[OF h] by simp
  qed
next
  assume a: "\<forall>x p q z. merge_eval M x p q z \<longrightarrow> ok\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q \<longrightarrow> ok\<^sub>v z"
  show "M is NDDm"
    unfolding Healthy_def'
  proof (rule ext, clarify)
    fix m z
    show "NDDm M (m, z) = M (m, z)"
      using a by (cases m; auto simp: NDDm_def)
  qed
qed

subsection \<open> Associativity \<close>

text \<open> Parallel is associative on NDD operands when the merge is symmetric,
  NDDm-healthy, and associative on nondivergent branches. \<close>

lemma par_by_merge_assoc_NDD:
  fixes P Q R :: "'s des_hrel" and M :: "'s des_merge"
  assumes nondiv: "P is NDD" "Q is NDD" "R is NDD"
    and merge: "M is SymMerge" "M is NDDm"
      "AssocMerge (merge_guard (\<lambda>x z. ok\<^sub>v x \<longrightarrow> ok\<^sub>v z) M)"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) \<parallel>\<^bsub>M\<^esub> R = P \<parallel>\<^bsub>M\<^esub> (Q \<parallel>\<^bsub>M\<^esub> R)"
proof (rule par_by_merge_assoc_guard[OF SymMerge_merge_guard[OF merge(1)] merge(3)])
  show "\<lbrakk> ok\<^sub>v x \<longrightarrow> ok\<^sub>v p; ok\<^sub>v x \<longrightarrow> ok\<^sub>v q; merge_eval M x p q z \<rbrakk> \<Longrightarrow>
      ok\<^sub>v x \<longrightarrow> ok\<^sub>v z" for x p q z
    using merge(2) by (simp add: NDDm_healthy_iff)
  show "P (x,z) \<Longrightarrow> ok\<^sub>v x \<longrightarrow> ok\<^sub>v z" "Q (x,z) \<Longrightarrow> ok\<^sub>v x \<longrightarrow> ok\<^sub>v z"
    "R (x,z) \<Longrightarrow> ok\<^sub>v x \<longrightarrow> ok\<^sub>v z" for x z
    using nondiv[unfolded NDD_healthy_iff]
    by (blast dest: preD_true_iff[THEN iffD1])+
qed

lemma merge_des_NDDm [closure]: "merge_des j is NDDm"
  unfolding NDDm_healthy_iff
proof (intro allI impI)
  fix x p q z
  assume "merge_eval (merge_des j) x p q z" "ok\<^sub>v x \<and> ok\<^sub>v p \<and> ok\<^sub>v q"
  then show "ok\<^sub>v z"
    by (cases x; cases p; cases q; cases z; simp add: merge_des_expand)
qed

text \<open> On nondivergent branches @{term "merge_des j"} agrees with
  @{term "HDm (merge_des_raw j)"}, which is associative when @{term j} is. \<close>

lemma des_par_assoc_nd:
  assumes nondiv: "P is NDD" "Q is NDD" "R is NDD"
    and merge: "j is SymMerge" "AssocMerge j"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  let ?G = "\<lambda>x z. ok\<^sub>v x \<longrightarrow> ok\<^sub>v z"
  have "merge_guard ?G (merge_des j) = merge_guard ?G (HDm (merge_des_raw j))"
    by (rule merge_guard_cong, rule merge_des_ok_eval; blast)
  moreover have "AssocMerge (merge_guard ?G (HDm (merge_des_raw j)))"
    by (rule AssocMerge_merge_guard[OF HDm_merge_des_raw_AssocMerge[OF merge(2)]];
        auto simp: HDm_merge_des_raw_eval)
  ultimately have "AssocMerge (merge_guard ?G (merge_des j))"
    by simp
  then show ?thesis
    by (rule par_by_merge_assoc_NDD[OF nondiv merge_des_SymMerge[OF merge(1)] merge_des_NDDm])
qed

end
