section \<open> Design Parallel-by-Merge \<close>

theory utp_des_parallel
  imports utp_des_healths
begin

text \<open> Design merge healthiness, state-merge lifting, and parallel composition laws. \<close>

type_synonym 's des_merge = "'s des_vars_ext merge"

subsection \<open> Design Merge Healthiness \<close>

text \<open> These merge conditions preserve design healthiness under parallel by merge.
  The prior, branch and output alphabets may differ, as needed for angelic designs. \<close>

subsubsection \<open> Definitions \<close>

definition H1m ::
  "(('a des_vars_scheme, 'b, 'c) mrg, 'd) urel \<Rightarrow> (('a des_vars_scheme, 'b, 'c) mrg, 'd) urel"
where [pred]: "H1m M = (M \<or> (\<not> $<:ok\<^sup><)\<^sub>e)"

text \<open> $H2m$ applies $H2$ to the merge result by composing the merge with @{const J}. \<close>

definition H2m ::
  "(('a, 'b, 'c) mrg, 'd des_vars_scheme) urel \<Rightarrow> (('a, 'b, 'c) mrg, 'd des_vars_scheme) urel"
where [pred]: "H2m M = M ;; J"

text \<open> $H3m$ is right-composition with design skip on the merge alphabet. \<close>

definition H3m ::
  "(('a, 'b, 'c) mrg, 'd des_vars_scheme) urel \<Rightarrow> (('a, 'b, 'c) mrg, 'd des_vars_scheme) urel"
where [pred]: "H3m M \<equiv> M ;; II\<^sub>D"

text \<open> $HDm$ combines $H1m$ and $H2m$. \<close>

definition HDm ::
  "(('a des_vars_scheme, 'b, 'c) mrg, 'd des_vars_scheme) urel
   \<Rightarrow> (('a des_vars_scheme, 'b, 'c) mrg, 'd des_vars_scheme) urel"
where [pred]: "HDm \<equiv> H1m \<circ> H2m"

subsubsection \<open> Idempotence and Monotonicity \<close>

lemma H1m_idem: "H1m(H1m M) = H1m M"
  by pred_auto

lemma H2m_idem: "H2m(H2m M) = H2m M"
  by (simp add: H2m_def seqr_assoc J_idem)

lemma H3m_idem: "H3m(H3m M) = H3m M"
  by (simp add: H3m_def seqr_assoc)

lemma H1m_H2m_commute:
  "(H1m \<circ> H2m) M = (H2m \<circ> H1m) M"
  by (simp add: comp_def; pred_auto)

lemmas H1m_H2m_commute' = H1m_H2m_commute[simplified comp_apply]

lemma HDm_idem: "HDm(HDm M) = HDm M"
  by (simp add: HDm_def H1m_H2m_commute' H1m_idem H2m_idem)

lemma H1m_Idempotent [closure]: "Idempotent H1m"
  by (simp add: Idempotent_def H1m_idem)

lemma H2m_Idempotent [closure]: "Idempotent H2m"
  by (simp add: Idempotent_def H2m_idem)

lemma H3m_Idempotent [closure]: "Idempotent H3m"
  by (simp add: Idempotent_def H3m_idem)

lemma HDm_Idempotent [closure]: "Idempotent HDm"
  by (simp add: Idempotent_def HDm_idem)

lemma H1m_mono: "M \<sqsubseteq> N \<Longrightarrow> H1m M \<sqsubseteq> H1m N"
  by pred_auto

lemma H2m_mono: "M \<sqsubseteq> N \<Longrightarrow> H2m M \<sqsubseteq> H2m N"
  by (simp add: H2m_def seqr_mono)

lemma H3m_mono: "M \<sqsubseteq> N \<Longrightarrow> H3m M \<sqsubseteq> H3m N"
  by (simp add: H3m_def seqr_mono)

lemma HDm_mono: "M \<sqsubseteq> N \<Longrightarrow> HDm M \<sqsubseteq> HDm N"
  by (simp add: HDm_def H1m_mono H2m_mono)

lemma H1m_Monotonic [closure]: "Monotonic H1m"
  by (rule MonotonicI, rule H1m_mono)

lemma H2m_Monotonic [closure]: "Monotonic H2m"
  by (rule MonotonicI, rule H2m_mono)

lemma H3m_Monotonic [closure]: "Monotonic H3m"
  by (rule MonotonicI, rule H3m_mono)

lemma HDm_Monotonic [closure]: "Monotonic HDm"
  by (rule MonotonicI, rule HDm_mono)

lemma HDm_fixed_iff:
  "M is HDm \<longleftrightarrow> (M is H1m) \<and> (M is H2m)"
  using H1m_idem[of "H2m M"] H1m_H2m_commute'[of "H2m M"]
  by (auto simp add: Healthy_def' HDm_def H2m_idem)

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
  by (simp add: HDm_def H1m_H2m_commute' H1m_idem)
lemma H2m_HDm_commute:
  "H2m (HDm M) = HDm (H2m M)"
  by (simp add: HDm_def H1m_H2m_commute' H2m_idem)
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

text \<open> H2m and HDm distribute over conjunction for H2m-healthy operands, but not in general. \<close>

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

lemma H2m_not_conj_distrib:
  "\<not> (\<forall> M N :: 's des_merge. H2m(M \<and> N) = (H2m M \<and> H2m N))"
proof -
  have "H2m(ok\<^sup>> \<and> \<not> ok\<^sup>>) \<noteq>
    (H2m(ok\<^sup>>) \<and> H2m(\<not> ok\<^sup>>) :: 's des_merge)"
    by pred_auto
  then show ?thesis by blast
qed

lemma HDm_not_conj_distrib:
  "\<not> (\<forall> M N :: 's des_merge. HDm(M \<and> N) = (HDm M \<and> HDm N))"
proof -
  have "HDm(ok\<^sup>> \<and> \<not> ok\<^sup>>) \<noteq>
    (HDm(ok\<^sup>>) \<and> HDm(\<not> ok\<^sup>>) :: 's des_merge)"
    by pred_auto
  then show ?thesis by blast
qed

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

subsection \<open> Generic Design Parallel Laws \<close>

subsubsection \<open> Healthiness Closure \<close>

lemma des_par_by_merge_unfold:
  fixes P Q :: "'s des_hrel" and M :: "'s des_merge"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) (x, z) \<longleftrightarrow>
    (\<exists>p q. P (x, p) \<and> Q (x, q) \<and> merge_eval M x p q z)"
  by (cases x; cases z;
      simp add: par_by_merge_def par_sep_def; pred_auto; blast)

text \<open> The closure rules allow the operands to have different output alphabets. \<close>

lemma H1_par_by_merge [closure]:
  fixes P :: "('a, 'b) des_rel" and Q :: "('a, 'c) des_rel"
    and M :: "(('a des_vars_scheme, 'b des_vars_scheme, 'c des_vars_scheme) mrg, 'd des_vars_scheme) urel"
  assumes "P is H1" "Q is H1" "M is H1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H1"
  using assms by (pred_simp; auto simp add: all_bool_eq ex_bool_eq)

lemma H2_par_by_merge [closure]:
  fixes P :: "('a des_vars_scheme, 'b) urel" and Q :: "('a des_vars_scheme, 'c) urel"
    and M :: "(('a des_vars_scheme, 'b, 'c) mrg, 'd des_vars_scheme) urel"
  assumes "M is H2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H2"
  using assms
  by (simp add: Healthy_def' H2_def H2m_def par_by_merge_def seqr_assoc)

lemma H3_par_by_merge [closure]:
  fixes P :: "('a des_vars_scheme, 'b) urel" and Q :: "('a des_vars_scheme, 'c) urel"
    and M :: "(('a des_vars_scheme, 'b, 'c) mrg, 'd des_vars_scheme) urel"
  assumes "M is H3m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H3"
  using assms
  by (simp add: Healthy_def' H3_def H3m_def par_by_merge_seq_add)

lemma H_par_by_merge [closure]:
  fixes P :: "('a, 'b) des_rel" and Q :: "('a, 'c) des_rel"
    and M :: "(('a des_vars_scheme, 'b des_vars_scheme, 'c des_vars_scheme) mrg, 'd des_vars_scheme) urel"
  assumes "P is H1" "Q is H1" "M is HDm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is \<^bold>H"
  by (rule Healthy_intro;
      simp add: Healthy_if H1_par_by_merge H2_par_by_merge
        HDm_healths assms)

subsubsection \<open> Miracle \<close>

lemma par_by_merge_miracle:
  assumes "P is H1" "M is H1m"
  shows "P \<parallel>\<^bsub>M\<^esub> \<top>\<^sub>D = \<top>\<^sub>D"
        "\<top>\<^sub>D \<parallel>\<^bsub>M\<^esub> P = \<top>\<^sub>D"
  using assms
  by (simp add: Healthy_def' H1_def H1m_def top_d_not_ok par_by_merge_eval;
      pred_auto; blast)+

subsection \<open> Lifting a State Merge \<close>

subsubsection \<open> Construction \<close>

text \<open> The raw lift applies the state merge and sets the output flag to the conjunction
  of the branch flags. \<close>

(* merge_des_raw j ((ok,s), (okL,sL), (okR,sR), (ok',s')) =
     (ok' = (okL \<and> okR)) \<and> j(s, sL, sR, s') *)
definition merge_des_raw :: "'s merge \<Rightarrow> 's des_merge" where
"merge_des_raw j = (\<lambda>(m, z).
  des_vars.ok\<^sub>v z =
    (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
  j (\<lparr>mrg_prior\<^sub>v = des_vars.more (mrg_prior\<^sub>v m),
       mrg_left\<^sub>v = des_vars.more (mrg_left\<^sub>v m),
       mrg_right\<^sub>v = des_vars.more (mrg_right\<^sub>v m), \<dots> = ()\<rparr>,
     des_vars.more z))"

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

(* okL \<and> okR \<Longrightarrow>
     merge_des j ((True,s), (okL,sL), (okR,sR), (ok',s')) =
       (ok' \<and> j(s, sL, sR, s')) *)
lemma merge_des_expand_terminate:
  assumes "okL" "okR"
  shows "merge_eval (merge_des j) \<lparr>ok\<^sub>v = True, \<dots> = s\<rparr>
    \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
    \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr> \<longleftrightarrow> (ok' \<and> merge_eval j s sL sR s')"
  using assms by (simp only: merge_des_expand; blast)

(* \<not>(okL \<and> okR) \<Longrightarrow>
     merge_des j ((True,s), (okL,sL), (okR,sR), (ok',s')) =
       (\<exists>y. j(s, sL, sR, y)) *)
lemma merge_des_expand_diverge:
  assumes "\<not> (okL \<and> okR)"
  shows "merge_eval (merge_des j) \<lparr>ok\<^sub>v = True, \<dots> = s\<rparr>
    \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
    \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr> \<longleftrightarrow> (\<exists>y. merge_eval j s sL sR y)"
  using assms by (simp only: merge_des_expand; blast)

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
  by (rule HDm_seq[OF _ N_implies_H[OF skip_d_is_H1_H3]]; simp add: Healthy_def' H1m_idem)

lemma merge_des_is_H3m [closure]: "merge_des j is H3m"
  by (simp add: Healthy_def' merge_des_def H3m_idem)

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
    using assms unfolding AssocMerge_cyclic_eval
    by (simp add: ex_des HDm_merge_des_raw_eval ex_bool_eq; blast)
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
    by (simp only: des_par_by_merge_unfold expand_result merge_des_expand)
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
      Healthy_if[OF H1_par_by_merge[OF assms HDm_healths(1)[OF merge_des_is_HDm]]])

subsubsection \<open> Divergence and Zero Laws \<close>

text \<open> A divergent branch permits every output when both branch observations exist
  and their states can merge. \<close>

(* P((True,s),(okL,sL)) \<and> Q((True,s),(okR,sR)) \<and> \<not>(okL \<and> okR) \<and> j(s, sL, sR, y) \<Longrightarrow>
     (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q)((True,s),(ok',s')) *)
lemma des_par_diverge:
  "\<lbrakk> P (\<lparr>ok\<^sub>v = True, \<dots> = s\<rparr>, \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>);
     Q (\<lparr>ok\<^sub>v = True, \<dots> = s\<rparr>, \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>);
     \<not> (okL \<and> okR); merge_eval j s sL sR y \<rbrakk> \<Longrightarrow>
    (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) (\<lparr>ok\<^sub>v = True, \<dots> = s\<rparr>, \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>)"
  unfolding des_par_expand by blast

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
  have feasible: "\<exists>ok' s'. P (\<lparr>ok\<^sub>v = ok0, \<dots> = s\<rparr>, \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>)" for ok0 s
    using fun_cong[OF is_H4_alt_def[THEN iffD1, OF assms(1)],
        of "(\<lparr>ok\<^sub>v = ok0, \<dots> = s\<rparr>, \<lparr>ok\<^sub>v = ok0, \<dots> = s\<rparr>)"]
    by (simp add: seq_def true_pred_def) (metis des_vars.surjective)
  show "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> \<bottom>\<^sub>D) = \<bottom>\<^sub>D" "(\<bottom>\<^sub>D \<parallel>\<^sub>D\<^bsub>j\<^esub> P) = \<bottom>\<^sub>D"
    by (rule ext; case_tac x; rename_tac s t; case_tac s; case_tac t;
        simp add: des_par_expand bot_d_true true_pred_def ex_bool_eq all_bool_eq
          mergeable feasible[simplified ex_bool_eq])+
qed

lemma des_par_miracle:
  assumes "P is H1"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> \<top>\<^sub>D) = \<top>\<^sub>D" 
        "(\<top>\<^sub>D \<parallel>\<^sub>D\<^bsub>j\<^esub> P) = \<top>\<^sub>D"
  by (rule par_by_merge_miracle[OF assms HDm_healths(1)[OF merge_des_is_HDm]])+

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
proof -
  have assoc: "(\<exists>u. merge_eval j x p q u \<and> merge_eval j x u r z) =
      (\<exists>u. merge_eval j x q r u \<and> merge_eval j x p u z)" for x p q r z
    using par_by_merge_assoc_iff[where M=j]
      par_by_merge_assoc[OF sym am] by blast
  have ex_des: "(\<exists>x. F x) = (\<exists>b s. F \<lparr>ok\<^sub>v = b, \<dots> = s\<rparr>)"
    for F :: "'s des_vars_ext \<Rightarrow> bool"
    by pred_auto
  have lifted_assoc:
    "(\<exists>u. merge_eval (merge_des j) x p q u \<and> merge_eval (merge_des j) x u r z) =
     (\<exists>u. merge_eval (merge_des j) x q r u \<and> merge_eval (merge_des j) x p u z)"
    for x p q r z
    by (cases x; cases p; cases q; cases r; cases z;
        rename_tac b s0 a u d v e w c s;
        simp only: ex_des merge_des_expand mergeable HOL.simp_thms;
        case_tac b; case_tac a; case_tac d; case_tac e;
        simp add: ex_bool_eq all_bool_eq assoc mergeable conj_left_commute)
  show ?thesis
    using lifted_assoc par_by_merge_assoc_iff[where M="merge_des j"] by blast
qed

text \<open>NDD-healthy operands cannot diverge when started. Under this guard,
  the completed merge agrees with the uncompleted merge, whose associativity
  gives the result.\<close>

lemma des_par_assoc_nondiv:
  fixes j :: "'s merge"
  assumes sym_j: "j is SymMerge" and am: "AssocMerge j"
    and nondiv: "P is NDD" "Q is NDD" "R is NDD"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have pre: "pre\<^sub>D P = true" "pre\<^sub>D Q = true" "pre\<^sub>D R = true"
    using nondiv by (simp_all add: NDD_healthy_iff)
  let ?M = "merge_des j" and ?N = "HDm (merge_des_raw j)"
  let ?G = "\<lambda>x z. ok\<^sub>v x \<longrightarrow> ok\<^sub>v z"
  have sym: "?N is SymMerge"
    by (simp add: SymMerge_HDm merge_des_raw_SymMerge sym_j)
  have assoc: "AssocMerge ?N"
    by (rule HDm_merge_des_raw_AssocMerge[OF am])
  have agree: "merge_eval ?M x p q z = merge_eval ?N x p q z"
    if "?G x p" "?G x q" for x p q z
    by (rule merge_des_ok_eval; use that in blast)
  have closed: "?G x z"
    if "?G x p" "?G x q" "merge_eval ?M x p q z" for x p q z
    using that agree[OF that(1,2)] by (auto simp: HDm_merge_des_raw_eval)
  have g: "P (x,z) \<Longrightarrow> ?G x z" "Q (x,z) \<Longrightarrow> ?G x z"
    "R (x,z) \<Longrightarrow> ?G x z" for x z
    using pre by (blast dest: preD_true_iff[THEN iffD1])+
  have fold_N: "(\<exists>u. merge_eval ?N x p q u \<and> merge_eval ?N x u r z) =
      (\<exists>u. merge_eval ?N x q r u \<and> merge_eval ?N x p u z)" for x p q r z
    using par_by_merge_assoc_iff[where M="?N"] par_by_merge_assoc[OF sym assoc] by blast
  show ?thesis
  proof (rule par_by_merge_assoc_on[OF _ g])
    fix x p q r z :: "'s des_vars_ext"
    assume guard: "?G x p" "?G x q" "?G x r"
    have "(\<exists>u. merge_eval ?M x p q u \<and> merge_eval ?M x u r z) =
        (\<exists>u. merge_eval ?N x p q u \<and> merge_eval ?N x u r z)"
      using closed[OF guard(1,2)] agree[OF _ guard(3)]
      by (simp only: agree[OF guard(1,2), symmetric]; blast)
    also have "... = (\<exists>u. merge_eval ?N x q r u \<and> merge_eval ?N x p u z)"
      by (rule fold_N)
    also have "... = (\<exists>u. merge_eval ?M x q r u \<and> merge_eval ?M x p u z)"
      using closed[OF guard(2,3)] agree[OF guard(1)]
      by (simp only: agree[OF guard(2,3), symmetric]; blast)
    finally show "(\<exists>u. merge_eval ?M x p q u \<and> merge_eval ?M x u r z) =
        (\<exists>u. merge_eval ?M x q r u \<and> merge_eval ?M x p u z)" .
  qed
qed

end
