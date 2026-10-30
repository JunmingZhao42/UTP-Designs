section \<open> Design Parallel-by-Merge \<close>

theory utp_des_parallel
  imports utp_des_healths
begin

text \<open> A design merge relates the initial state and the two branch results to a final state.
  The theory first develops healthiness conditions for design merges and shows that parallel
  by merge preserves design healthiness. It then lifts a state merge to a healthy design merge,
  defines design parallel, and proves its laws for divergence, Chaos, Miracle, and associativity. \<close>

type_synonym 's des_merge = "'s des_vars_ext merge"

subsection \<open> Design Merge Healthiness \<close>

text \<open> The merge conditions below are sufficient to preserve $H1$ and $H2$ under parallel-by-merge.\<close>

subsubsection \<open> Definitions \<close>

definition H1m :: "'s des_merge \<Rightarrow> 's des_merge" where
[pred]: "H1m M = (M \<or> (\<not> $<:ok\<^sup><)\<^sub>e)"

text \<open> $H2m$ applies $H2$ to the merge result by composing the merge with @{const J}. \<close>

definition H2m :: "'s des_merge \<Rightarrow> 's des_merge" where
[pred]: "H2m M = M ;; J"

text \<open> $H3m$ is right-composition with design skip on the merge alphabet. \<close>

definition H3m :: "'s des_merge \<Rightarrow> 's des_merge" where
[pred]: "H3m M \<equiv> M ;; II\<^sub>D"

text \<open> $HDM$ combines $H1m$ and $H2m$. \<close>

definition HDM :: "'s des_merge \<Rightarrow> 's des_merge" where
[pred]: "HDM = H1m \<circ> H2m"

subsubsection \<open> Idempotence and Monotonicity \<close>

lemma H1m_idem: "H1m(H1m M) = H1m M"
  by pred_auto

lemma H2m_idem: "H2m(H2m M) = H2m M"
  by (simp add: H2m_def seqr_assoc J_idem)

lemma H3m_idem: "H3m(H3m M) = H3m M"
  by (simp add: H3m_def seqr_assoc)

lemma H3m_Idempotent [closure]: "Idempotent H3m"
  by (simp add: Idempotent_def H3m_idem)

lemma H3m_mono: "M \<sqsubseteq> N \<Longrightarrow> H3m M \<sqsubseteq> H3m N"
  by (simp add: H3m_def seqr_mono)

lemma H3m_Monotonic [closure]: "Monotonic H3m"
  by (rule MonotonicI, rule H3m_mono)

lemma H1m_H2m_commute:
  "(H1m \<circ> H2m) M = (H2m \<circ> H1m) M"
  by (simp add: comp_def; pred_auto)

lemmas H1m_H2m_commute' = H1m_H2m_commute[simplified comp_apply]

lemma HDM_idem: "HDM(HDM M) = HDM M"
  by (simp add: HDM_def H1m_H2m_commute' H1m_idem H2m_idem)

lemma H1m_Idempotent [closure]: "Idempotent H1m"
  by (simp add: Idempotent_def H1m_idem)

lemma H2m_Idempotent [closure]: "Idempotent H2m"
  by (simp add: Idempotent_def H2m_idem)

lemma HDM_Idempotent [closure]: "Idempotent HDM"
  by (simp add: Idempotent_def HDM_idem)

lemma H1m_mono: "M \<sqsubseteq> N \<Longrightarrow> H1m M \<sqsubseteq> H1m N"
  by pred_auto

lemma H2m_mono: "M \<sqsubseteq> N \<Longrightarrow> H2m M \<sqsubseteq> H2m N"
  by (simp add: H2m_def seqr_mono)

lemma HDM_mono: "M \<sqsubseteq> N \<Longrightarrow> HDM M \<sqsubseteq> HDM N"
  by (simp add: HDM_def H1m_mono H2m_mono)

lemma H1m_Monotonic [closure]: "Monotonic H1m"
  by (rule MonotonicI, rule H1m_mono)

lemma H2m_Monotonic [closure]: "Monotonic H2m"
  by (rule MonotonicI, rule H2m_mono)

lemma HDM_Monotonic [closure]: "Monotonic HDM"
  by (rule MonotonicI, rule HDM_mono)

lemma HDM_fixed_iff:
  "M is HDM \<longleftrightarrow> (M is H1m) \<and> (M is H2m)"
  using H1m_idem[of "H2m M"] H1m_H2m_commute'[of "H2m M"]
  by (auto simp add: Healthy_def' HDM_def H2m_idem)

lemma HDM_healths [closure]:
  assumes "M is HDM"
  shows "M is H1m" "M is H2m"
  using assms by (simp_all add: HDM_fixed_iff)

lemma HDM_intro:
  assumes "M is H1m" "M is H2m"
  shows "M is HDM"
  by (simp add: HDM_fixed_iff assms)

subsubsection \<open> Disjunction and Conjunction \<close>

lemma H1m_disj: "H1m(M \<or> N) = (H1m M \<or> H1m N)"
  by pred_auto

lemma H1m_conj: "H1m(M \<and> N) = (H1m M \<and> H1m N)"
  by pred_auto

lemma H2m_disj: "H2m(M \<or> N) = (H2m M \<or> H2m N)"
  by (simp add: H2m_def seqr_or_distl)

lemma HDM_disj: "HDM(M \<or> N) = (HDM M \<or> HDM N)"
  by (simp add: HDM_def H1m_disj H2m_disj)

text \<open> $H2m$ and $HDM$ do not distribute over arbitrary conjunctions. Closing each conjunct
  separately can use a different intermediate value of $ok'$. The conjunction of two healthy
  merges is still healthy. \<close>

lemma H2m_conj:
  assumes "M is H2m" "N is H2m"
  shows "H2m(M \<and> N) = (H2m M \<and> H2m N)"
proof -
  have "H2m(H2m M \<and> H2m N) = (H2m M \<and> H2m N)"
    by (simp add: H2m_def J_split usubst; pred_auto)
  then show ?thesis
    by (simp only: Healthy_if[OF assms(1)] Healthy_if[OF assms(2)])
qed

lemma HDM_conj:
  assumes "M is H2m" "N is H2m"
  shows "HDM(M \<and> N) = (HDM M \<and> HDM N)"
  by (simp add: HDM_def H2m_conj assms H1m_conj)

lemma H2m_not_conj_distrib:
  "\<not> (\<forall> M N :: 's des_merge. H2m(M \<and> N) = (H2m M \<and> H2m N))"
proof -
  have "H2m(ok\<^sup>> \<and> \<not> ok\<^sup>>) \<noteq>
    (H2m(ok\<^sup>>) \<and> H2m(\<not> ok\<^sup>>) :: 's des_merge)"
    by pred_auto
  then show ?thesis by blast
qed

lemma HDM_not_conj_distrib:
  "\<not> (\<forall> M N :: 's des_merge. HDM(M \<and> N) = (HDM M \<and> HDM N))"
proof -
  have "HDM(ok\<^sup>> \<and> \<not> ok\<^sup>>) \<noteq>
    (HDM(ok\<^sup>>) \<and> HDM(\<not> ok\<^sup>>) :: 's des_merge)"
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

lemma HDM_disj_closed [closure]:
  assumes "M is HDM" "N is HDM"
  shows "(M \<or> N) is HDM"
  by (rule Healthy_intro; simp add: HDM_disj Healthy_if assms)

lemma HDM_conj_closed [closure]:
  assumes "M is HDM" "N is HDM"
  shows "(M \<and> N) is HDM"
  by (rule HDM_intro; simp add: assms closure)

subsubsection \<open> Symmetry \<close>

lemma SymMerge_H1m [closure]:
  assumes "M is SymMerge"
  shows "H1m M is SymMerge"
  using assms by (pred_simp; blast)

lemma SymMerge_H2m [closure]:
  assumes "M is SymMerge"
  shows "H2m M is SymMerge"
  using assms by (simp add: Healthy_def' H2m_def seqr_assoc[symmetric])

lemma SymMerge_HDM [closure]:
  assumes "M is SymMerge"
  shows "HDM M is SymMerge"
  by (simp add: HDM_def assms closure)

subsubsection \<open> Sequential Composition \<close>

lemma H1m_seq [closure]:
  assumes "M is H1m" "P is H1"
  shows "M ;; P is H1m"
  using assms by (pred_simp; blast)

text \<open> For $H2m$, only the continuation needs to be $H2$-healthy. \<close>

lemma H2m_seq [closure]:
  assumes "P is H2"
  shows "M ;; P is H2m"
  using assms by (simp add: Healthy_def' H2m_def H2_def seqr_assoc)

text \<open> Hence $HDM$ needs only $H1m$ of the merge; $H2m$ comes from the continuation. \<close>

lemma HDM_seq [closure]:
  assumes "M is H1m" "P is \<^bold>H"
  shows "M ;; P is HDM"
  by (rule HDM_intro;
      simp add: assms closure H_implies_H1 H_implies_H2)

subsection \<open> Parallel by Merge Preserves Design Healthiness \<close>

lemma des_par_by_merge_unfold:
  fixes P Q :: "'s des_hrel" and M :: "'s des_merge"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) (s0, out) \<longleftrightarrow>
    (\<exists>p q. P (s0, p) \<and> Q (s0, q) \<and> merge_eval M s0 p q out)"
  by (cases s0; cases out;
      simp add: par_by_merge_def par_sep_def; pred_auto; blast)

lemma H1_par_by_merge [closure]:
  fixes P Q :: "'s des_hrel" and M :: "'s des_merge"
  assumes "P is H1" "Q is H1" "M is H1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H1"
  using assms by (pred_simp; auto simp add: all_bool_eq ex_bool_eq)

lemma H2_par_by_merge [closure]:
  fixes P Q :: "'s des_hrel" and M :: "'s des_merge"
  assumes "M is H2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H2"
  using assms
  by (simp add: Healthy_def' H2_def H2m_def par_by_merge_def seqr_assoc)

lemma H3_par_by_merge [closure]:
  fixes P Q :: "'s des_hrel" and M :: "'s des_merge"
  assumes "M is H3m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H3"
  using assms
  by (simp add: Healthy_def' H3_def H3m_def par_by_merge_seq_add)

lemma H_par_by_merge [closure]:
  fixes P Q :: "'s des_hrel" and M :: "'s des_merge"
  assumes "P is H1" "Q is H1" "M is HDM"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is \<^bold>H"
  by (rule Healthy_intro;
      simp add: Healthy_if H1_par_by_merge H2_par_by_merge
        HDM_healths assms)

subsection \<open> Lifting a State Merge \<close>

text \<open> The raw lift applies $j$ to the ordinary state parts of the initial state, both branch
  results, and the resulting state. It sets $ok = ok_0 \wedge ok_1$. \<close>

(* merge_des_raw j ((ok0,s0), (okL,sL), (okR,sR), (okOut,sOut)) =
     (okOut = (okL \<and> okR)) \<and> j(s0, sL, sR, sOut) *)
definition merge_des_raw :: "'s merge \<Rightarrow> 's des_merge" where
"merge_des_raw j = (\<lambda>(m, out).
  des_vars.ok\<^sub>v out =
    (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
  j (\<lparr>mrg_prior\<^sub>v = des_vars.more (mrg_prior\<^sub>v m),
       mrg_left\<^sub>v = des_vars.more (mrg_left\<^sub>v m),
       mrg_right\<^sub>v = des_vars.more (mrg_right\<^sub>v m), \<dots> = ()\<rparr>,
     des_vars.more out))"

text \<open> As in the reactive merge $M_R(M) = N_R(M) ;; II_R$, the design merge follows the healthy
  raw lift with @{const skip_d}. A nonterminating intermediate result releases the final
  observation, so a divergent branch retains only the existence of a merged state. \<close>

definition merge_des :: "'s merge \<Rightarrow> 's des_merge" ("M\<^sub>D") where
"merge_des j = HDM (merge_des_raw j) ;; II\<^sub>D"

text \<open> @{const skip_d} absorbs the $H2m$ part of $HDM$, since $J ;; II_D = II_D$. \<close>

lemma merge_des_alt_def: "merge_des j = H1m (merge_des_raw j) ;; II\<^sub>D"
  by (simp only: merge_des_def HDM_def comp_apply H1m_H2m_commute')
     (simp add: H2m_def seqr_assoc skip_d_absorb_J_2)

lemma merge_des_is_HDM [closure]: "M\<^sub>D(j) is HDM"
  unfolding merge_des_alt_def
  by (rule HDM_seq[OF _ N_implies_H[OF skip_d_is_H1_H3]]; simp add: Healthy_def' H1m_idem)

lemma merge_des_is_H3m [closure]: "merge_des j is H3m"
  by (simp add: Healthy_def' H3m_def merge_des_def seqr_assoc)

text \<open> A symmetric state merge lifts to a symmetric design merge. \<close>

lemma merge_des_SymMerge [closure]:
  assumes "j is SymMerge"
  shows "M\<^sub>D(j) is SymMerge"
proof -
  have "merge_des_raw j is SymMerge"
    using assms by (simp add: Healthy_def' merge_des_raw_def fun_eq_iff; pred_auto; blast)
  then have "HDM (merge_des_raw j) is SymMerge"
    by (rule SymMerge_HDM)
  then show ?thesis
    by (simp add: merge_des_def Healthy_def' seqr_assoc[symmetric])
qed

subsubsection \<open> Evaluating the Merge \<close>

text \<open> Unfolding the merge: termination of both branches requires termination and the
  state merge; otherwise only some merged state must exist. \<close>

(* merge_des j ((ok0,s0), (okL,sL), (okR,sR), (okOut,sOut)) =
     \<not>ok0 \<or> (((okL \<and> okR) \<longrightarrow> (okOut \<and> j(s0, sL, sR, sOut))) \<and>
            (\<exists>y. j(s0, sL, sR, y))) *)
lemma merge_des_expand:
  "merge_eval (merge_des j) \<lparr>ok\<^sub>v = started, \<dots> = s0\<rparr>
    \<lparr>ok\<^sub>v = a, \<dots> = u\<rparr> \<lparr>ok\<^sub>v = b, \<dots> = v\<rparr>
    \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr> \<longleftrightarrow>
    (\<not> started \<or>
      ((a \<and> b \<longrightarrow> (c \<and> merge_eval j s0 u v z)) \<and> (\<exists>y. merge_eval j s0 u v y)))"
  by (simp add: merge_des_alt_def H1m_def merge_des_raw_def skip_d_def rdesign_def design_def;
      pred_auto; blast)

(* okL \<and> okR \<Longrightarrow>
     merge_des j ((True,s0), (okL,sL), (okR,sR), (okOut,sOut)) =
       (okOut \<and> j(s0, sL, sR, sOut)) *)
lemma merge_des_expand_terminate:
  assumes "a" "b"
  shows "merge_eval (merge_des j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
    \<lparr>ok\<^sub>v = a, \<dots> = u\<rparr> \<lparr>ok\<^sub>v = b, \<dots> = v\<rparr>
    \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr> \<longleftrightarrow> (c \<and> merge_eval j s0 u v z)"
  using assms by (simp only: merge_des_expand; blast)

(* \<not>(okL \<and> okR) \<Longrightarrow>
     merge_des j ((True,s0), (okL,sL), (okR,sR), (okOut,sOut)) =
       (\<exists>y. j(s0, sL, sR, y)) *)
lemma merge_des_expand_diverge:
  assumes "\<not> (a \<and> b)"
  shows "merge_eval (merge_des j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
    \<lparr>ok\<^sub>v = a, \<dots> = u\<rparr> \<lparr>ok\<^sub>v = b, \<dots> = v\<rparr>
    \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr> \<longleftrightarrow> (\<exists>y. merge_eval j s0 u v y)"
  using assms by (simp only: merge_des_expand; blast)

subsection \<open> Design Parallel \<close>

abbreviation des_par ::
  "'s des_hrel \<Rightarrow> 's merge \<Rightarrow> 's des_hrel \<Rightarrow> 's des_hrel"
  ("_ \<parallel>\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q \<equiv> P \<parallel>\<^bsub>M\<^sub>D(j)\<^esub> Q"

(* (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q)((ok0,s0), (okOut,sOut)) =
     \<exists>okL sL okR sR. P((ok0,s0), (okL,sL)) \<and> Q((ok0,s0), (okR,sR)) \<and>
       (\<not>ok0 \<or> (((okL \<and> okR) \<longrightarrow> (okOut \<and> j(s0, sL, sR, sOut))) \<and>
                 (\<exists>y. j(s0, sL, sR, y)))) *)
lemma des_par_expand:
  fixes P Q :: "'s des_hrel"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) (\<lparr>ok\<^sub>v = started, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>) \<longleftrightarrow>
   (\<exists>a u b v. P (\<lparr>ok\<^sub>v = started, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = a, \<dots> = u\<rparr>) \<and> Q (\<lparr>ok\<^sub>v = started, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = b, \<dots> = v\<rparr>) \<and>
    (\<not> started \<or>
      ((a \<and> b \<longrightarrow> (c \<and> merge_eval j s0 u v z)) \<and> (\<exists>y. merge_eval j s0 u v y))))"
proof -
  have expand_result:
    "(\<exists>p :: 's des_vars_ext. F p) \<longleftrightarrow>
      (\<exists>b x. F \<lparr>ok\<^sub>v = b, \<dots> = x\<rparr>)" for F
    by pred_auto
  show ?thesis
    by (simp only: des_par_by_merge_unfold expand_result merge_des_expand)
qed

lemma des_par_H_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) is \<^bold>H"
  by (rule H_par_by_merge[OF assms merge_des_is_HDM])

lemma des_par_H3_closure [closure]:
  "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) is H3"
  by (rule H3_par_by_merge[OF merge_des_is_H3m])

lemma des_par_N_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) is \<^bold>N"
  by (simp add: Healthy_def' Healthy_if[OF des_par_H3_closure]
      Healthy_if[OF H1_par_by_merge[OF assms HDM_healths(1)[OF merge_des_is_HDM]]])

subsection \<open> Divergence, Chaos, and Miracle \<close>

text \<open> If one branch diverges from s0, the parallel composition accepts every output from s0,
  provided (1) the other branch has some observation from s0, that is, it is not
  infeasible there, and (2) the two branch states have a merged state under j. \<close>

(* P((True,s0),(okL,sL)) \<and> Q((True,s0),(okR,sR)) \<and> \<not>(okL \<and> okR) \<and> j(s0, sL, sR, y) \<Longrightarrow>
     (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q)((True,s0),(okOut,sOut)) *)
lemma des_par_diverge:
  assumes "P (\<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = a, \<dots> = u\<rparr>)"
      and "Q (\<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = b, \<dots> = v\<rparr>)"
      and "\<not> (a \<and> b)" and "merge_eval j s0 u v y"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) (\<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>)"
  using assms unfolding des_par_expand by blast

lemma des_par_chaos_chaos:
  fixes j :: "'s merge"
  assumes "\<And>s0. \<exists>u v y. merge_eval j s0 u v y"
  shows "(\<bottom>\<^sub>D \<parallel>\<^sub>D\<^bsub>j\<^esub> \<bottom>\<^sub>D) = \<bottom>\<^sub>D"
  by (rule ext; case_tac x; rename_tac s t; case_tac s; case_tac t;
      simp add: des_par_expand bot_d_true true_pred_def ex_bool_eq assms)

lemma des_par_chaos:
  fixes P :: "'s des_hrel"
  assumes "P is H4" and mergeable: "mergeable j"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> \<bottom>\<^sub>D) = \<bottom>\<^sub>D" 
        "(\<bottom>\<^sub>D \<parallel>\<^sub>D\<^bsub>j\<^esub> P) = \<bottom>\<^sub>D"
proof -
  have feasible: "\<exists>a u. P (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = a, \<dots> = u\<rparr>)" for b s0
    using fun_cong[OF is_H4_alt_def[THEN iffD1, OF assms(1)],
        of "(\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>)"]
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
  using assms
  by (simp_all add: Healthy_def' H1_def des_par_by_merge_unfold
      merge_des_alt_def H1m_def merge_des_raw_def skip_d_def rdesign_def design_def)
     (pred_auto; blast)+

subsection \<open> Commutativity \<close>

text \<open> A symmetric state merge makes design parallel commutative, since the lifted merge
  inherits the symmetry. \<close>

lemma des_par_comm:
  assumes "j is SymMerge"
  shows "P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>D\<^bsub>j\<^esub> P"
  by (rule par_by_merge_comm; use merge_des_SymMerge[OF assms] in \<open>simp add: Healthy_def'\<close>)

subsection \<open> Associativity \<close>

lemma des_par_assoc_state:
  fixes P Q R :: "'s des_hrel" and j :: "'s merge"
  assumes "j is SymMerge" "AssocMerge j" and mergeable: "mergeable j"
  shows "(P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have sym: "merge_eval j s0 a b z = merge_eval j s0 b a z" for s0 a b z
    using fun_cong[OF assms(1)[unfolded Healthy_def'],
        of "(\<lparr>mrg_prior\<^sub>v = s0, mrg_left\<^sub>v = a, mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)"]
    by pred_auto
  have assoc: "(\<exists>v. merge_eval j s0 a b v \<and> merge_eval j s0 v c z) =
      (\<exists>v. merge_eval j s0 b c v \<and> merge_eval j s0 a v z)" for s0 a b c z
    using fun_cong[OF assms(2)[unfolded AssocMerge_def],
        of "(\<lparr>mrg_prior\<^sub>v = s0, mrg_left\<^sub>v = a,
          mrg_right\<^sub>v = \<lparr>mrg_prior\<^sub>v = s0, mrg_left\<^sub>v = b, mrg_right\<^sub>v = c, \<dots> = ()\<rparr>, \<dots> = ()\<rparr>, z)"]
    by (pred_simp; simp add: sym)
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
    by (rule ext; case_tac x; simp only: des_par_by_merge_unfold;
        use lifted_assoc in blast)
qed

end
