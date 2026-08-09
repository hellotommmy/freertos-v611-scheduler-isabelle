theory Scheduler_Generic_Root_Coverage_Insert_End
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage_Core.Scheduler_Generic_Root_Universe_Coverage_Core"
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Generated_Container_Frame.Scheduler_Resume_Generated_Container_Frame"
begin

text \<open>
  Abstract counterpart of one Generic-item insert-end.  The target root, task,
  physical key, ring, cursor, and insertion position all remain symbolic.  The
  logical key is read from the total Generic observation K_G, whose equality
  with the physical item value follows from GenericRootFamilyCoverage.
\<close>

definition generic_family_insert_end_abs ::
  "(xLIST_C ptr \<Rightarrow> 'tid node_ring) \<Rightarrow>
   xLIST_C ptr \<Rightarrow> 'tid \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   (xLIST_C ptr \<Rightarrow> 'tid node_ring)"
where
  "generic_family_insert_end_abs abs_fam target t K_G =
     abs_fam(target :=
       list_insert_end_abs (Generic t) (K_G t) (abs_fam target))"

lemma generic_ring_insert_end_Generic:
  assumes wf: "xlist_wf q"
    and generic: "generic_ring q"
  shows "generic_ring (list_insert_end_abs (Generic t) k q)"
  by (rule generic_ring_insert_end[OF wf generic])

lemma GenericRootFamilyCoverage_insert_end_abs_fresh:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and task: "t \<in> managed"
    and target: "target \<in> GenericRootUniverse"
    and absent:
      "raw_family_members GenericRootUniverse raw_fam
         (generic_item_raw_ptr D t) = {}"
  shows "Generic t \<notin> set (ring (abs_fam target))"
proof
  assume member: "Generic t \<in> set (ring (abs_fam target))"
  have raw_member:
    "generic_item_raw_ptr D t \<in> set (ring (raw_fam target))"
    using GenericRootFamilyCoverage_member_iff[
      OF coverage task target] member by blast
  have target_member:
    "target \<in> raw_family_members GenericRootUniverse raw_fam
       (generic_item_raw_ptr D t)"
    using target raw_member by (simp add: raw_family_members_def)
  show False using absent target_member by simp
qed

lemma scheduler_family_insert_end_raw_other_membership:
  assumes pre:
    "scheduler_family_pre_rel h roots raw_fam managed D"
    and target: "target \<in> roots"
    and different: "q \<noteq> p"
  shows
    "q \<in> set (ring
       (scheduler_family_insert_end_raw h raw_fam target p lp))
       \<longleftrightarrow>
     q \<in> set (ring (raw_fam lp))"
proof (cases "lp = target")
  case True
  have raw: "raw_xlist_rel h target (raw_fam target)"
    using pre target
    by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
  have wf: "xlist_wf (raw_fam target)"
    using raw by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have ring_set:
    "set (ring (list_insert_end_abs p (raw_key_at h p)
       (raw_fam target))) = insert p (set (ring (raw_fam target)))"
    by (rule ring_set_insert_end[OF wf])
  show ?thesis
    using True different ring_set
    by (simp add: scheduler_family_insert_end_raw_def)
next
  case False
  then show ?thesis
    by (simp add: scheduler_family_insert_end_raw_def)
qed

lemma GenericRootFamilyCoverage_generic_ptr_managed:
  assumes task: "t \<in> managed"
  shows
    "generic_item_raw_ptr D t \<in> universal_managed_nodes managed D"
  using task
  by (auto simp: generic_item_raw_ptr_def universal_managed_nodes_def)

lemma GenericRootFamilyCoverage_generic_ptr_injective:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and left: "u \<in> managed"
    and right: "t \<in> managed"
    and equal: "generic_item_raw_ptr D u = generic_item_raw_ptr D t"
  shows "u = t"
proof -
  have left_decode:
    "sd_node_decode D (generic_item_raw_ptr D u) = Some (Generic u)"
    by (rule GenericRootFamilyCoverage_generic_decodeD[OF coverage left])
  have right_decode:
    "sd_node_decode D (generic_item_raw_ptr D t) = Some (Generic t)"
    by (rule GenericRootFamilyCoverage_generic_decodeD[OF coverage right])
  have decode_eq:
    "sd_node_decode D (generic_item_raw_ptr D u) =
     sd_node_decode D (generic_item_raw_ptr D t)"
    by (rule arg_cong[OF equal])
  have some_to_right:
    "Some (Generic u) =
     sd_node_decode D (generic_item_raw_ptr D t)"
    by (rule trans[OF sym[OF left_decode] decode_eq])
  have some_eq: "Some (Generic u) = Some (Generic t)"
    by (rule trans[OF some_to_right right_decode])
  have node_eq: "Generic u = Generic t"
    using some_eq by (simp only: option.inject)
  show ?thesis using node_eq by (simp only: node_kind.inject)
qed

section \<open>Root representation\<close>

lemma GenericRootFamilyCoverage_insert_end_root_rep:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and target: "target \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and absent:
      "raw_family_members GenericRootUniverse raw_fam
         (generic_item_raw_ptr D t) = {}"
    and root: "lp \<in> GenericRootUniverse"
  shows
    "generic_family_root_rep D
       (scheduler_family_insert_end_raw h raw_fam target
         (generic_item_raw_ptr D t))
       (generic_family_insert_end_abs abs_fam target t K_G)
       managed lp"
proof (cases "lp = target")
  case False
  have old:
    "generic_family_root_rep D raw_fam abs_fam managed lp"
    by (rule GenericRootFamilyCoverage_root_repD[OF coverage root])
  have raw_at:
    "scheduler_family_insert_end_raw h raw_fam target
       (generic_item_raw_ptr D t) lp = raw_fam lp"
    by (simp only: scheduler_family_insert_end_raw_def fun_upd_apply
        False if_False)
  have abs_at:
    "generic_family_insert_end_abs abs_fam target t K_G lp = abs_fam lp"
    by (simp only: generic_family_insert_end_abs_def fun_upd_apply
        False if_False)
  show ?thesis
    using old
    unfolding generic_family_root_rep_def
    by (simp only: raw_at abs_at)
next
  case True
  let ?p = "generic_item_raw_ptr D t"
  have old:
    "generic_family_root_rep D raw_fam abs_fam managed target"
    by (rule GenericRootFamilyCoverage_root_repD[OF coverage target])
  have raw: "raw_xlist_rel h target (raw_fam target)"
    by (rule GenericRootFamilyCoverage_raw_rootD[OF coverage target])
  have raw_wf: "xlist_wf (raw_fam target)"
    using raw by (simp add: raw_xlist_rel_def raw_xlist_view_def)
  have abs_wf: "xlist_wf (abs_fam target)"
    using old by (simp add: generic_family_root_rep_def)
  have abs_generic: "generic_ring (abs_fam target)"
    using old by (simp add: generic_family_root_rep_def)
  have abs_fresh: "Generic t \<notin> set (ring (abs_fam target))"
    by (rule GenericRootFamilyCoverage_insert_end_abs_fresh[
      OF coverage task target absent])
  have raw_old_subset:
    "set (ring (raw_fam target)) \<subseteq>
       generic_item_raw_set managed D"
    using old by (simp add: generic_family_root_rep_def)
  have p_generic: "?p \<in> generic_item_raw_set managed D"
    using task by (auto simp: generic_item_raw_set_def)
  have raw_ring_set:
    "set (ring (list_insert_end_abs ?p (raw_key_at h ?p)
       (raw_fam target))) = insert ?p (set (ring (raw_fam target)))"
    by (rule ring_set_insert_end[OF raw_wf])
  have raw_post_subset:
    "set (ring (list_insert_end_abs ?p (raw_key_at h ?p)
       (raw_fam target))) \<subseteq> generic_item_raw_set managed D"
    apply (subst raw_ring_set)
    apply (rule insert_subsetI)
     apply (rule p_generic)
    apply (rule raw_old_subset)
    done
  have decode:
    "sd_node_decode D ?p = Some (Generic t)"
    by (rule GenericRootFamilyCoverage_generic_decodeD[OF coverage task])
  have key: "raw_key_at h ?p = K_G t"
    by (rule GenericRootFamilyCoverage_physical_keyD[OF coverage task])
  have relabel:
    "xlist_relabel (sd_node_decode D)
       (list_insert_end_abs ?p (raw_key_at h ?p) (raw_fam target))
       (list_insert_end_abs (Generic t) (K_G t) (abs_fam target))"
    by (rule xlist_relabel_insert_end_preserved[
      OF GenericRootFamilyCoverage_relabelD[OF coverage target]
        raw_wf abs_wf abs_fresh decode key])
  have abs_post_wf:
    "xlist_wf
       (list_insert_end_abs (Generic t) (K_G t) (abs_fam target))"
    by (rule list_insert_end_preserves_wf[OF abs_wf abs_fresh])
  have abs_post_generic:
    "generic_ring
       (list_insert_end_abs (Generic t) (K_G t) (abs_fam target))"
    by (rule generic_ring_insert_end_Generic[OF abs_wf abs_generic])
  show ?thesis
    using True raw_post_subset relabel abs_post_wf abs_post_generic
    by (simp add: generic_family_root_rep_def
        scheduler_family_insert_end_raw_def
        generic_family_insert_end_abs_def)
qed

section \<open>Container representation\<close>

lemma GenericRootFamilyCoverage_insert_end_container_frame:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and target: "target \<in> GenericRootUniverse"
    and fresh:
      "raw_fresh_for_insert target (ring (raw_fam target))
         (generic_item_raw_ptr D t)"
    and task: "t \<in> managed"
    and observed: "q \<in> generic_item_raw_set managed D"
    and different: "q \<noteq> generic_item_raw_ptr D t"
  shows
    "pvContainer_C
       (h_val
         (raw_insert_concrete_heap h target (raw_fam target)
           (generic_item_raw_ptr D t)) q) =
     pvContainer_C (h_val h q)"
proof -
  have pre:
    "scheduler_family_pre_rel h GenericRootUniverse raw_fam managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have p_managed:
    "generic_item_raw_ptr D t \<in> universal_managed_nodes managed D"
    by (rule GenericRootFamilyCoverage_generic_ptr_managed[OF task])
  have q_managed: "q \<in> universal_managed_nodes managed D"
    using observed
    by (auto simp: generic_item_raw_set_def generic_item_raw_ptr_def
        universal_managed_nodes_def)
  have bytes:
    "\<forall>a\<in>raw_container_field_region q.
       raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t) a = h a"
    by (rule raw_insert_end_family_container_byte_frame[
      OF pre target fresh p_managed q_managed different])
  show ?thesis by (rule raw_container_bytes_to_projection[OF bytes])
qed

lemma GenericRootFamilyCoverage_insert_end_target_nonnull:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and target: "target \<in> GenericRootUniverse"
  shows "PTR_COERCE(xLIST_C \<rightarrow> unit) target \<noteq> NULL"
proof -
  have raw: "raw_xlist_rel h target (raw_fam target)"
    by (rule GenericRootFamilyCoverage_raw_rootD[OF coverage target])
  have layout: "raw_xlist_layout target (ring (raw_fam target))"
    using raw by (simp add: raw_xlist_rel_def)
  have guard: "c_guard target"
    using layout by (auto simp: raw_xlist_layout_def)
  have target_not_null: "target \<noteq> NULL"
    by (rule c_guard_NULL[OF guard])
  show ?thesis using target_not_null by simp
qed

lemma GenericRootFamilyCoverage_insert_end_container_faithful:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and target: "target \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and absent:
      "raw_family_members GenericRootUniverse raw_fam
         (generic_item_raw_ptr D t) = {}"
    and fresh:
      "raw_fresh_for_insert target (ring (raw_fam target))
         (generic_item_raw_ptr D t)"
  shows
    "raw_family_container_faithful_on
       (raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_insert_end_raw h raw_fam target
         (generic_item_raw_ptr D t))
       (generic_item_raw_set managed D)"
proof -
  let ?p = "generic_item_raw_ptr D t"
  let ?h' = "raw_insert_concrete_heap h target (raw_fam target) ?p"
  let ?raw' = "scheduler_family_insert_end_raw h raw_fam target ?p"
  have pre:
    "scheduler_family_pre_rel h GenericRootUniverse raw_fam managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have p_managed:
    "?p \<in> universal_managed_nodes managed D"
    by (rule GenericRootFamilyCoverage_generic_ptr_managed[OF task])
  note post = scheduler_family_insert_end_pre_rel_and_linked[
    OF pre target fresh p_managed absent]
  have post_members: "raw_family_members GenericRootUniverse ?raw' ?p = {target}"
    using post by simp
  have post_container:
    "pvContainer_C (h_val ?h' ?p) = PTR_COERCE(xLIST_C \<rightarrow> unit) target"
    using post by simp
  have target_nonnull:
    "PTR_COERCE(xLIST_C \<rightarrow> unit) target \<noteq> NULL"
    by (rule GenericRootFamilyCoverage_insert_end_target_nonnull[
      OF coverage target])
  have old_faithful:
    "raw_family_container_faithful_on h GenericRootUniverse raw_fam
       (generic_item_raw_set managed D)"
    using GenericRootFamilyCoverage_container_repD[OF coverage]
    by (simp add: generic_family_container_rep_def)
  have member_frame:
    "\<And>lp q. q \<noteq> ?p \<Longrightarrow>
       (q \<in> set (ring (?raw' lp)) \<longleftrightarrow>
        q \<in> set (ring (raw_fam lp)))"
    by (rule scheduler_family_insert_end_raw_other_membership[
      OF pre target])
  have family_member_frame:
    "\<And>q. q \<noteq> ?p \<Longrightarrow>
       raw_family_members GenericRootUniverse ?raw' q =
       raw_family_members GenericRootUniverse raw_fam q"
    unfolding raw_family_members_def
    using member_frame by auto
  have container_frame:
    "\<And>q. q \<in> generic_item_raw_set managed D \<Longrightarrow>
       q \<noteq> ?p \<Longrightarrow>
       pvContainer_C (h_val ?h' q) = pvContainer_C (h_val h q)"
    by (rule GenericRootFamilyCoverage_insert_end_container_frame[
      OF coverage target fresh task])
  show ?thesis
    unfolding raw_family_container_faithful_on_def
  proof (rule conjI)
    show
      "\<forall>q\<in>generic_item_raw_set managed D.
         pvContainer_C (h_val ?h' q) = NULL \<longleftrightarrow>
         raw_family_members GenericRootUniverse ?raw' q = {}"
    proof (intro ballI)
      fix q
      assume q_managed: "q \<in> generic_item_raw_set managed D"
      show
        "pvContainer_C (h_val ?h' q) = NULL \<longleftrightarrow>
         raw_family_members GenericRootUniverse ?raw' q = {}"
      proof (cases "q = ?p")
        case True
        show ?thesis
          using post_members post_container target_nonnull target True
          by simp
      next
        case False
        have old_iff:
          "pvContainer_C (h_val h q) = NULL \<longleftrightarrow>
           raw_family_members GenericRootUniverse raw_fam q = {}"
          using old_faithful q_managed
          by (simp add: raw_family_container_faithful_on_def)
        show ?thesis
          using old_iff container_frame[OF q_managed False]
            family_member_frame[OF False]
          by simp
      qed
    qed
  next
    show
      "\<forall>lp\<in>GenericRootUniverse.
       \<forall>q\<in>generic_item_raw_set managed D \<inter>
         set (ring (?raw' lp)).
       pvContainer_C (h_val ?h' q) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    proof (intro ballI)
      fix lp
      assume lp_root: "lp \<in> GenericRootUniverse"
      fix q
      assume q_post:
        "q \<in> generic_item_raw_set managed D \<inter>
           set (ring (?raw' lp))"
      have q_managed: "q \<in> generic_item_raw_set managed D"
        using q_post by simp
      have q_member: "q \<in> set (ring (?raw' lp))"
        using q_post by simp
      show
        "pvContainer_C (h_val ?h' q) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      proof (cases "q = ?p")
        case True
        have lp_target: "lp = target"
          using post_members lp_root q_member True
          by (auto simp: raw_family_members_def)
        show ?thesis using post_container True lp_target by simp
      next
        case False
        have old_member: "q \<in> set (ring (raw_fam lp))"
          using member_frame[where lp=lp and q=q, OF False] q_member
          by blast
        have old_container:
          "pvContainer_C (h_val h q) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          using old_faithful lp_root q_managed old_member
          by (auto simp: raw_family_container_faithful_on_def)
        show ?thesis
          using container_frame[OF q_managed False] old_container by simp
      qed
    qed
  qed
qed

lemma GenericRootFamilyCoverage_insert_end_container_rep:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and target: "target \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and absent:
      "raw_family_members GenericRootUniverse raw_fam
         (generic_item_raw_ptr D t) = {}"
    and fresh:
      "raw_fresh_for_insert target (ring (raw_fam target))
         (generic_item_raw_ptr D t)"
  shows
    "generic_family_container_rep D
       (raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_insert_end_raw h raw_fam target
         (generic_item_raw_ptr D t)) managed"
proof -
  let ?p = "generic_item_raw_ptr D t"
  let ?h' = "raw_insert_concrete_heap h target (raw_fam target) ?p"
  let ?raw' = "scheduler_family_insert_end_raw h raw_fam target ?p"
  have pre:
    "scheduler_family_pre_rel h GenericRootUniverse raw_fam managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have p_managed:
    "?p \<in> universal_managed_nodes managed D"
    by (rule GenericRootFamilyCoverage_generic_ptr_managed[OF task])
  note post = scheduler_family_insert_end_pre_rel_and_linked[
    OF pre target fresh p_managed absent]
  have post_members: "raw_family_members GenericRootUniverse ?raw' ?p = {target}"
    using post by simp
  have post_container:
    "pvContainer_C (h_val ?h' ?p) = PTR_COERCE(xLIST_C \<rightarrow> unit) target"
    using post by simp
  have faithful:
    "raw_family_container_faithful_on ?h' GenericRootUniverse ?raw'
       (generic_item_raw_set managed D)"
    by (rule GenericRootFamilyCoverage_insert_end_container_faithful[
      OF coverage target task absent fresh])
  have old_container:
    "\<And>u lp. u \<in> managed \<Longrightarrow>
       lp \<in> GenericRootUniverse \<Longrightarrow>
       (generic_item_raw_ptr D u \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
        pvContainer_C (h_val h (generic_item_raw_ptr D u)) =
          PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"
    using GenericRootFamilyCoverage_container_repD[OF coverage]
    by (auto simp: generic_family_container_rep_def)
  show ?thesis
    unfolding generic_family_container_rep_def
  proof (rule conjI)
    show
      "raw_family_container_faithful_on ?h' GenericRootUniverse ?raw'
        (generic_item_raw_set managed D)"
      by (rule faithful)
  next
    show
      "\<forall>u\<in>managed. \<forall>lp\<in>GenericRootUniverse.
       generic_item_raw_ptr D u \<in> set (ring (?raw' lp)) \<longleftrightarrow>
       pvContainer_C (h_val ?h' (generic_item_raw_ptr D u)) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    proof (intro ballI)
      fix u
      assume u_managed: "u \<in> managed"
      fix lp
      assume lp_root: "lp \<in> GenericRootUniverse"
      let ?q = "generic_item_raw_ptr D u"
      show
        "?q \<in> set (ring (?raw' lp)) \<longleftrightarrow>
         pvContainer_C (h_val ?h' ?q) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      proof (cases "u = t")
        case True
        have q_p: "?q = ?p"
          using True by (simp only:)
        have member_iff: "?q \<in> set (ring (?raw' lp)) \<longleftrightarrow> lp = target"
          using post_members lp_root True
          by (auto simp: raw_family_members_def)
        have inserted_container:
          "pvContainer_C (h_val ?h' ?q) =
             PTR_COERCE(xLIST_C \<rightarrow> unit) target"
          using post_container by (simp only: q_p)
        show ?thesis
        proof
          assume post_member: "?q \<in> set (ring (?raw' lp))"
          have lp_target: "lp = target"
            by (rule iffD1[OF member_iff post_member])
          show
            "pvContainer_C (h_val ?h' ?q) =
               PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
            using inserted_container lp_target by (simp only:)
        next
          assume observed_container:
            "pvContainer_C (h_val ?h' ?q) =
               PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          have coerced_eq:
            "PTR_COERCE(xLIST_C \<rightarrow> unit) target =
             PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
            by (rule trans[OF sym[OF inserted_container]
                  observed_container])
          have target_lp: "target = lp"
            using coerced_eq by (simp only: ptr_coerce_eq)
          have lp_target: "lp = target" by (rule sym[OF target_lp])
          show "?q \<in> set (ring (?raw' lp))"
            by (rule iffD2[OF member_iff lp_target])
        qed
      next
        case False
        have q_ne: "?q \<noteq> ?p"
        proof
          assume "?q = ?p"
          then have "u = t"
            by (rule GenericRootFamilyCoverage_generic_ptr_injective[
              OF coverage u_managed task])
          then show False using False by simp
        qed
        have q_generic: "?q \<in> generic_item_raw_set managed D"
          using u_managed by (auto simp: generic_item_raw_set_def)
        have member_frame:
          "?q \<in> set (ring (?raw' lp)) \<longleftrightarrow>
           ?q \<in> set (ring (raw_fam lp))"
          by (rule scheduler_family_insert_end_raw_other_membership[
            OF pre target q_ne])
        have container_frame:
          "pvContainer_C (h_val ?h' ?q) = pvContainer_C (h_val h ?q)"
          by (rule GenericRootFamilyCoverage_insert_end_container_frame[
            OF coverage target fresh task q_generic q_ne])
        have old_iff:
          "?q \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
           pvContainer_C (h_val h ?q) =
             PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          by (rule old_container[OF u_managed lp_root])
        show ?thesis
        proof
          assume post_member: "?q \<in> set (ring (?raw' lp))"
          have old_member: "?q \<in> set (ring (raw_fam lp))"
            by (rule iffD1[OF member_frame post_member])
          have old_observation:
            "pvContainer_C (h_val h ?q) =
               PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
            by (rule iffD1[OF old_iff old_member])
          show
            "pvContainer_C (h_val ?h' ?q) =
               PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
            by (rule trans[OF container_frame old_observation])
        next
          assume post_observation:
            "pvContainer_C (h_val ?h' ?q) =
               PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          have old_observation:
            "pvContainer_C (h_val h ?q) =
               PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
            by (rule trans[OF sym[OF container_frame] post_observation])
          have old_member: "?q \<in> set (ring (raw_fam lp))"
            by (rule iffD2[OF old_iff old_observation])
          show "?q \<in> set (ring (?raw' lp))"
            by (rule iffD2[OF member_frame old_member])
        qed
      qed
    qed
  qed
qed

section \<open>Key representation\<close>

lemma GenericRootFamilyCoverage_insert_end_physical_keys:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and target: "target \<in> GenericRootUniverse"
    and fresh:
      "raw_fresh_for_insert target (ring (raw_fam target))
         (generic_item_raw_ptr D t)"
    and task: "t \<in> managed"
    and observed: "u \<in> managed"
  shows
    "raw_key_at
       (raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t))
       (generic_item_raw_ptr D u) = K_G u"
proof -
  have pre:
    "scheduler_family_pre_rel h GenericRootUniverse raw_fam managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have p_managed:
    "generic_item_raw_ptr D t \<in> universal_managed_nodes managed D"
    by (rule GenericRootFamilyCoverage_generic_ptr_managed[OF task])
  have q_managed:
    "generic_item_raw_ptr D u \<in> universal_managed_nodes managed D"
    by (rule GenericRootFamilyCoverage_generic_ptr_managed[OF observed])
  have bytes:
    "\<forall>a\<in>raw_key_field_region (generic_item_raw_ptr D u).
       raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t) a = h a"
    by (rule raw_insert_end_family_key_byte_frame[
      OF pre target fresh p_managed q_managed])
  have frame:
    "raw_key_at
       (raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t))
       (generic_item_raw_ptr D u) =
     raw_key_at h (generic_item_raw_ptr D u)"
    by (rule raw_key_bytes_to_projection[OF bytes])
  show ?thesis
    using frame GenericRootFamilyCoverage_physical_keyD[
      OF coverage observed] by simp
qed

lemma GenericRootFamilyCoverage_insert_end_abstract_keys:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and target: "target \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and absent:
      "raw_family_members GenericRootUniverse raw_fam
         (generic_item_raw_ptr D t) = {}"
    and root: "lp \<in> GenericRootUniverse"
    and observed: "u \<in> managed"
    and member:
      "Generic u \<in> set (ring
        (generic_family_insert_end_abs abs_fam target t K_G lp))"
  shows
    "item_key (generic_family_insert_end_abs abs_fam target t K_G lp)
       (Generic u) = K_G u"
proof (cases "lp = target")
  case False
  have old_member: "Generic u \<in> set (ring (abs_fam lp))"
    using member False
    by (simp add: generic_family_insert_end_abs_def)
  have old_key: "item_key (abs_fam lp) (Generic u) = K_G u"
    by (rule GenericRootFamilyCoverage_abstract_keyD[
      OF coverage observed root old_member])
  show ?thesis
    using old_key False
    by (simp add: generic_family_insert_end_abs_def)
next
  case True
  have old_rep:
    "generic_family_root_rep D raw_fam abs_fam managed target"
    by (rule GenericRootFamilyCoverage_root_repD[OF coverage target])
  have old_wf: "xlist_wf (abs_fam target)"
    using old_rep by (simp add: generic_family_root_rep_def)
  have fresh_abs: "Generic t \<notin> set (ring (abs_fam target))"
    by (rule GenericRootFamilyCoverage_insert_end_abs_fresh[
      OF coverage task target absent])
  have post_set:
    "set (ring (list_insert_end_abs (Generic t) (K_G t)
       (abs_fam target))) = insert (Generic t) (set (ring (abs_fam target)))"
    by (rule ring_set_insert_end[OF old_wf])
  show ?thesis
  proof (cases "u = t")
    case True_u: True
    show ?thesis
      using True True_u
      by (simp add: generic_family_insert_end_abs_def
          list_insert_end_abs_def)
  next
    case False_u: False
    have old_member: "Generic u \<in> set (ring (abs_fam target))"
      using member True post_set False_u
      by (simp add: generic_family_insert_end_abs_def)
    have old_key: "item_key (abs_fam target) (Generic u) = K_G u"
      by (rule GenericRootFamilyCoverage_abstract_keyD[
        OF coverage observed target old_member])
    show ?thesis
      using True False_u old_key
      by (simp add: generic_family_insert_end_abs_def
          list_insert_end_abs_def)
  qed
qed

lemma GenericRootFamilyCoverage_insert_end_key_rep:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and target: "target \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and absent:
      "raw_family_members GenericRootUniverse raw_fam
         (generic_item_raw_ptr D t) = {}"
    and fresh:
      "raw_fresh_for_insert target (ring (raw_fam target))
         (generic_item_raw_ptr D t)"
  shows
    "generic_family_key_rep D
       (raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_insert_end_raw h raw_fam target
         (generic_item_raw_ptr D t))
       (generic_family_insert_end_abs abs_fam target t K_G)
       managed K_G"
  unfolding generic_family_key_rep_def
proof (rule conjI)
  show
    "\<forall>u\<in>managed.
       raw_key_at
         (raw_insert_concrete_heap h target (raw_fam target)
           (generic_item_raw_ptr D t))
         (generic_item_raw_ptr D u) = K_G u"
  proof (intro ballI)
    fix u
    assume observed: "u \<in> managed"
    show
      "raw_key_at
         (raw_insert_concrete_heap h target (raw_fam target)
           (generic_item_raw_ptr D t))
         (generic_item_raw_ptr D u) = K_G u"
      by (rule GenericRootFamilyCoverage_insert_end_physical_keys[
        OF coverage target fresh task observed])
  qed
next
  show
    "\<forall>lp\<in>GenericRootUniverse. \<forall>u\<in>managed.
       Generic u \<in> set (ring
         (generic_family_insert_end_abs abs_fam target t K_G lp))
       \<longrightarrow>
       item_key (generic_family_insert_end_abs abs_fam target t K_G lp)
         (Generic u) = K_G u"
  proof (intro ballI impI)
    fix lp
    assume root: "lp \<in> GenericRootUniverse"
    fix u
    assume observed: "u \<in> managed"
    assume member:
      "Generic u \<in> set (ring
        (generic_family_insert_end_abs abs_fam target t K_G lp))"
    show
      "item_key (generic_family_insert_end_abs abs_fam target t K_G lp)
         (Generic u) = K_G u"
      by (rule GenericRootFamilyCoverage_insert_end_abstract_keys[
        OF coverage target task absent root observed member])
  qed
qed

section \<open>Coverage capstone\<close>

theorem GenericRootFamilyCoverage_insert_end_preserved:
  assumes coverage:
    "GenericRootFamilyCoverage D h GenericRootUniverse
       raw_fam abs_fam managed K_G"
    and target: "target \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and absent:
      "raw_family_members GenericRootUniverse raw_fam
         (generic_item_raw_ptr D t) = {}"
    and fresh:
      "raw_fresh_for_insert target (ring (raw_fam target))
         (generic_item_raw_ptr D t)"
  shows
    "GenericRootFamilyCoverage D
       (raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_insert_end_raw h raw_fam target
         (generic_item_raw_ptr D t))
       (generic_family_insert_end_abs abs_fam target t K_G)
       managed K_G"
proof (rule GenericRootFamilyCoverageI)
  show "GenericRootUniverse = GenericRootUniverse" by simp
next
  have pre:
    "scheduler_family_pre_rel h GenericRootUniverse raw_fam managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have p_managed:
    "generic_item_raw_ptr D t \<in> universal_managed_nodes managed D"
    by (rule GenericRootFamilyCoverage_generic_ptr_managed[OF task])
  note post = scheduler_family_insert_end_pre_rel_and_linked[
    OF pre target fresh p_managed absent]
  show
    "scheduler_family_pre_rel
       (raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_insert_end_raw h raw_fam target
         (generic_item_raw_ptr D t)) managed D"
    using post by simp
next
  show "universal_decoder_laws managed D"
    by (rule GenericRootFamilyCoverage_decoder_lawsD[OF coverage])
next
  fix lp
  assume root: "lp \<in> GenericRootUniverse"
  show
    "generic_family_root_rep D
       (scheduler_family_insert_end_raw h raw_fam target
         (generic_item_raw_ptr D t))
       (generic_family_insert_end_abs abs_fam target t K_G)
       managed lp"
    by (rule GenericRootFamilyCoverage_insert_end_root_rep[
      OF coverage target task absent root])
next
  show
    "generic_family_container_rep D
       (raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_insert_end_raw h raw_fam target
         (generic_item_raw_ptr D t)) managed"
    by (rule GenericRootFamilyCoverage_insert_end_container_rep[
      OF coverage target task absent fresh])
next
  show
    "generic_family_key_rep D
       (raw_insert_concrete_heap h target (raw_fam target)
         (generic_item_raw_ptr D t))
       GenericRootUniverse
       (scheduler_family_insert_end_raw h raw_fam target
         (generic_item_raw_ptr D t))
       (generic_family_insert_end_abs abs_fam target t K_G)
       managed K_G"
    by (rule GenericRootFamilyCoverage_insert_end_key_rep[
      OF coverage target task absent fresh])
qed

end
