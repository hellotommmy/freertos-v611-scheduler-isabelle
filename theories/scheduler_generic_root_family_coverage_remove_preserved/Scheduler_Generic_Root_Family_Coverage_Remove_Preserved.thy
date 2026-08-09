theory Scheduler_Generic_Root_Family_Coverage_Remove_Preserved
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage_Core.Scheduler_Generic_Root_Universe_Coverage_Core"
    "EAL6_FreeRTOS_V611_Scheduler_Node_Kind_Family_Remove_Preservation.Scheduler_Node_Kind_Family_Remove_Preservation"
begin

text \<open>
  Removing one Generic item from its represented owner preserves the complete
  Generic-root coverage relation.  The theorem is parametric in the task
  domain, decoder, heap, root family, owner, keys, ring lengths and cursors.
  In particular, the owner is only required to be a member of the configured
  GenericRootUniverse; it is not restricted to a ready or delayed root, so the
  termination root is covered by the same statement.
\<close>

lemma scheduler_family_generic_raw_ptr_eq_generic_item_raw_ptr[simp]:
  "scheduler_family_generic_raw_ptr D t = generic_item_raw_ptr D t"
  by (simp only: scheduler_family_generic_raw_ptr_def
      generic_item_raw_ptr_def)

lemma scheduler_family_generic_raw_set_eq_generic_item_raw_set[simp]:
  "scheduler_family_generic_raw_set live D = generic_item_raw_set live D"
proof -
  have pointwise:
    "scheduler_family_generic_raw_ptr D = generic_item_raw_ptr D"
    by (rule ext)
       (simp only: scheduler_family_generic_raw_ptr_eq_generic_item_raw_ptr)
  show ?thesis
    by (simp only: scheduler_family_generic_raw_set_def
        generic_item_raw_set_def pointwise)
qed

theorem GenericRootFamilyCoverage_remove_preserved:
  assumes coverage:
      "GenericRootFamilyCoverage
         D h roots raw_fam abs_fam managed K_G"
    and source: "source \<in> GenericRootUniverse"
    and task: "t \<in> managed"
    and member:
      "generic_item_raw_ptr D t \<in> set (ring (raw_fam source))"
  shows
    "GenericRootFamilyCoverage D
       (raw_remove_concrete_heap h (generic_item_raw_ptr D t)) roots
       (scheduler_family_remove_raw raw_fam source
          (generic_item_raw_ptr D t))
       (scheduler_family_remove_abs abs_fam source (Generic t))
       managed K_G"
proof -
  let ?p = "generic_item_raw_ptr D t"
  let ?h' = "raw_remove_concrete_heap h ?p"
  let ?raw' = "scheduler_family_remove_raw raw_fam source ?p"
  let ?abs' = "scheduler_family_remove_abs abs_fam source (Generic t)"

  have universe: "roots = GenericRootUniverse"
    by (rule GenericRootFamilyCoverage_universeD[OF coverage])
  have source_root: "source \<in> roots"
    using source universe by simp
  have pre: "scheduler_family_pre_rel h roots raw_fam managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have laws: "universal_decoder_laws managed D"
    by (rule GenericRootFamilyCoverage_decoder_lawsD[OF coverage])
  have old_roots:
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      generic_family_root_rep D raw_fam abs_fam managed lp"
    by (rule GenericRootFamilyCoverage_root_repD[OF coverage])
  have generic_only:
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      set (ring (raw_fam lp))
        \<subseteq> scheduler_family_generic_raw_set managed D"
    using old_roots
    by (simp add: generic_family_root_rep_def)
  have relabels:
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      xlist_relabel (sd_node_decode D) (raw_fam lp) (abs_fam lp)"
    using old_roots
    by (simp add: generic_family_root_rep_def)
  have abs_wf:
    "\<And>lp. lp \<in> roots \<Longrightarrow> xlist_wf (abs_fam lp)"
    using old_roots
    by (simp add: generic_family_root_rep_def)
  have old_physical_keys:
    "\<And>u. u \<in> managed \<Longrightarrow>
      raw_key_at h (scheduler_family_generic_raw_ptr D u) = K_G u"
    using GenericRootFamilyCoverage_physical_keyD[OF coverage]
    by simp
  have native_member:
    "scheduler_family_generic_raw_ptr D t
       \<in> set (ring (raw_fam source))"
    using member by simp

  note interface_native = scheduler_generic_task_family_remove_interface[
      OF pre laws source_root task native_member generic_only relabels
         abs_wf old_physical_keys]
  have interface:
    "scheduler_node_kind_family_remove_post D h ?h' roots
       raw_fam abs_fam managed source ?p (Generic t) \<and>
     (\<forall>lp\<in>roots.
        set (ring (?raw' lp)) \<subseteq> generic_item_raw_set managed D) \<and>
     (\<forall>lp\<in>roots.
        xlist_relabel (sd_node_decode D) (?raw' lp) (?abs' lp)) \<and>
     (\<forall>u\<in>managed. raw_key_at ?h' (generic_item_raw_ptr D u) = K_G u)"
    using interface_native
    unfolding scheduler_family_generic_raw_ptr_def generic_item_raw_ptr_def
      scheduler_family_generic_raw_set_def generic_item_raw_set_def
    by assumption
  have interface_rest1:
    "(\<forall>lp\<in>roots.
        set (ring (?raw' lp)) \<subseteq> generic_item_raw_set managed D) \<and>
     (\<forall>lp\<in>roots.
        xlist_relabel (sd_node_decode D) (?raw' lp) (?abs' lp)) \<and>
     (\<forall>u\<in>managed.
        raw_key_at ?h' (generic_item_raw_ptr D u) = K_G u)"
    using interface by (rule conjunct2)
  have pre_and_unlinked:
    "scheduler_family_pre_rel ?h' roots ?raw' managed D \<and>
     raw_family_globally_unlinked ?h' roots ?raw' ?p"
    by (rule scheduler_family_remove_pre_rel_and_unlinked[
          OF pre source_root member])
  have pre_post: "scheduler_family_pre_rel ?h' roots ?raw' managed D"
    using pre_and_unlinked by (rule conjunct1)
  have subset_post:
    "\<forall>lp\<in>roots.
       set (ring (?raw' lp)) \<subseteq> generic_item_raw_set managed D"
    using interface_rest1 by (rule conjunct1)
  have interface_rest2:
    "(\<forall>lp\<in>roots.
        xlist_relabel (sd_node_decode D) (?raw' lp) (?abs' lp)) \<and>
     (\<forall>u\<in>managed.
        raw_key_at ?h' (generic_item_raw_ptr D u) = K_G u)"
    using interface_rest1 by (rule conjunct2)
  have relabel_post:
    "\<forall>lp\<in>roots.
       xlist_relabel (sd_node_decode D) (?raw' lp) (?abs' lp)"
    using interface_rest2 by (rule conjunct1)
  have decode_p: "sd_node_decode D ?p = Some (Generic t)"
    by (rule GenericRootFamilyCoverage_generic_decodeD[OF coverage task])
  have wf_post: "\<forall>lp\<in>roots. xlist_wf (?abs' lp)"
  proof (intro ballI)
    fix lp
    assume lp_root: "lp \<in> roots"
    show "xlist_wf (?abs' lp)"
      by (rule scheduler_family_remove_abs_wf_preserved[
            where owner=source and roots=roots and p="?p"
              and raw_fam=raw_fam and decode_fn="sd_node_decode D"
              and abs_fam=abs_fam and n="Generic t" and lp=lp,
            OF source_root member relabels abs_wf decode_p lp_root])
  qed
  have physical_keys_post:
    "\<forall>u\<in>managed.
       raw_key_at ?h' (generic_item_raw_ptr D u) = K_G u"
    using interface_rest2 by (rule conjunct2)
  have unlinked:
    "raw_family_globally_unlinked ?h' roots ?raw' ?p"
    using pre_and_unlinked by (rule conjunct2)
  have removed_members: "raw_family_members roots ?raw' ?p = {}"
    using unlinked by (simp add: raw_family_globally_unlinked_def)
  note removed_effect = scheduler_family_remove_item_effect[
      OF pre source_root member]
  have removed_effect_rest:
    "pvContainer_C (h_val ?h' ?p) = NULL \<and>
     xLIST_ITEM_C.pxNext_C (h_val ?h' ?p) =
       xLIST_ITEM_C.pxNext_C (h_val h ?p) \<and>
     xLIST_ITEM_C.pxPrevious_C (h_val ?h' ?p) =
       xLIST_ITEM_C.pxPrevious_C (h_val h ?p)"
    using removed_effect by (rule conjunct2)
  have removed_null: "pvContainer_C (h_val ?h' ?p) = NULL"
    using removed_effect_rest by (rule conjunct1)

  have generic_rings_post:
    "\<forall>lp\<in>roots. generic_ring (?abs' lp)"
  proof (intro ballI)
    fix lp
    assume lp_root: "lp \<in> roots"
    have old: "generic_ring (abs_fam lp)"
      using old_roots[OF lp_root]
      by (simp add: generic_family_root_rep_def)
    show "generic_ring (?abs' lp)"
      using old
      by (cases "lp = source")
         (auto simp: scheduler_family_remove_abs_def list_remove_abs_def
            generic_ring_def)
  qed
  have root_rep_post:
    "\<And>lp. lp \<in> roots \<Longrightarrow>
      generic_family_root_rep D ?raw' ?abs' managed lp"
    using subset_post relabel_post wf_post generic_rings_post
    by (simp add: generic_family_root_rep_def)
  have container_old:
    "generic_family_container_rep D h roots raw_fam managed"
    by (rule GenericRootFamilyCoverage_container_repD[OF coverage])
  have faithful_old:
    "raw_family_container_faithful_on h roots raw_fam
       (generic_item_raw_set managed D)"
    using container_old
    by (simp add: generic_family_container_rep_def)
  have p_managed: "?p \<in> generic_item_raw_set managed D"
    using task by (auto simp: generic_item_raw_set_def)
  have membership_frame:
    "\<And>lp q. lp \<in> roots \<Longrightarrow>
      q \<in> generic_item_raw_set managed D \<Longrightarrow> q \<noteq> ?p \<Longrightarrow>
      (q \<in> set (ring (?raw' lp)) \<longleftrightarrow>
       q \<in> set (ring (raw_fam lp)))"
  proof -
    fix lp q
    assume lp_root: "lp \<in> roots"
      and q_managed: "q \<in> generic_item_raw_set managed D"
      and q_ne: "q \<noteq> ?p"
    show
      "q \<in> set (ring (?raw' lp)) \<longleftrightarrow>
       q \<in> set (ring (raw_fam lp))"
      by (rule scheduler_family_remove_raw_membership_frame[OF q_ne])
  qed
  have container_frame:
    "\<And>q. q \<in> generic_item_raw_set managed D \<Longrightarrow> q \<noteq> ?p \<Longrightarrow>
      pvContainer_C (h_val ?h' q) = pvContainer_C (h_val h q)"
  proof -
    fix q
    assume q_managed: "q \<in> generic_item_raw_set managed D"
      and q_ne: "q \<noteq> ?p"
    obtain u where u_managed: "u \<in> managed"
      and q: "q = generic_item_raw_ptr D u"
      using q_managed by (auto simp: generic_item_raw_set_def)
    have q_universal: "q \<in> universal_managed_nodes managed D"
      using u_managed q
      by (auto simp: generic_item_raw_ptr_def universal_managed_nodes_def)
    show "pvContainer_C (h_val ?h' q) = pvContainer_C (h_val h q)"
      using scheduler_family_remove_managed_payload_frame[
        OF pre source_root member q_universal q_ne]
      by simp
  qed
  have faithful_post:
    "raw_family_container_faithful_on ?h' roots ?raw'
       (generic_item_raw_set managed D)"
    by (rule raw_family_container_faithful_on_preserved[
          OF faithful_old p_managed removed_members membership_frame
             container_frame removed_null])
  have faithful_live_owner:
    "\<forall>lp\<in>roots.
       \<forall>q\<in>generic_item_raw_set managed D \<inter> set (ring (?raw' lp)).
       pvContainer_C (h_val ?h' q) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    using faithful_post
    unfolding raw_family_container_faithful_on_def
    by (rule conjunct2)
  have pointwise_container_post:
    "\<forall>u\<in>managed. \<forall>lp\<in>roots.
       generic_item_raw_ptr D u \<in> set (ring (?raw' lp)) \<longleftrightarrow>
       pvContainer_C (h_val ?h' (generic_item_raw_ptr D u)) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
  proof (intro ballI)
    fix u
    assume u_managed: "u \<in> managed"
    fix lp
    assume lp_root: "lp \<in> roots"
    show
      "generic_item_raw_ptr D u \<in> set (ring (?raw' lp)) \<longleftrightarrow>
       pvContainer_C (h_val ?h' (generic_item_raw_ptr D u)) =
         PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    proof
      assume post_member:
        "generic_item_raw_ptr D u \<in> set (ring (?raw' lp))"
      have raw_managed:
        "generic_item_raw_ptr D u \<in> generic_item_raw_set managed D"
        using u_managed by (auto simp: generic_item_raw_set_def)
      have in_domain:
        "generic_item_raw_ptr D u \<in>
           generic_item_raw_set managed D \<inter> set (ring (?raw' lp))"
        using raw_managed post_member by (rule IntI)
      have at_root:
        "\<forall>q\<in>generic_item_raw_set managed D \<inter>
             set (ring (?raw' lp)).
           pvContainer_C (h_val ?h' q) =
             PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
        by (rule bspec[OF faithful_live_owner lp_root])
      show
        "pvContainer_C (h_val ?h' (generic_item_raw_ptr D u)) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
        by (rule bspec[OF at_root in_domain])
    next
      assume post_container:
        "pvContainer_C (h_val ?h' (generic_item_raw_ptr D u)) =
           PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      show "generic_item_raw_ptr D u \<in> set (ring (?raw' lp))"
      proof (cases "u = t")
        case True
        have ptr_eq: "generic_item_raw_ptr D u = ?p"
          using True by simp
        have null:
          "pvContainer_C (h_val ?h' (generic_item_raw_ptr D u)) = NULL"
          using removed_null ptr_eq by simp
        have raw: "raw_xlist_rel h lp (raw_fam lp)"
          by (rule GenericRootFamilyCoverage_raw_rootD[OF coverage lp_root])
        have guard: "c_guard lp"
          using raw by (simp add: raw_xlist_rel_def raw_xlist_layout_def)
        have root_not_null:
          "PTR_COERCE(xLIST_C \<rightarrow> unit) lp \<noteq> NULL"
        proof -
          have "lp \<noteq> NULL" by (rule c_guard_NULL[OF guard])
          then show ?thesis by simp
        qed
        have coerced_null:
          "PTR_COERCE(xLIST_C \<rightarrow> unit) lp = NULL"
          by (rule trans[OF sym[OF post_container] null])
        show ?thesis using root_not_null coerced_null by contradiction
      next
        case False
        have decode_u:
          "sd_node_decode D (generic_item_raw_ptr D u) = Some (Generic u)"
          by (rule GenericRootFamilyCoverage_generic_decodeD[
                OF coverage u_managed])
        have decode_t:
          "sd_node_decode D ?p = Some (Generic t)"
          by (rule GenericRootFamilyCoverage_generic_decodeD[
                OF coverage task])
        have pointer_ne: "generic_item_raw_ptr D u \<noteq> ?p"
        proof
          assume equal: "generic_item_raw_ptr D u = ?p"
          have decode_eq:
            "sd_node_decode D (generic_item_raw_ptr D u) =
             sd_node_decode D ?p"
            by (rule arg_cong[OF equal])
          have some_to_p:
            "Some (Generic u) = sd_node_decode D ?p"
            by (rule trans[OF sym[OF decode_u] decode_eq])
          have some_eq: "Some (Generic u) = Some (Generic t)"
            by (rule trans[OF some_to_p decode_t])
          have node_eq: "Generic u = Generic t"
            using some_eq by (simp only: option.inject)
          have tid_eq: "u = t"
            using node_eq by (simp only: node_kind.inject)
          show False using False tid_eq by contradiction
        qed
        have raw_managed:
          "generic_item_raw_ptr D u \<in> generic_item_raw_set managed D"
          using u_managed by (auto simp: generic_item_raw_set_def)
        have member_same:
          "generic_item_raw_ptr D u \<in> set (ring (?raw' lp)) \<longleftrightarrow>
           generic_item_raw_ptr D u \<in> set (ring (raw_fam lp))"
          by (rule membership_frame[
                OF lp_root raw_managed pointer_ne])
        have container_same:
          "pvContainer_C (h_val ?h' (generic_item_raw_ptr D u)) =
           pvContainer_C (h_val h (generic_item_raw_ptr D u))"
          by (rule container_frame[OF raw_managed pointer_ne])
        have old_iff:
          "generic_item_raw_ptr D u \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
           pvContainer_C (h_val h (generic_item_raw_ptr D u)) =
             PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          by (rule GenericRootFamilyCoverage_container_iff[
                OF coverage u_managed lp_root])
        have old_container:
          "pvContainer_C (h_val h (generic_item_raw_ptr D u)) =
             PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          by (rule trans[OF sym[OF container_same] post_container])
        have old_member:
          "generic_item_raw_ptr D u \<in> set (ring (raw_fam lp))"
          by (rule iffD2[OF old_iff old_container])
        show ?thesis by (rule iffD2[OF member_same old_member])
      qed
    qed
  qed
  have container_post:
    "generic_family_container_rep D ?h' roots ?raw' managed"
    using faithful_post pointwise_container_post
    by (simp add: generic_family_container_rep_def)
  have abstract_keys_post:
    "\<forall>lp\<in>roots. \<forall>u\<in>managed.
       Generic u \<in> set (ring (?abs' lp)) \<longrightarrow>
       item_key (?abs' lp) (Generic u) = K_G u"
  proof (intro ballI impI)
    fix lp
    assume lp_root: "lp \<in> roots"
    fix u
    assume u_managed: "u \<in> managed"
      and abstract_member: "Generic u \<in> set (ring (?abs' lp))"
    have labels:
      "xlist_relabel (sd_node_decode D) (?raw' lp) (?abs' lp)"
      using relabel_post lp_root by blast
    obtain q where raw_member: "q \<in> set (ring (?raw' lp))"
      and decode: "sd_node_decode D q = Some (Generic u)"
      using xlist_relabel_decoder_right_closed[
        OF labels abstract_member] by blast
    have q_eq: "q = generic_item_raw_ptr D u"
      using universal_node_decode_Generic_iff[
          OF laws, where p=q and t=u]
        decode u_managed
      by (simp add: generic_item_raw_ptr_def)
    have raw_rel: "raw_xlist_rel ?h' lp (?raw' lp)"
      using pre_post lp_root
      by (auto simp: scheduler_family_pre_rel_def raw_family_rel_def)
    have raw_key:
      "item_key (?raw' lp) q = raw_key_at ?h' q"
      using raw_rel raw_member
      by (auto simp: raw_xlist_rel_def raw_xlist_view_def)
    have relabel_key:
      "item_key (?raw' lp) q = item_key (?abs' lp) (Generic u)"
      using labels raw_member decode
      by (auto simp: xlist_relabel_def)
    have physical_key:
      "raw_key_at ?h' (generic_item_raw_ptr D u) = K_G u"
      using physical_keys_post u_managed by blast
    show "item_key (?abs' lp) (Generic u) = K_G u"
      using raw_key relabel_key physical_key q_eq by simp
  qed
  have key_post:
    "generic_family_key_rep D ?h' roots ?raw' ?abs' managed K_G"
    using physical_keys_post abstract_keys_post
    by (simp add: generic_family_key_rep_def)

  show ?thesis
    by (rule GenericRootFamilyCoverageI[
          OF universe pre_post laws root_rep_post container_post key_post])
qed

end
