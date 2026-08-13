theory Scheduler_Global_Coverage_Generic_Heap_Frame
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Generic_Root_Universe_Coverage_Core.Scheduler_Generic_Root_Universe_Coverage_Core"
    "EAL6_FreeRTOS_V611_Scheduler_Delay_Suspended_Core.Scheduler_Delay_Suspended_Core"
begin

text \<open>
  Whole-family Generic coverage observes the concrete list storage of every
  protected root and the complete Generic item of every managed task.  Equality
  on exactly those observations is therefore sufficient to move the relation
  to an arbitrary framed heap.  The root family, managed domain, decoder,
  abstract rings and total key observation remain universally quantified.
\<close>

theorem GenericRootFamilyCoverage_heap_frameI:
  assumes coverage:
      "GenericRootFamilyCoverage
         D h roots raw_fam abs_fam managed K_G"
    and root_frame:
      "\<And>lp address. lp \<in> roots \<Longrightarrow>
        address \<in> raw_xlist_storage lp (raw_fam lp) \<Longrightarrow>
        h' address = h address"
    and item_frame:
      "\<And>t. t \<in> managed \<Longrightarrow>
        h_val h' (generic_item_raw_ptr D t) =
          h_val h (generic_item_raw_ptr D t)"
  shows
    "GenericRootFamilyCoverage
       D h' roots raw_fam abs_fam managed K_G"
proof (rule GenericRootFamilyCoverageI)
  show "roots = GenericRootUniverse"
    by (rule GenericRootFamilyCoverage_universeD[OF coverage])
next
  have old_pre:
    "scheduler_family_pre_rel h roots raw_fam managed D"
    by (rule GenericRootFamilyCoverage_preD[OF coverage])
  have new_family: "raw_family_rel h' roots raw_fam"
    unfolding raw_family_rel_def
  proof (intro conjI ballI)
    show "finite roots"
      using old_pre
      by (simp add: scheduler_family_pre_rel_def raw_family_rel_def)
  next
    fix lp
    assume root: "lp \<in> roots"
    have old: "raw_xlist_rel h lp (raw_fam lp)"
      by (rule GenericRootFamilyCoverage_raw_rootD[OF coverage root])
    show "raw_xlist_rel h' lp (raw_fam lp)"
      by (rule delay_raw_xlist_rel_storage_frame[OF old])
         (use root root_frame in blast)
  qed
  show "scheduler_family_pre_rel h' roots raw_fam managed D"
    using old_pre new_family
    by (simp add: scheduler_family_pre_rel_def)
next
  show "universal_decoder_laws managed D"
    by (rule GenericRootFamilyCoverage_decoder_lawsD[OF coverage])
next
  fix lp
  assume root: "lp \<in> roots"
  show "generic_family_root_rep D raw_fam abs_fam managed lp"
    by (rule GenericRootFamilyCoverage_root_repD[OF coverage root])
next
  have old:
    "generic_family_container_rep D h roots raw_fam managed"
    by (rule GenericRootFamilyCoverage_container_repD[OF coverage])
  have old_faithful:
    "raw_family_container_faithful_on h roots raw_fam
       (generic_item_raw_set managed D)"
    using old by (simp add: generic_family_container_rep_def)
  have old_members:
    "\<And>t lp. t \<in> managed \<Longrightarrow> lp \<in> roots \<Longrightarrow>
      generic_item_raw_ptr D t \<in> set (ring (raw_fam lp)) \<longleftrightarrow>
      pvContainer_C (h_val h (generic_item_raw_ptr D t)) =
        PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
    using old by (auto simp: generic_family_container_rep_def)
  have point_frame:
    "\<And>p. p \<in> generic_item_raw_set managed D \<Longrightarrow>
      h_val h' p = h_val h p"
  proof -
    fix p
    assume managed_ptr: "p \<in> generic_item_raw_set managed D"
    then obtain t where task: "t \<in> managed"
        and p: "p = generic_item_raw_ptr D t"
      by (auto simp: generic_item_raw_set_def)
    show "h_val h' p = h_val h p"
      using item_frame[OF task] p by simp
  qed
  show "generic_family_container_rep D h' roots raw_fam managed"
    unfolding generic_family_container_rep_def
  proof (intro conjI)
    show
      "raw_family_container_faithful_on h' roots raw_fam
         (generic_item_raw_set managed D)"
      unfolding raw_family_container_faithful_on_def
    proof (intro conjI)
      show
        "\<forall>p\<in>generic_item_raw_set managed D.
          (pvContainer_C (h_val h' p) = NULL) =
            (raw_family_members roots raw_fam p = {})"
      proof (intro ballI)
        fix p
        assume managed_ptr: "p \<in> generic_item_raw_set managed D"
        have old_null:
          "(pvContainer_C (h_val h p) = NULL) =
            (raw_family_members roots raw_fam p = {})"
          using old_faithful managed_ptr
          by (simp add: raw_family_container_faithful_on_def)
        show
          "(pvContainer_C (h_val h' p) = NULL) =
            (raw_family_members roots raw_fam p = {})"
          using old_null point_frame[OF managed_ptr] by simp
      qed
    next
      show
        "\<forall>lp\<in>roots. \<forall>p\<in>generic_item_raw_set managed D \<inter>
          set (ring (raw_fam lp)).
          pvContainer_C (h_val h' p) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
      proof (intro ballI)
        fix lp
        assume root: "lp \<in> roots"
        fix p
        assume member:
          "p \<in> generic_item_raw_set managed D \<inter>
            set (ring (raw_fam lp))"
        have old_container:
          "pvContainer_C (h_val h p) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          using old_faithful root member
          by (auto simp: raw_family_container_faithful_on_def)
        show
          "pvContainer_C (h_val h' p) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp"
          using old_container point_frame[of p] member by auto
      qed
    qed
  next
    show
      "\<forall>t\<in>managed. \<forall>lp\<in>roots.
        (generic_item_raw_ptr D t \<in> set (ring (raw_fam lp))) =
          (pvContainer_C (h_val h' (generic_item_raw_ptr D t)) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"
    proof (intro ballI)
      fix t
      assume task: "t \<in> managed"
      fix lp
      assume root: "lp \<in> roots"
      show
        "(generic_item_raw_ptr D t \<in> set (ring (raw_fam lp))) =
          (pvContainer_C (h_val h' (generic_item_raw_ptr D t)) =
            PTR_COERCE(xLIST_C \<rightarrow> unit) lp)"
        using old_members[OF task root] item_frame[OF task] by simp
    qed
  qed
next
  have old:
    "generic_family_key_rep
       D h roots raw_fam abs_fam managed K_G"
    by (rule GenericRootFamilyCoverage_key_repD[OF coverage])
  show
    "generic_family_key_rep
       D h' roots raw_fam abs_fam managed K_G"
    unfolding generic_family_key_rep_def
  proof (intro conjI)
    show
      "\<forall>t\<in>managed. raw_key_at h' (generic_item_raw_ptr D t) = K_G t"
    proof (intro ballI)
      fix t
      assume task: "t \<in> managed"
      have old_key:
        "raw_key_at h (generic_item_raw_ptr D t) = K_G t"
        using old task by (simp add: generic_family_key_rep_def)
      show "raw_key_at h' (generic_item_raw_ptr D t) = K_G t"
        using old_key item_frame[OF task]
        by (simp add: raw_key_at_def)
    qed
  next
    show
      "\<forall>lp\<in>roots. \<forall>t\<in>managed.
        Generic t \<in> set (ring (abs_fam lp)) \<longrightarrow>
          item_key (abs_fam lp) (Generic t) = K_G t"
      using old by (simp add: generic_family_key_rep_def)
  qed
qed

end
