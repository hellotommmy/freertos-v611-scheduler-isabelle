theory Scheduler_Due_Prefix_Strong_Result_Event_Semantics
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Result_Shared_Defs.Scheduler_Due_Prefix_Strong_Result_Shared_Defs"
begin

text \<open>
  The physical Event branch needs one semantic interpretation before it can
  update the scheduler-level waiting set.  In the linked case the selected
  task occurs at exactly one root of the complete Event universe; in the NULL
  case it occurs at none.  The linked owner is external (hence is not the
  distinguished pending root), and its abstract ring is duplicate-free.

  This is an entry-state fact.  It is derivable from total Event coverage and
  the checked physical branch; it is not a premise about a desired poststate.
\<close>

definition one_due_event_branch_abstract_semantics ::
  "xLIST_C ptr set \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_context \<Rightarrow>
   ('tid, xLIST_C ptr) one_due_snapshot \<Rightarrow>
   xLIST_C ptr one_due_event_branch \<Rightarrow> bool"
where
  "one_due_event_branch_abstract_semantics external C S branch \<longleftrightarrow>
     (case branch of
        DueEventLinked owner \<Rightarrow>
          owner \<in> external \<and>
          owner \<noteq> GeneratedPendingEventRoot \<and>
          distinct (ring (ods_event_family S owner)) \<and>
          (\<forall>lp\<in>EventRootUniverse external.
             (Event (odc_task C) \<in>
                set (ring (ods_event_family S lp))) = (lp = owner))
      | DueEventNull \<Rightarrow>
          (\<forall>lp\<in>EventRootUniverse external.
             Event (odc_task C) \<notin>
               set (ring (ods_event_family S lp))))"

lemma EventRootFamilyCoverage_linked_branch_abstract_semantics:
  assumes coverage:
      "EventRootFamilyCoverage external D h event_raw
         (ods_event_family S) managed K_E"
    and task: "odc_task C \<in> managed"
    and owner: "owner \<in> external"
    and member:
      "event_item_raw_ptr D (odc_task C) \<in>
         set (ring (event_raw owner))"
  shows
    "one_due_event_branch_abstract_semantics external C S
       (DueEventLinked owner)"
proof -
  have rel:
    "scheduler_event_root_family_rel D h
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw (ods_event_family S) managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF coverage])
  have owner_root: "owner \<in> EventRootUniverse external"
    by (rule EventRootUniverse_externalI[OF owner])
  have unique:
    "raw_family_members (EventRootUniverse external) event_raw
       (event_item_raw_ptr D (odc_task C)) = {owner}"
    by (rule scheduler_event_root_family_member_singletonD[
          OF rel owner_root member])
  have owner_wf: "xlist_wf (ods_event_family S owner)"
    by (rule scheduler_event_root_family_abs_wfD[OF rel owner_root])
  have owner_not_pending: "owner \<noteq> GeneratedPendingEventRoot"
    using EventRootFamilyCoverage_external_wfD[OF coverage] owner
    by (auto simp: EventExternalRootInputWF_def)
  have exact:
    "\<forall>lp\<in>EventRootUniverse external.
       (Event (odc_task C) \<in>
          set (ring (ods_event_family S lp))) = (lp = owner)"
  proof (intro ballI)
    fix lp
    assume lp: "lp \<in> EventRootUniverse external"
    have member_iff:
      "event_item_raw_ptr D (odc_task C) \<in>
          set (ring (event_raw lp)) \<longleftrightarrow>
       Event (odc_task C) \<in>
          set (ring (ods_event_family S lp))"
      by (rule scheduler_event_root_family_member_iff[OF rel task lp])
    have raw_iff:
      "event_item_raw_ptr D (odc_task C) \<in>
          set (ring (event_raw lp)) \<longleftrightarrow> lp = owner"
      using unique lp by (auto simp: raw_family_members_def)
    show
      "(Event (odc_task C) \<in>
          set (ring (ods_event_family S lp))) = (lp = owner)"
      using member_iff raw_iff by blast
  qed
  show ?thesis
    using owner owner_not_pending owner_wf exact
    by (simp add: one_due_event_branch_abstract_semantics_def
        xlist_wf_def)
qed

lemma EventRootFamilyCoverage_null_branch_abstract_semantics:
  assumes coverage:
      "EventRootFamilyCoverage external D h event_raw
         (ods_event_family S) managed K_E"
    and task: "odc_task C \<in> managed"
    and absent:
      "raw_family_members (EventRootUniverse external) event_raw
         (event_item_raw_ptr D (odc_task C)) = {}"
  shows
    "one_due_event_branch_abstract_semantics external C S DueEventNull"
proof -
  have rel:
    "scheduler_event_root_family_rel D h
       (EventRootUniverse external) GeneratedPendingEventRoot
       event_raw (ods_event_family S) managed K_E"
    by (rule EventRootFamilyCoverage_relD[OF coverage])
  have exact:
    "\<forall>lp\<in>EventRootUniverse external.
       Event (odc_task C) \<notin>
         set (ring (ods_event_family S lp))"
  proof (intro ballI)
    fix lp
    assume lp: "lp \<in> EventRootUniverse external"
    have raw_absent:
      "event_item_raw_ptr D (odc_task C) \<notin>
         set (ring (event_raw lp))"
      using absent lp by (auto simp: raw_family_members_def)
    show
      "Event (odc_task C) \<notin>
         set (ring (ods_event_family S lp))"
      using scheduler_event_root_family_member_iff[OF rel task lp]
        raw_absent by blast
  qed
  show ?thesis
    using exact
    by (simp add: one_due_event_branch_abstract_semantics_def)
qed

lemma one_due_full_family_cutpoints_branch_abstract_semantics:
  assumes families:
      "one_due_full_family_cutpoints external D managed C S h
         generic_raw event_raw branch"
    and task: "odc_task C \<in> managed"
  shows
    "one_due_event_branch_abstract_semantics external C S branch"
proof -
  let ?hg = "one_due_generic_remove_heap D C h"
  have coverage:
    "EventRootFamilyCoverage external D ?hg event_raw
       (ods_event_family S) managed (ods_event_payload S)"
    using families
    by (simp add: one_due_full_family_cutpoints_def Let_def)
  have witness:
    "one_due_family_branch_witness D C ?hg event_raw external branch"
    using families
    by (simp add: one_due_full_family_cutpoints_def Let_def)
  show ?thesis
  proof (cases branch)
    case (DueEventLinked owner)
    have owner_external: "owner \<in> external"
      and member:
        "event_item_raw_ptr D (odc_task C) \<in>
           set (ring (event_raw owner))"
      using witness DueEventLinked
      by (simp_all add: one_due_family_branch_witness_def)
    show ?thesis
      using EventRootFamilyCoverage_linked_branch_abstract_semantics[
        OF coverage task owner_external member]
        DueEventLinked by simp
  next
    case DueEventNull
    have absent:
      "raw_family_members (EventRootUniverse external) event_raw
         (event_item_raw_ptr D (odc_task C)) = {}"
      using witness DueEventNull
      by (simp add: one_due_family_branch_witness_def)
    show ?thesis
      using EventRootFamilyCoverage_null_branch_abstract_semantics[
        OF coverage task absent]
        DueEventNull by simp
  qed
qed

lemma one_due_event_branch_external_union:
  assumes semantics:
    "one_due_event_branch_abstract_semantics external C S branch"
  shows
    "Collect (\<lambda>t. \<exists>lp\<in>external.
        Event t \<in> set (ring
          (one_due_event_abs_after_remove C branch S lp))) =
     Collect (\<lambda>t. \<exists>lp\<in>external.
        Event t \<in> set (ring (ods_event_family S lp))) -
       {odc_task C}"
proof (cases branch)
  case (DueEventLinked owner)
  have owner: "owner \<in> external"
    and distinct_owner:
      "distinct (ring (ods_event_family S owner))"
    and exact:
      "\<forall>lp\<in>EventRootUniverse external.
        (Event (odc_task C) \<in>
           set (ring (ods_event_family S lp))) = (lp = owner)"
    using semantics DueEventLinked
    by (simp_all add: one_due_event_branch_abstract_semantics_def)
  show ?thesis
  proof (rule set_eqI)
    fix t
    show
      "t \<in> Collect (\<lambda>u. \<exists>lp\<in>external.
          Event u \<in> set (ring
            (one_due_event_abs_after_remove C branch S lp))) \<longleftrightarrow>
       t \<in> Collect (\<lambda>u. \<exists>lp\<in>external.
          Event u \<in> set (ring (ods_event_family S lp))) -
             {odc_task C}"
    proof (cases "t = odc_task C")
      case True
      have post_absent:
        "\<forall>lp\<in>external.
          Event (odc_task C) \<notin> set (ring
            (one_due_event_abs_after_remove C branch S lp))"
      proof (intro ballI)
        fix lp
        assume lp_external: "lp \<in> external"
        have lp_root: "lp \<in> EventRootUniverse external"
          by (rule EventRootUniverse_externalI[OF lp_external])
        show
          "Event (odc_task C) \<notin> set (ring
            (one_due_event_abs_after_remove C branch S lp))"
        proof (cases "lp = owner")
          case True
          show ?thesis
            using distinct_owner DueEventLinked True
            by (simp add: one_due_event_abs_after_remove_def
                event_remove_abs_family_def list_remove_abs_def
                set_remove1_eq)
        next
          case False
          have old_absent:
            "Event (odc_task C) \<notin>
               set (ring (ods_event_family S lp))"
            using exact lp_root False by blast
          show ?thesis
            using old_absent DueEventLinked False
            by (simp add: one_due_event_abs_after_remove_def
                event_remove_abs_family_def)
        qed
      qed
      show ?thesis using True post_absent by simp
    next
      case False
      have frame:
        "\<And>lp. Event t \<in> set (ring
            (one_due_event_abs_after_remove C branch S lp)) \<longleftrightarrow>
          Event t \<in> set (ring (ods_event_family S lp))"
        using event_remove_abs_family_membership_frame[OF False]
          DueEventLinked
        by (simp add: one_due_event_abs_after_remove_def)
      show ?thesis using False frame by auto
    qed
  qed
next
  case DueEventNull
  have absent:
    "\<forall>lp\<in>EventRootUniverse external.
       Event (odc_task C) \<notin>
         set (ring (ods_event_family S lp))"
    using semantics DueEventNull
    by (simp add: one_due_event_branch_abstract_semantics_def)
  have task_not_waiting:
    "odc_task C \<notin>
       Collect (\<lambda>t. \<exists>lp\<in>external.
          Event t \<in> set (ring (ods_event_family S lp)))"
    using absent by (auto intro: EventRootUniverse_externalI)
  show ?thesis
    using DueEventNull task_not_waiting
    by (simp add: one_due_event_abs_after_remove_def)
qed

lemma one_due_event_branch_retired_absence:
  assumes semantics:
      "one_due_event_branch_abstract_semantics external C S branch"
    and old_absence:
      "\<forall>t\<in>managed - sa_live before.
        \<forall>lp\<in>EventRootUniverse external.
          Event t \<notin> set (ring (ods_event_family S lp))"
    and live: "sa_live after = sa_live before"
    and task_live: "odc_task C \<in> sa_live before"
  shows
    "\<forall>t\<in>managed - sa_live after.
      \<forall>lp\<in>EventRootUniverse external.
        Event t \<notin> set (ring
          (one_due_event_abs_after_remove C branch S lp))"
proof (intro ballI)
  fix t lp
  assume retired: "t \<in> managed - sa_live after"
    and root: "lp \<in> EventRootUniverse external"
  have old_retired: "t \<in> managed - sa_live before"
    using retired live by simp
  have old: "Event t \<notin> set (ring (ods_event_family S lp))"
    by (rule old_absence[rule_format, OF old_retired root])
  have different: "t \<noteq> odc_task C"
    using retired live task_live by auto
  show
    "Event t \<notin> set (ring
      (one_due_event_abs_after_remove C branch S lp))"
    using old event_remove_abs_family_membership_frame[OF different]
    by (cases branch)
       (simp_all add: one_due_event_abs_after_remove_def)
qed

lemma strong_event_role_projection_one_due_reentry:
  assumes role:
      "strong_event_role_projection before managed external
         (ods_event_family S)"
    and semantics:
      "one_due_event_branch_abstract_semantics external C S branch"
    and frame: "due_prefix_abstract_control_frame before after"
    and waiting:
      "sa_event_waiting after =
         sa_event_waiting before - {odc_task C}"
    and task_live: "odc_task C \<in> sa_live before"
  shows
    "strong_event_role_projection after managed external
       (ods_event_family (one_due_reentry_snapshot C branch S))"
proof -
  have post_family:
    "ods_event_family (one_due_reentry_snapshot C branch S) =
       one_due_event_abs_after_remove C branch S"
    by (rule sym, rule one_due_event_abs_after_remove_is_reentry)
  have pending_owner_frame:
    "one_due_event_abs_after_remove C branch S GeneratedPendingEventRoot =
       ods_event_family S GeneratedPendingEventRoot"
  proof (cases branch)
    case (DueEventLinked owner)
    have owner_ne: "owner \<noteq> GeneratedPendingEventRoot"
      using semantics DueEventLinked
      by (simp add: one_due_event_branch_abstract_semantics_def)
    show ?thesis
      using DueEventLinked owner_ne
      by (simp add: one_due_event_abs_after_remove_def
          event_remove_abs_family_def)
  next
    case DueEventNull
    show ?thesis
      using DueEventNull
      by (simp add: one_due_event_abs_after_remove_def)
  qed
  have union:
    "Collect (\<lambda>t. \<exists>lp\<in>external.
        Event t \<in> set (ring
          (one_due_event_abs_after_remove C branch S lp))) =
     sa_event_waiting after"
    using one_due_event_branch_external_union[OF semantics]
      role waiting
    by (simp add: strong_event_role_projection_def)
  have live: "sa_live after = sa_live before"
    using frame by (simp add: due_prefix_abstract_control_frame_def)
  have retired:
    "\<forall>t\<in>managed - sa_live after.
      \<forall>lp\<in>EventRootUniverse external.
        Event t \<notin> set (ring
          (one_due_event_abs_after_remove C branch S lp))"
  proof (rule one_due_event_branch_retired_absence[
      OF semantics _ live task_live])
    show
      "\<forall>t\<in>managed - sa_live before.
        \<forall>lp\<in>EventRootUniverse external.
          Event t \<notin> set (ring (ods_event_family S lp))"
      using role
      by (simp add: strong_event_role_projection_def)
  qed
  show ?thesis
    using role frame pending_owner_frame union retired post_family
    by (simp add: strong_event_role_projection_def
        due_prefix_abstract_control_frame_def)
qed

corollary one_due_full_family_cutpoints_event_role_projection:
  assumes families:
      "one_due_full_family_cutpoints external D managed C S h
         generic_raw event_raw branch"
    and task_managed: "odc_task C \<in> managed"
    and role:
      "strong_event_role_projection before managed external
         (ods_event_family S)"
    and frame: "due_prefix_abstract_control_frame before after"
    and waiting:
      "sa_event_waiting after =
         sa_event_waiting before - {odc_task C}"
    and task_live: "odc_task C \<in> sa_live before"
  shows
    "strong_event_role_projection after managed external
       (ods_event_family (one_due_reentry_snapshot C branch S))"
proof -
  have semantics:
    "one_due_event_branch_abstract_semantics external C S branch"
    by (rule one_due_full_family_cutpoints_branch_abstract_semantics[
          OF families task_managed])
  show ?thesis
    by (rule strong_event_role_projection_one_due_reentry[
          OF role semantics frame waiting task_live])
qed

end
