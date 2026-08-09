theory Scheduler_Due_Prefix_Managed_Arbitrary_While_Defs
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Managed_Gate_Nonlast_Capstone.Scheduler_Due_Prefix_Managed_Gate_Nonlast_Capstone"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Generated_While_Finally.Scheduler_Due_Prefix_Generated_While_Finally"
begin

text \<open>
  Managed-view induction package for an arbitrary finite due prefix.  The
  context, physical Event branch, shared snapshot and both raw families are
  quantified exactly once.  Consequently DueLoopStrongHeadRel and the local
  managed Gate-H relation cannot choose different representations of the
  same concrete heap.

  The total due ledger and processed prefix are explicit.  A normal body
  result therefore has only one possible successor index.  The managed
  domain, termination ring, protected external Event roots and total key
  observations remain parameters across the whole fold.
\<close>

definition due_prefix_managed_strong_generated_head_index ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow> 'tid list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "due_prefix_managed_strong_generated_head_index D R now entry all_due
       future processed task due_tail pxTCB c managed termination external
       K_G K_E \<longleftrightarrow>
     all_due = processed @ map Generic (task # due_tail) \<and>
     (\<exists>C branch S generic_raw event_raw.
       odc_task C = task \<and>
       pxTCB = sd_tcb_ptr D task \<and>
       DueLoopStrongHeadRel D c
         (due_prefix_fold_state entry processed)
         managed termination external
         generic_raw (ods_generic_family S)
         event_raw (ods_event_family S) K_G K_E S
         now entry processed (map Generic (task # due_tail))
         (map Generic future) DueGate (Some (Generic task)) pxTCB \<and>
       due_prefix_managed_gate_inv D R c now entry processed
         (map Generic (task # due_tail)) (map Generic future)
         (due_prefix_fold_state entry processed) managed
         C branch S generic_raw event_raw)"

text \<open>
  Unified external entry.  The zero-due branch is a stable strong snapshot
  and deliberately has no Gate-H witness.  A nonempty branch carries one
  shared managed-view package; the canonical constructor proved in the next
  theory manufactures that package from Strong plus the generated roots.
\<close>

definition ManagedStrongDuePrefixGeneratedEntryRel ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.tskTaskControlBlock_C ptr \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow> bool"
where
  "ManagedStrongDuePrefixGeneratedEntryRel D R c now entry due_tasks
       future pxTCB managed termination external K_G K_E \<longleftrightarrow>
     (case due_tasks of
        [] \<Rightarrow>
          (\<exists>S generic_raw event_raw.
            StrongDuePrefixLoopHeadRel D c entry managed termination external
              generic_raw (ods_generic_family S)
              event_raw (ods_event_family S) K_G K_E S
              now entry [] [] (map Generic future)
              (due_prefix_exit_phase_of [] (map Generic future))
              (due_prefix_next_node_of [] (map Generic future)) pxTCB)
      | task # due_tail \<Rightarrow>
          (\<exists>C branch S generic_raw event_raw.
            odc_task C = task \<and>
            pxTCB = sd_tcb_ptr D task \<and>
            DueLoopStrongHeadRel D c entry managed termination external
              generic_raw (ods_generic_family S)
              event_raw (ods_event_family S) K_G K_E S
              now entry [] (map Generic (task # due_tail))
              (map Generic future) DueGate (Some (Generic task)) pxTCB \<and>
            due_prefix_managed_gate_inv D R c now entry []
              (map Generic (task # due_tail)) (map Generic future)
              entry managed C branch S generic_raw event_raw))"

text \<open>
  Stable zero-due public closure.  The generated control theorem records its
  own exact zero post, while the second conjunct retains a whole-scheduler
  Strong head over the unchanged state.  No successor postcondition is an
  assumption of this definition or of its eventual theorem.
\<close>

definition due_prefix_managed_generated_zero_strong_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_managed_generated_zero_strong_post D now entry future before
       managed termination external K_G K_E t \<longleftrightarrow>
     t = before \<and>
     due_prefix_generated_zero_public_post D now entry future before t \<and>
     (\<exists>pxTCB S generic_raw event_raw.
       StrongDuePrefixLoopHeadRel D t entry managed termination external
         generic_raw (ods_generic_family S)
         event_raw (ods_event_family S) K_G K_E S
         now entry [] [] (map Generic future)
         (due_prefix_exit_phase_of [] (map Generic future))
         (due_prefix_next_node_of [] (map Generic future)) pxTCB)"

end
