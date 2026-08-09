theory Scheduler_Due_Prefix_Strong_Generated_Terminal_Contracts
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Terminal_Empty_Result.Scheduler_Due_Prefix_Strong_Terminal_Empty_Result"
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_Terminal_Future_Source.Scheduler_Due_Prefix_Strong_Terminal_Future_Source"
    Scheduler_Due_Prefix_Strong_Generated_Index
begin

text \<open>
  Shared last-due contract used by the arbitrary-list induction.  The two
  branches mirror the generated control flow exactly:

    * an empty future suffix makes the last body return NULL and the next
      while guard fail;
    * a nonempty future suffix makes the last body return its head pointer and
      the next body throw Exn () before changing the state.

  Each branch quantifies one last-head Gate-H package.  Its weak generated
  terminal evidence and its strong whole-scheduler endpoint are tied to the
  same C, branch, snapshot, raw families and concrete before-state.  K_G and
  K_E are parameters, so the contract cannot replace them at the terminal
  join.
\<close>

definition due_prefix_strong_generated_terminal_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid list \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_strong_generated_terminal_post D now entry all_due future
       managed termination external K_G K_E r t \<longleftrightarrow>
     (case future of
        [] \<Rightarrow>
          (\<exists>processed task C branch S generic_raw event_raw before.
            all_due = processed @ [Generic task] \<and>
            r = Result NULL \<and>
            DueLoopSharedLastEmptyEndpoint D now entry processed task C
              branch S generic_raw event_raw K_G K_E managed termination
              external before t)
      | f # fs \<Rightarrow>
          (\<exists>processed task C branch S generic_raw event_raw before.
            all_due = processed @ [Generic task] \<and>
            r = Exn () \<and>
            DueLoopStrongTerminalFutureState D now entry processed task f fs
              C branch S generic_raw event_raw K_G K_E managed termination
              external before t \<and>
            due_prefix_generated_terminal_post D now entry all_due
              (f # fs) (Exn ()) t))"

definition due_prefix_strong_generated_terminal_head_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid list \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_strong_generated_terminal_head_post D now entry all_due future
       managed termination external K_G K_E t \<longleftrightarrow>
     (\<exists>pxTCB generic_raw event_raw S.
       StrongDuePrefixLoopHeadRel D t
         (due_prefix_fold_state entry all_due)
         managed termination external
         generic_raw (ods_generic_family S)
         event_raw (ods_event_family S) K_G K_E S
         now entry all_due [] (map Generic future)
         (due_prefix_exit_phase_of [] (map Generic future))
         (due_prefix_next_node_of [] (map Generic future)) pxTCB)"

definition due_prefix_strong_generated_complete_public_post ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid list \<Rightarrow> 'tid list \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> 'tid set \<Rightarrow>
   'tid node_ring \<Rightarrow> xLIST_C ptr set \<Rightarrow>
   ('tid \<Rightarrow> 32 word) \<Rightarrow> ('tid \<Rightarrow> 32 word) \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "due_prefix_strong_generated_complete_public_post D now entry due_tasks
       future before managed termination external K_G K_E t \<longleftrightarrow>
     due_prefix_generated_complete_public_post D now entry due_tasks future
       before t \<and>
     due_prefix_strong_generated_terminal_head_post D now entry
       (map Generic due_tasks) future managed termination external K_G K_E t"

lemma due_prefix_strong_generated_terminal_post_legacyD:
  assumes terminal:
    "due_prefix_strong_generated_terminal_post D now entry all_due future
       managed termination external K_G K_E r t"
  shows
    "due_prefix_generated_terminal_post D now entry all_due future r t"
proof (cases future)
  case Nil
  obtain processed task C branch S generic_raw event_raw before where
      ledger: "all_due = processed @ [Generic task]"
    and result: "r = Result NULL"
    and endpoint:
      "DueLoopSharedLastEmptyEndpoint D now entry processed task C branch S
        generic_raw event_raw K_G K_E managed termination external before t"
    using terminal Nil
    by (auto simp: due_prefix_strong_generated_terminal_post_def)
  have legacy:
    "due_prefix_generated_terminal_post D now entry
       (processed @ [Generic task]) [] (Result NULL) t"
  proof -
    note endpoint0 =
      endpoint[unfolded DueLoopSharedLastEmptyEndpoint_def Let_def]
    note endpoint1 = conjunct2[OF endpoint0]
    note endpoint2 = conjunct2[OF endpoint1]
    note endpoint3 = conjunct2[OF endpoint2]
    note endpoint4 = conjunct2[OF endpoint3]
    show ?thesis by (rule conjunct1[OF endpoint4])
  qed
  show ?thesis using legacy ledger result Nil by simp
next
  case (Cons f fs)
  show ?thesis
    using terminal Cons
    by (auto simp: due_prefix_strong_generated_terminal_post_def)
qed

lemma due_prefix_strong_generated_terminal_post_controlD:
  assumes terminal:
    "due_prefix_strong_generated_terminal_post D now entry all_due future
       managed termination external K_G K_E r t"
  shows
    "(future = [] \<and> r = Result NULL) \<or>
     (\<exists>f fs. future = f # fs \<and> r = Exn ())"
  using terminal
  by (cases future)
     (auto simp: due_prefix_strong_generated_terminal_post_def)

lemma due_prefix_strong_generated_terminal_post_headD:
  assumes terminal:
    "due_prefix_strong_generated_terminal_post D now entry all_due future
       managed termination external K_G K_E r t"
  shows
    "due_prefix_strong_generated_terminal_head_post D now entry all_due
       future managed termination external K_G K_E t"
proof (cases future)
  case Nil
  obtain processed task C branch S generic_raw event_raw before where
      ledger: "all_due = processed @ [Generic task]"
    and endpoint:
      "DueLoopSharedLastEmptyEndpoint D now entry processed task C branch S
        generic_raw event_raw K_G K_E managed termination external before t"
    using terminal Nil
    by (auto simp: due_prefix_strong_generated_terminal_post_def)
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' before)"
  let ?hg = "one_due_generic_remove_heap D C ?h0"
  let ?he = "one_due_event_remove_heap D C branch ?hg"
  let ?generic_raw' =
    "one_due_reentry_generic_raw D C ?he generic_raw"
  let ?event_raw' =
    "one_due_event_raw_after_remove D C branch event_raw"
  let ?S' = "one_due_reentry_snapshot C branch S"
  have strong:
    "StrongDuePrefixLoopHeadRel D t
       (due_prefix_result_step_abs entry processed (Generic task))
       managed termination external
       ?generic_raw' (ods_generic_family ?S')
       ?event_raw' (ods_event_family ?S') K_G K_E ?S'
       now entry (processed @ [Generic task]) [] []
       EmptyExit None NULL"
  proof -
    note endpoint0 =
      endpoint[unfolded DueLoopSharedLastEmptyEndpoint_def Let_def]
    note endpoint1 = conjunct2[OF endpoint0]
    note endpoint2 = conjunct2[OF endpoint1]
    note endpoint3 = conjunct2[OF endpoint2]
    note endpoint4 = conjunct2[OF endpoint3]
    note endpoint5 = conjunct2[OF endpoint4]
    show ?thesis by (rule conjunct2[OF endpoint5])
  qed
  have fold:
    "due_prefix_result_step_abs entry processed (Generic task) =
       due_prefix_fold_state entry all_due"
    using ledger by (simp add: due_prefix_result_step_abs_def)
  show ?thesis
    unfolding due_prefix_strong_generated_terminal_head_post_def
    apply (rule exI[where x=NULL])
    apply (rule exI[where x = "?generic_raw'"])
    apply (rule exI[where x = "?event_raw'"])
    apply (rule exI[where x = "?S'"])
    using strong fold ledger Nil by simp
next
  case (Cons f fs)
  obtain processed task C branch S generic_raw event_raw before where
      ledger: "all_due = processed @ [Generic task]"
    and state:
      "DueLoopStrongTerminalFutureState D now entry processed task f fs C
        branch S generic_raw event_raw K_G K_E managed termination external
        before t"
    using terminal Cons
    by (auto simp: due_prefix_strong_generated_terminal_post_def)
  let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' before)"
  let ?hg = "one_due_generic_remove_heap D C ?h0"
  let ?he = "one_due_event_remove_heap D C branch ?hg"
  let ?generic_raw' =
    "one_due_reentry_generic_raw D C ?he generic_raw"
  let ?event_raw' =
    "one_due_event_raw_after_remove D C branch event_raw"
  let ?S' = "one_due_reentry_snapshot C branch S"
  have strong:
    "StrongDuePrefixLoopHeadRel D t
       (due_prefix_result_step_abs entry processed (Generic task))
       managed termination external
       ?generic_raw' (ods_generic_family ?S')
       ?event_raw' (ods_event_family ?S') K_G K_E ?S'
       now entry (processed @ [Generic task]) []
       (Generic f # map Generic fs)
       FutureExit (Some (Generic f)) (sd_tcb_ptr D f)"
  proof -
    note state0 =
      state[unfolded DueLoopStrongTerminalFutureState_def Let_def]
    note state1 = conjunct2[OF state0]
    show ?thesis by (rule conjunct1[OF state1])
  qed
  have fold:
    "due_prefix_result_step_abs entry processed (Generic task) =
       due_prefix_fold_state entry all_due"
    using ledger by (simp add: due_prefix_result_step_abs_def)
  show ?thesis
    unfolding due_prefix_strong_generated_terminal_head_post_def
    apply (rule exI[where x="sd_tcb_ptr D f"])
    apply (rule exI[where x = "?generic_raw'"])
    apply (rule exI[where x = "?event_raw'"])
    apply (rule exI[where x = "?S'"])
    using strong fold ledger Cons by simp
qed

lemma due_prefix_strong_generated_terminal_post_publicD:
  assumes nonempty: "due_tasks \<noteq> []"
    and ledger: "all_due = map Generic due_tasks"
    and terminal:
      "due_prefix_strong_generated_terminal_post D now entry all_due future
         managed termination external K_G K_E r t"
  shows
    "due_prefix_strong_generated_complete_public_post D now entry due_tasks
       future before managed termination external K_G K_E t"
proof -
  have legacy:
    "due_prefix_generated_terminal_post D now entry
       (map Generic due_tasks) future r t"
    using due_prefix_strong_generated_terminal_post_legacyD[OF terminal]
      ledger by simp
  have weak:
    "due_prefix_generated_complete_public_post D now entry due_tasks future
       before t"
  proof -
    obtain task tail where tasks: "due_tasks = task # tail"
      using nonempty by (cases due_tasks) auto
    show ?thesis
      unfolding due_prefix_generated_complete_public_post_def
      apply (rule exI[where x=r])
      using legacy tasks
      by (simp add: due_prefix_generated_complete_terminal_post_def)
  qed
  have head:
    "due_prefix_strong_generated_terminal_head_post D now entry
       (map Generic due_tasks) future managed termination external K_G K_E t"
    using due_prefix_strong_generated_terminal_post_headD[OF terminal]
      ledger by simp
  show ?thesis
    using weak head
    by (simp add: due_prefix_strong_generated_complete_public_post_def)
qed

lemma due_prefix_strong_generated_complete_public_post_oldD:
  assumes exact:
    "due_prefix_strong_generated_complete_public_post D now entry due_tasks
       future before managed termination external K_G K_E t"
  shows
    "strong_due_prefix_generated_complete_public_post D now entry due_tasks
       future before managed termination external t"
proof -
  have weak:
    "due_prefix_generated_complete_public_post D now entry due_tasks future
       before t"
    and head:
      "due_prefix_strong_generated_terminal_head_post D now entry
        (map Generic due_tasks) future managed termination external K_G K_E t"
    using exact
    by (simp_all add: due_prefix_strong_generated_complete_public_post_def)
  obtain pxTCB generic_raw event_raw S where strong:
    "StrongDuePrefixLoopHeadRel D t
       (due_prefix_fold_state entry (map Generic due_tasks))
       managed termination external
       generic_raw (ods_generic_family S)
       event_raw (ods_event_family S) K_G K_E S
       now entry (map Generic due_tasks) [] (map Generic future)
       (due_prefix_exit_phase_of [] (map Generic future))
       (due_prefix_next_node_of [] (map Generic future)) pxTCB"
    using head
    by (auto simp: due_prefix_strong_generated_terminal_head_post_def)
  have old_head:
    "StrongDuePrefixGeneratedLoopHeadPost D t
       (due_prefix_fold_state entry (map Generic due_tasks))
       managed termination external now entry
       (map Generic due_tasks) [] (map Generic future) pxTCB"
    unfolding StrongDuePrefixGeneratedLoopHeadPost_def
    apply (rule exI[where x=
      "due_prefix_exit_phase_of [] (map Generic future)"])
    apply (rule exI[where x=
      "due_prefix_next_node_of [] (map Generic future)"])
    apply (rule exI[where x=generic_raw])
    apply (rule exI[where x="ods_generic_family S"])
    apply (rule exI[where x=event_raw])
    apply (rule exI[where x="ods_event_family S"])
    apply (rule exI[where x=K_G])
    apply (rule exI[where x=K_E])
    apply (rule exI[where x=S])
    by (rule strong)
  show ?thesis
    unfolding strong_due_prefix_generated_complete_public_post_def
    apply (intro conjI)
    subgoal by (rule weak)
    apply (rule exI[where x=
      "due_prefix_fold_state entry (map Generic due_tasks)"])
    apply (rule exI[where x=pxTCB])
    by (rule old_head)
qed

end
