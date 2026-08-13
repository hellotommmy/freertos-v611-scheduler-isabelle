theory Scheduler_Delayed_Cursor_General_Terminal_Future_Bare
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Terminal_Future_Result.Scheduler_Delayed_Cursor_General_Terminal_Future_Result"
begin

text \<open>
  The last due body returns the symbolic future-head pointer.  The next body
  throws before its first write, so the exact cursor-general endpoint and all
  transformed family witnesses remain the same last-due poststate.
\<close>

theorem CursorGeneralDueLoopStrongHeadRel_managed_gate_last_future_bare_loop_full:
  assumes strong:
    "CursorGeneralDueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed [Generic task]
       (Generic f # map Generic fs) phase next pxTCB"
    and gate:
      "due_prefix_managed_gate_inv D R c now entry processed [Generic task]
         (Generic f # map Generic fs) current managed
         C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_bare_loop (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Exn () \<and>
       CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
         processed task f fs C branch S generic_raw event_raw K_G K_E managed
         termination external c t \<and>
       due_prefix_generated_terminal_post D now entry
         (processed @ [Generic task]) (f # fs) (Exn ()) t\<rbrace>"
proof -
  have head_nonnull: "sd_tcb_ptr D task \<noteq> NULL"
    using due_prefix_managed_gate_inv_head_nonnull[OF gate] selector by simp
  note body =
    CursorGeneralDueLoopStrongHeadRel_managed_gate_last_future_result_full[
      OF strong gate selector roots]
  show ?thesis
    unfolding due_prefix_generated_bare_loop_def
  proof (rule runs_to_whileLoop_unroll_exn)
    show
      "\<not> (\<lambda>p _. p \<noteq> NULL) (sd_tcb_ptr D task) c \<Longrightarrow>
       Result (sd_tcb_ptr D task) = Exn () \<and>
       CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
         processed task f fs C branch S generic_raw event_raw K_G K_E managed
         termination external c c \<and>
       due_prefix_generated_terminal_post D now entry
         (processed @ [Generic task]) (f # fs) (Exn ()) c"
      using head_nonnull by simp
    show
      "(\<lambda>p _. p \<noteq> NULL) (sd_tcb_ptr D task) c \<Longrightarrow>
       one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
       \<lbrace>\<lambda>r t.
         (\<forall>b. r = Result b \<longrightarrow>
           whileLoop (\<lambda>p _. p \<noteq> NULL)
             one_due_tick_loop_body_source b \<bullet> t
             \<lbrace>\<lambda>q u.
               q = Exn () \<and>
               CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
                 processed task f fs C branch S generic_raw event_raw K_G K_E
                 managed termination external c u \<and>
               due_prefix_generated_terminal_post D now entry
                 (processed @ [Generic task]) (f # fs) (Exn ()) u\<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
           Exn e = Exn () \<and>
           CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
             processed task f fs C branch S generic_raw event_raw K_G K_E
             managed termination external c t \<and>
           due_prefix_generated_terminal_post D now entry
             (processed @ [Generic task]) (f # fs) (Exn ()) t)\<rbrace>"
    proof -
      assume guard: "(\<lambda>p _. p \<noteq> NULL) (sd_tcb_ptr D task) c"
      show ?thesis
      proof (rule runs_to_weaken[OF body])
        fix r ::
          "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
        fix t :: Scheduler_V611_Parse.globals
        assume body_post:
          "CursorGeneralDueLoopManagedStrongTerminalFutureBodyPost D now entry
             processed task f fs C branch S generic_raw event_raw K_G K_E
             managed termination external c r t"
        have result: "r = Result (sd_tcb_ptr D f)"
          and body_exact:
            "one_due_tick_body_post D C branch generic_raw c
              (Result (sd_tcb_ptr D f)) t"
          and terminal_source:
            "due_prefix_terminal_source_rel D
              (Generic f # map Generic fs)
              (due_prefix_result_step_abs entry processed (Generic task))
              FutureExit (Some (Generic f)) (sd_tcb_ptr D f)"
          and state:
            "CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
              processed task f fs C branch S generic_raw event_raw K_G K_E
              managed termination external c t"
          using body_post
          by (simp_all add:
            CursorGeneralDueLoopManagedStrongTerminalFutureBodyPost_def)
        let ?after =
          "due_prefix_result_step_abs entry processed (Generic task)"
        let ?h0 = "hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c)"
        let ?hg = "one_due_generic_remove_heap D C ?h0"
        let ?he = "one_due_event_remove_heap D C branch ?hg"
        let ?generic_raw' =
          "one_due_reentry_generic_raw D C ?he generic_raw"
        let ?event_raw' =
          "one_due_event_raw_after_remove D C branch event_raw"
        let ?S' = "one_due_reentry_snapshot C branch S"
        note state_facts = state[
          unfolded CursorGeneralDueLoopManagedStrongTerminalFutureState_def
            Let_def]
        note state_eq = conjunct1[OF state_facts]
        note state_tail = conjunct2[OF state_facts]
        have terminal_head:
          "CursorGeneralStrongDuePrefixLoopHeadRel D t ?after managed
             termination external ?generic_raw' (ods_generic_family ?S')
             ?event_raw' (ods_event_family ?S') K_G K_E ?S'
             now entry (processed @ [Generic task]) []
             (Generic f # map Generic fs)
             FutureExit (Some (Generic f)) (sd_tcb_ptr D f)"
          by (rule conjunct1[OF state_tail])
        have exit:
          "due_prefix_exit_inv now entry (processed @ [Generic task]) []
             (Generic f # map Generic fs) ?after
             FutureExit (Some (Generic f))"
          using terminal_head
          by (simp add: CursorGeneralStrongDuePrefixLoopHeadRel_def)
        have ready:
          "due_prefix_future_source_ready D t now ?after f (K_G f)"
          by (rule conjunct2[OF state_tail])
        have f_nonnull: "sd_tcb_ptr D f \<noteq> NULL"
          by (rule due_prefix_future_source_ready_nonnull[OF ready])
        have throws:
          "one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> t
           \<lbrace>\<lambda>q u. q = Exn () \<and> u = t\<rbrace>"
          by (rule due_prefix_future_source_ready_throws[OF ready])
        have terminal_post:
          "due_prefix_generated_terminal_post D now entry
             (processed @ [Generic task]) (f # fs) (Exn ()) t"
          unfolding due_prefix_generated_terminal_post_def
          apply (rule exI[where x="?after"])
          apply (rule exI[where x=FutureExit])
          apply (rule exI[where x="Some (Generic f)"])
          apply (rule exI[where x="sd_tcb_ptr D f"])
          apply (rule exI[where x=C])
          apply (rule exI[where x=branch])
          apply (rule exI[where x=generic_raw])
          apply (rule exI[where x=c])
          using exit terminal_source body_exact by simp
        have loop_future:
          "whileLoop (\<lambda>p _. p \<noteq> NULL)
             one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> t
           \<lbrace>\<lambda>q u.
             q = Exn () \<and>
             CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
               processed task f fs C branch S generic_raw event_raw K_G K_E
               managed termination external c u \<and>
             due_prefix_generated_terminal_post D now entry
               (processed @ [Generic task]) (f # fs) (Exn ()) u\<rbrace>"
        proof (rule runs_to_whileLoop_unroll_exn)
          show
            "\<not> (\<lambda>p _. p \<noteq> NULL) (sd_tcb_ptr D f) t \<Longrightarrow>
             Result (sd_tcb_ptr D f) = Exn () \<and>
             CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
               processed task f fs C branch S generic_raw event_raw K_G K_E
               managed termination external c t \<and>
             due_prefix_generated_terminal_post D now entry
               (processed @ [Generic task]) (f # fs) (Exn ()) t"
            using f_nonnull by simp
          show
            "(\<lambda>p _. p \<noteq> NULL) (sd_tcb_ptr D f) t \<Longrightarrow>
             one_due_tick_loop_body_source (sd_tcb_ptr D f) \<bullet> t
             \<lbrace>\<lambda>q u.
               (\<forall>b. q = Result b \<longrightarrow>
                 whileLoop (\<lambda>p _. p \<noteq> NULL)
                   one_due_tick_loop_body_source b \<bullet> u
                   \<lbrace>\<lambda>v w.
                     v = Exn () \<and>
                     CursorGeneralDueLoopManagedStrongTerminalFutureState D now
                       entry processed task f fs C branch S generic_raw
                       event_raw K_G K_E managed termination external c w \<and>
                     due_prefix_generated_terminal_post D now entry
                       (processed @ [Generic task]) (f # fs)
                       (Exn ()) w\<rbrace>) \<and>
               (\<forall>e. q = Exn e \<longrightarrow>
                 Exn e = Exn () \<and>
                 CursorGeneralDueLoopManagedStrongTerminalFutureState D now
                   entry processed task f fs C branch S generic_raw event_raw
                   K_G K_E managed termination external c u \<and>
                 due_prefix_generated_terminal_post D now entry
                   (processed @ [Generic task]) (f # fs) (Exn ()) u)\<rbrace>"
          proof -
            assume future_guard:
              "(\<lambda>p _. p \<noteq> NULL) (sd_tcb_ptr D f) t"
            show ?thesis
            proof (rule runs_to_weaken[OF throws])
              fix q ::
                "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
              fix u :: Scheduler_V611_Parse.globals
              assume throw_post: "q = Exn () \<and> u = t"
              show
                "(\<forall>b. q = Result b \<longrightarrow>
                   whileLoop (\<lambda>p _. p \<noteq> NULL)
                     one_due_tick_loop_body_source b \<bullet> u
                     \<lbrace>\<lambda>v w.
                       v = Exn () \<and>
                       CursorGeneralDueLoopManagedStrongTerminalFutureState D
                         now entry processed task f fs C branch S generic_raw
                         event_raw K_G K_E managed termination external c w \<and>
                       due_prefix_generated_terminal_post D now entry
                         (processed @ [Generic task]) (f # fs)
                         (Exn ()) w\<rbrace>) \<and>
                 (\<forall>e. q = Exn e \<longrightarrow>
                   Exn e = Exn () \<and>
                   CursorGeneralDueLoopManagedStrongTerminalFutureState D now
                     entry processed task f fs C branch S generic_raw event_raw
                     K_G K_E managed termination external c u \<and>
                   due_prefix_generated_terminal_post D now entry
                     (processed @ [Generic task]) (f # fs) (Exn ()) u)"
                using throw_post state terminal_post by auto
            qed
          qed
        qed
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop (\<lambda>p _. p \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
               \<lbrace>\<lambda>q u.
                 q = Exn () \<and>
                 CursorGeneralDueLoopManagedStrongTerminalFutureState D now
                   entry processed task f fs C branch S generic_raw event_raw
                   K_G K_E managed termination external c u \<and>
                 due_prefix_generated_terminal_post D now entry
                   (processed @ [Generic task]) (f # fs) (Exn ()) u\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow>
             Exn e = Exn () \<and>
             CursorGeneralDueLoopManagedStrongTerminalFutureState D now entry
               processed task f fs C branch S generic_raw event_raw K_G K_E
               managed termination external c t \<and>
             due_prefix_generated_terminal_post D now entry
               (processed @ [Generic task]) (f # fs) (Exn ()) t)"
          using result loop_future by auto
      qed
    qed
  qed
qed

end
