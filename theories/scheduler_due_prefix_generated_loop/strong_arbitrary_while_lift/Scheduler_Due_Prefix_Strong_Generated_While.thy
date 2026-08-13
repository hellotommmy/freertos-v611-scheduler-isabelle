theory Scheduler_Due_Prefix_Strong_Generated_While
  imports Scheduler_Due_Prefix_Strong_Generated_Terminal_Contracts
begin

text \<open>
  Arbitrary finite nonempty due-prefix execution.  Induction is on the exact
  tail after the current due task.  A Cons tail can only use the non-last
  Result capstone; a Nil tail can only use one of the two generated terminal
  leaves.  Thus a future-head Exn is never fed back as a successor index, and
  the last due task is never sent to the non-last theorem.
\<close>

theorem due_prefix_strong_generated_bare_loop_nonempty:
  assumes index:
    "due_prefix_strong_generated_head_index D R now entry all_due future
       processed task due_tail pxTCB c
       managed termination external K_G K_E"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_strong_generated_terminal_post D now entry all_due
       future managed termination external K_G K_E\<rbrace>"
  using index
proof (induction due_tail arbitrary: processed task pxTCB c)
  case Nil
  obtain C branch S generic_raw event_raw where
      ledger: "all_due = processed @ [Generic task]"
    and selector: "odc_task C = task"
    and ptr: "pxTCB = sd_tcb_ptr D task"
    and strong:
      "DueLoopStrongHeadRel D c
        (due_prefix_fold_state entry processed)
        managed termination external
        generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry processed [Generic task] (map Generic future)
        DueGate (Some (Generic task)) pxTCB"
    and gate:
      "due_prefix_gate_inv D R c now entry processed [Generic task]
        (map Generic future) (due_prefix_fold_state entry processed)
        C branch S generic_raw event_raw"
    using Nil.prems
    by (auto simp: due_prefix_strong_generated_head_index_def)
  show ?case
  proof (cases future)
    case future_empty: Nil
    have strong_empty:
      "DueLoopStrongHeadRel D c
        (due_prefix_fold_state entry processed)
        managed termination external
        generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry processed [Generic task] []
        DueGate (Some (Generic task)) pxTCB"
      using strong future_empty by simp
    have gate_empty:
      "due_prefix_gate_inv D R c now entry processed [Generic task] []
        (due_prefix_fold_state entry processed)
        C branch S generic_raw event_raw"
      using gate future_empty by simp
    note terminal = DueLoopStrongHeadRel_last_empty_bare_loop_full[
      OF strong_empty gate_empty selector roots]
    show ?thesis
      unfolding ptr
    proof (rule runs_to_weaken[OF terminal])
      fix r ::
        "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
      fix t :: Scheduler_V611_Parse.globals
      assume post:
        "r = Result NULL \<and>
         DueLoopSharedLastEmptyEndpoint D now entry processed task C branch S
           generic_raw event_raw K_G K_E managed termination external c t"
      show
        "due_prefix_strong_generated_terminal_post D now entry all_due future
          managed termination external K_G K_E r t"
        unfolding due_prefix_strong_generated_terminal_post_def
        apply (simp only: future_empty list.case)
        apply (rule exI[where x=processed])
        apply (rule exI[where x=task])
        apply (rule exI[where x=C])
        apply (rule exI[where x=branch])
        apply (rule exI[where x=S])
        apply (rule exI[where x=generic_raw])
        apply (rule exI[where x=event_raw])
        apply (rule exI[where x=c])
        using ledger post by simp
    qed
  next
    case future_cons: (Cons f fs)
    have strong_future:
      "DueLoopStrongHeadRel D c
        (due_prefix_fold_state entry processed)
        managed termination external
        generic_raw (ods_generic_family S)
        event_raw (ods_event_family S) K_G K_E S
        now entry processed [Generic task]
        (Generic f # map Generic fs)
        DueGate (Some (Generic task)) pxTCB"
      using strong future_cons by simp
    have gate_future:
      "due_prefix_gate_inv D R c now entry processed [Generic task]
        (Generic f # map Generic fs)
        (due_prefix_fold_state entry processed)
        C branch S generic_raw event_raw"
      using gate future_cons by simp
    note terminal = DueLoopStrongHeadRel_last_future_bare_loop_full[
      OF strong_future gate_future selector roots]
    show ?thesis
      unfolding ptr
    proof (rule runs_to_weaken[OF terminal])
      fix r ::
        "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
      fix t :: Scheduler_V611_Parse.globals
      assume post:
        "r = Exn () \<and>
         DueLoopStrongTerminalFutureState D now entry processed task f fs C
           branch S generic_raw event_raw K_G K_E managed termination external
           c t \<and>
         due_prefix_generated_terminal_post D now entry
           (processed @ [Generic task]) (f # fs) (Exn ()) t"
      show
        "due_prefix_strong_generated_terminal_post D now entry all_due future
          managed termination external K_G K_E r t"
        unfolding due_prefix_strong_generated_terminal_post_def
        apply (simp only: future_cons list.case)
        apply (rule exI[where x=processed])
        apply (rule exI[where x=task])
        apply (rule exI[where x=C])
        apply (rule exI[where x=branch])
        apply (rule exI[where x=S])
        apply (rule exI[where x=generic_raw])
        apply (rule exI[where x=event_raw])
        apply (rule exI[where x=c])
        using ledger post by simp
    qed
  qed
next
  case (Cons u due_tail)
  have nonnull: "pxTCB \<noteq> NULL"
    by (rule due_prefix_strong_generated_head_index_nonnull[OF Cons.prems])
  note step = due_prefix_strong_generated_nonlast_index_step[
    OF Cons.prems roots]
  show ?case
    unfolding due_prefix_generated_bare_loop_def
  proof (rule runs_to_whileLoop_unroll_exn)
    show
      "\<not> (\<lambda>p _. p \<noteq> NULL) pxTCB c \<Longrightarrow>
       due_prefix_strong_generated_terminal_post D now entry all_due future
         managed termination external K_G K_E (Result pxTCB) c"
      using nonnull by simp
    show
      "(\<lambda>p _. p \<noteq> NULL) pxTCB c \<Longrightarrow>
       one_due_tick_loop_body_source pxTCB \<bullet> c
       \<lbrace>\<lambda>r t.
         (\<forall>b. r = Result b \<longrightarrow>
           whileLoop (\<lambda>p _. p \<noteq> NULL)
             one_due_tick_loop_body_source b \<bullet> t
             \<lbrace>due_prefix_strong_generated_terminal_post D now entry
               all_due future managed termination external K_G K_E\<rbrace>) \<and>
         (\<forall>e. r = Exn e \<longrightarrow>
           due_prefix_strong_generated_terminal_post D now entry all_due
             future managed termination external K_G K_E (Exn e) t)\<rbrace>"
    proof -
      assume guard: "(\<lambda>p _. p \<noteq> NULL) pxTCB c"
      show ?thesis
      proof (rule runs_to_weaken[OF step])
        fix r ::
          "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
        fix t :: Scheduler_V611_Parse.globals
        assume post:
          "r = Result (sd_tcb_ptr D u) \<and>
           due_prefix_strong_generated_head_index D R now entry all_due future
             (processed @ [Generic task]) u due_tail
             (sd_tcb_ptr D u) t managed termination external K_G K_E"
        have result: "r = Result (sd_tcb_ptr D u)"
          using post by simp
        have next_index:
          "due_prefix_strong_generated_head_index D R now entry all_due future
            (processed @ [Generic task]) u due_tail
            (sd_tcb_ptr D u) t managed termination external K_G K_E"
          using post by simp
        have next_loop:
          "due_prefix_generated_bare_loop (sd_tcb_ptr D u) \<bullet> t
           \<lbrace>due_prefix_strong_generated_terminal_post D now entry all_due
             future managed termination external K_G K_E\<rbrace>"
          by (rule Cons.IH[OF next_index])
        have recurse:
          "whileLoop (\<lambda>p _. p \<noteq> NULL)
             one_due_tick_loop_body_source (sd_tcb_ptr D u) \<bullet> t
           \<lbrace>due_prefix_strong_generated_terminal_post D now entry all_due
             future managed termination external K_G K_E\<rbrace>"
          using next_loop
          by (simp add: due_prefix_generated_bare_loop_def)
        show
          "(\<forall>b. r = Result b \<longrightarrow>
             whileLoop (\<lambda>p _. p \<noteq> NULL)
               one_due_tick_loop_body_source b \<bullet> t
               \<lbrace>due_prefix_strong_generated_terminal_post D now entry
                 all_due future managed termination external K_G K_E\<rbrace>) \<and>
           (\<forall>e. r = Exn e \<longrightarrow>
             due_prefix_strong_generated_terminal_post D now entry all_due
               future managed termination external K_G K_E (Exn e) t)"
          using result recurse by auto
      qed
    qed
  qed
qed

theorem due_prefix_strong_generated_finally_loop_nonempty:
  assumes index:
    "due_prefix_strong_generated_head_index D R now entry all_due future
       processed task due_tail pxTCB c
       managed termination external K_G K_E"
    and roots: "R = generated_scheduler_roots"
  shows
    "due_prefix_generated_finally_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>r t.
       r = Result () \<and>
       (\<exists>q. due_prefix_strong_generated_terminal_post D now entry
         all_due future managed termination external K_G K_E q t)\<rbrace>"
proof -
  have bare:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>due_prefix_strong_generated_terminal_post D now entry all_due
       future managed termination external K_G K_E\<rbrace>"
    by (rule due_prefix_strong_generated_bare_loop_nonempty[OF index roots])
  have bare_public:
    "due_prefix_generated_bare_loop pxTCB \<bullet> c
     \<lbrace>\<lambda>_ t. \<exists>q.
       due_prefix_strong_generated_terminal_post D now entry all_due future
         managed termination external K_G K_E q t\<rbrace>"
  proof (rule runs_to_weaken[OF bare])
    fix q ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "due_prefix_strong_generated_terminal_post D now entry all_due future
        managed termination external K_G K_E q t"
    show
      "\<exists>q. due_prefix_strong_generated_terminal_post D now entry all_due
        future managed termination external K_G K_E q t"
      by (rule exI[where x=q], rule post)
  qed
  show ?thesis
    by (rule due_prefix_generated_finally_normalises[OF bare_public])
qed

end
