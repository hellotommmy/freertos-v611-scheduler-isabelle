theory Scheduler_Resume_Managed_Loop_Induction
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Body_Reentry.Scheduler_Resume_Managed_Body_Reentry"
begin

text \<open>
  The managed pending-ready loop now closes by plain list induction.  Each
  nonempty step uses the checked managed body transaction, whose post-state is
  again a managed phase relation for the literal tail context.  The concrete
  yield word remains an independent accumulator: the re-entry snapshot is
  quiet, while the word records whether the incoming accumulator or any
  processed priority comparison requested a yield.
\<close>

lemma
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_drains_aux:
  fixes ts :: "'tid list"
  shows
    "\<And>c a generic_raw generic_abs event_raw event_abs S C P y.
       CursorGeneralStrongResumePendingManagedPhaseRel
         D c a managed termination external
         generic_raw generic_abs event_raw event_abs K_G K_E S C P \<Longrightarrow>
       rpc_tasks C = ts \<Longrightarrow>
       whileLoop resume_pending_generated_cond
         resume_pending_generated_body
         (resume_pending_next_head_tcb D ts, y) \<bullet> c
       \<lbrace>\<lambda>r s.
          \<exists>generic_raw' generic_abs' event_raw' event_abs'
             S' C' P' yw.
            r = Result (NULL, yw) \<and>
            CursorGeneralStrongResumePendingManagedPhaseRel
              D s (drain_pending_nodes_abs (map Event ts) a)
              managed termination external
              generic_raw' generic_abs' event_raw' event_abs'
              K_G K_E S' C' P' \<and>
            rpc_tasks C' = [] \<and>
            rpc_live C' = rpc_live C \<and>
            rpc_current_priority C' = rpc_current_priority C \<and>
            rpc_priority C' = rpc_priority C \<and>
            yw =
              (if \<exists>u\<in>set ts.
                    rpc_current_priority C \<le> rpc_priority C u
               then (1 :: int) else y)
       \<rbrace>"
proof (induction ts)
  case Nil
  have head_null:
    "resume_pending_next_head_tcb D ([] :: 'tid list) = NULL"
    by (simp add: resume_pending_next_head_tcb_def)
  have cond_false:
    "\<not> resume_pending_generated_cond
       (resume_pending_next_head_tcb D ([] :: 'tid list), y) c"
    using head_null
    by (simp add: resume_pending_generated_cond_def)
  show ?case
    apply (subst runs_to_whileLoop_cond_fail
        [of resume_pending_generated_cond
            "(resume_pending_next_head_tcb D ([] :: 'tid list), y)" c,
          OF cond_false])
    apply runs_to_vcg
     apply (simp add: resume_pending_next_head_tcb_def)
    apply (rule exI[of _ generic_raw])
    apply (rule exI[of _ generic_abs])
    apply (rule exI[of _ event_raw])
    apply (rule exI[of _ event_abs])
    apply (rule exI[of _ S])
    apply (rule exI[of _ C])
    apply (rule conjI)
     apply (rule exI[of _ P])
     using Nil.prems(1)
     apply (simp add: drain_pending_nodes_abs_map_Event
         resume_pending_drained_all_abs_simps)
    using Nil.prems(2)
    by simp
next
  case (Cons t rest)
  note phase = Cons.prems(1)
  note tasks = Cons.prems(2)
  have head_eq:
    "resume_pending_next_head_tcb D (t # rest) = sd_tcb_ptr D t"
    by (simp add: resume_pending_next_head_tcb_def)
  have guard_t: "c_guard (sd_tcb_ptr D t)"
    by (rule
      CursorGeneralStrongResumePendingManagedPhaseRel_head_tcb_guardD[
        OF phase tasks])
  have head_not_null: "sd_tcb_ptr D t \<noteq> NULL"
    by (rule c_guard_NULL[OF guard_t])
  have cond_true:
    "resume_pending_generated_cond (sd_tcb_ptr D t, y) c"
    using head_not_null
    by (simp add: resume_pending_generated_cond_def)
  note body =
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_body_reentry_exact[
      where y=y, OF phase tasks]
  note ctx = resume_pending_drained_context_components[of C t rest]

  show ?case
    apply (simp only: head_eq)
    apply (subst whileLoop_unroll)
    apply (simp only: runs_to_condition_iff)
    apply (simp only: cond_true if_True)
    apply (rule runs_to_bind)
    apply (rule runs_to_weaken[OF body])
    apply (clarsimp split del: if_split)
    apply (rule runs_to_weaken[OF Cons.IH[OF _ _]])
      apply assumption
     apply assumption
    apply clarify
    apply (rule conjI)
     apply (cases "rpc_current_priority C \<le> rpc_priority C t")
      apply (simp add: ctx)
     apply (simp add: ctx)
    apply (intro exI)
    apply (rule conjI)
     apply (rule exI)
     apply (simp only: drain_pending_nodes_abs_map_Event
         resume_pending_drained_all_abs_simps)
    apply (intro conjI)
        apply (simp add: ctx)
       apply (simp add: ctx)
      apply (simp add: ctx)
    by (simp add: ctx)
qed

theorem
  CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_drains:
  fixes y :: int
  assumes phase:
    "CursorGeneralStrongResumePendingManagedPhaseRel
       D c a managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S C P"
  shows
    "whileLoop resume_pending_generated_cond
       resume_pending_generated_body
       (resume_pending_next_head_tcb D (rpc_tasks C), y) \<bullet> c
     \<lbrace>\<lambda>r s.
        \<exists>generic_raw' generic_abs' event_raw' event_abs'
           S' C' P' yw.
          r = Result (NULL, yw) \<and>
          CursorGeneralStrongResumePendingManagedPhaseRel
            D s
            (drain_pending_nodes_abs (map Event (rpc_tasks C)) a)
            managed termination external
            generic_raw' generic_abs' event_raw' event_abs'
            K_G K_E S' C' P' \<and>
          rpc_tasks C' = [] \<and>
          rpc_live C' = rpc_live C \<and>
          rpc_current_priority C' = rpc_current_priority C \<and>
          rpc_priority C' = rpc_priority C \<and>
          yw =
            (if \<exists>u\<in>set (rpc_tasks C).
                  rpc_current_priority C \<le> rpc_priority C u
             then (1 :: int) else y)
     \<rbrace>"
  by (rule
    CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_drains_aux[
      OF phase refl])

ML \<open>
  fun audit_exact label expected th =
    let
      val _ =
        if null (Thm.hyps_of th) then ()
        else error (label ^ " has hidden hypotheses")
      val actual = length (Thm.prems_of th)
      val _ =
        if actual = expected then ()
        else error
          (label ^ " expected exactly " ^ Int.toString expected ^
           " premises, found " ^ Int.toString actual)
    in () end

  val _ = audit_exact "managed pending loop induction auxiliary" 2
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_drains_aux}
  val _ = audit_exact "managed pending loop induction" 1
    @{thm
      CursorGeneralStrongResumePendingManagedPhaseRel_generated_loop_drains}
\<close>

end
