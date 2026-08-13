theory Scheduler_Due_Prefix_Strong_Result_Components
  imports Scheduler_Due_Prefix_Strong_While_Connector
begin

text \<open>
  First non-last strong-preservation rung.  This theory deliberately separates
  the abstract/control ledger that is already forced by the exact generated
  Result step from the whole-heap family frames that are still open.

  The frame below lists exactly the scheduler_abs fields that a due wake does
  not change.  Ready/delayed ownership, wake, event-waiting and top-ready are
  intentionally absent because they are the semantic effects of the step.
\<close>

definition due_prefix_abstract_control_frame ::
  "'tid scheduler_abs \<Rightarrow> 'tid scheduler_abs \<Rightarrow> bool"
where
  "due_prefix_abstract_control_frame before after \<longleftrightarrow>
     sa_live after = sa_live before \<and>
     sa_priority after = sa_priority before \<and>
     sa_pending after = sa_pending before \<and>
     sa_suspended after = sa_suspended before \<and>
     sa_tick after = sa_tick before \<and>
     sa_missed_ticks after = sa_missed_ticks before \<and>
     sa_suspend_depth after = sa_suspend_depth before \<and>
     sa_missed_yield after = sa_missed_yield before \<and>
     sa_current after = sa_current before \<and>
     sa_current_role_a after = sa_current_role_a before \<and>
     sa_overflows after = sa_overflows before \<and>
     sa_yield_count after = sa_yield_count before"

lemma due_prefix_abstract_control_frame_refl:
  "due_prefix_abstract_control_frame a a"
  by (simp add: due_prefix_abstract_control_frame_def)

lemma due_prefix_abstract_control_frame_sym:
  assumes "due_prefix_abstract_control_frame a b"
  shows "due_prefix_abstract_control_frame b a"
  using assms by (simp add: due_prefix_abstract_control_frame_def)

lemma due_prefix_abstract_control_frame_trans:
  assumes ab: "due_prefix_abstract_control_frame a b"
    and bc: "due_prefix_abstract_control_frame b c"
  shows "due_prefix_abstract_control_frame a c"
  using ab bc by (simp add: due_prefix_abstract_control_frame_def)

lemma due_prefix_abstract_control_frame_add_ready:
  "due_prefix_abstract_control_frame s (add_ready_node n s)"
  by (cases n) (simp_all add: due_prefix_abstract_control_frame_def Let_def)

lemma due_prefix_abstract_control_frame_put_current:
  "due_prefix_abstract_control_frame s (put_current_delayed q s)"
  by (cases "sa_current_role_a s")
     (simp_all add: due_prefix_abstract_control_frame_def
        put_current_delayed_def)

lemma due_prefix_abstract_control_frame_fold_ready:
  "due_prefix_abstract_control_frame s (fold add_ready_node ns s)"
proof (induction ns arbitrary: s)
  case Nil
  show ?case
    using due_prefix_abstract_control_frame_refl[of s] by simp
next
  case (Cons n ns)
  have first:
    "due_prefix_abstract_control_frame s (add_ready_node n s)"
    by (rule due_prefix_abstract_control_frame_add_ready)
  have rest:
    "due_prefix_abstract_control_frame (add_ready_node n s)
       (fold add_ready_node ns (add_ready_node n s))"
    by (rule Cons.IH)
  have combined:
    "due_prefix_abstract_control_frame s
       (fold add_ready_node ns (add_ready_node n s))"
    by (rule due_prefix_abstract_control_frame_trans[OF first rest])
  show ?case using combined by simp
qed

lemma due_prefix_fold_state_control_frame:
  "due_prefix_abstract_control_frame entry
     (due_prefix_fold_state entry processed)"
proof -
  let ?removed =
    "remove_nodes processed (current_delayed_ring entry)"
  let ?put = "put_current_delayed ?removed entry"
  have put:
    "due_prefix_abstract_control_frame entry ?put"
    by (rule due_prefix_abstract_control_frame_put_current)
  have folded:
    "due_prefix_abstract_control_frame ?put
       (fold add_ready_node processed ?put)"
    by (rule due_prefix_abstract_control_frame_fold_ready)
  have combined:
    "due_prefix_abstract_control_frame entry
       (fold add_ready_node processed ?put)"
    by (rule due_prefix_abstract_control_frame_trans[OF put folded])
  show ?thesis
    using combined by (simp add: due_prefix_fold_state_def)
qed

lemma due_prefix_result_step_control_frame:
  assumes current:
    "current = due_prefix_fold_state entry processed"
  shows
    "due_prefix_abstract_control_frame current
       (due_prefix_result_step_abs entry processed n)"
proof -
  have entry_current:
    "due_prefix_abstract_control_frame entry current"
    using due_prefix_fold_state_control_frame[of entry processed]
      current by simp
  have current_entry:
    "due_prefix_abstract_control_frame current entry"
    by (rule due_prefix_abstract_control_frame_sym[OF entry_current])
  have entry_after:
    "due_prefix_abstract_control_frame entry
       (due_prefix_result_step_abs entry processed n)"
    using due_prefix_fold_state_control_frame[
      of entry "processed @ [n]"]
    by (simp add: due_prefix_result_step_abs_def)
  show ?thesis
    by (rule due_prefix_abstract_control_frame_trans[
          OF current_entry entry_after])
qed

section \<open>Pure preservation of the processing-phase invariants\<close>

text \<open>
  The following equation exposes one abstract Result step without choosing a
  task, priority, timestamp or delayed-list role.  In particular, the source
  delayed ring is selected by the abstract role bit, not by a fixed branch.
\<close>

lemma due_prefix_result_step_generic_state_eq:
  assumes current:
    "current = due_prefix_fold_state entry processed"
  shows
    "due_prefix_result_step_abs entry processed (Generic task) =
      (let q' = list_remove_abs (Generic task)
                    (current_delayed_ring current);
           p = sa_priority current task;
           k = (case sa_wake current task of None \<Rightarrow> 0 | Some w \<Rightarrow> w);
           ready' = list_insert_end_abs (Generic task) k
                      (sa_ready current p)
       in if sa_current_role_a current
          then
            (current\<lparr>sa_delayed_a := q'\<rparr>)
              \<lparr>sa_ready := (sa_ready current)(p := ready'),
                sa_wake := (sa_wake current)(task := None),
                sa_event_waiting := sa_event_waiting current - {task},
                sa_top_ready := max (sa_top_ready current) p\<rparr>
          else
            (current\<lparr>sa_delayed_b := q'\<rparr>)
              \<lparr>sa_ready := (sa_ready current)(p := ready'),
                sa_wake := (sa_wake current)(task := None),
                sa_event_waiting := sa_event_waiting current - {task},
                sa_top_ready := max (sa_top_ready current) p\<rparr>)"
  using due_prefix_result_step_is_one_generic_step[
      OF current, where n="Generic task" and t=task]
  by (cases "sa_current_role_a current")
     (simp_all add: put_current_delayed_def current_delayed_ring_def
        Let_def)

lemma due_loop_generic_task_set_remove:
  assumes distinct: "distinct (ring q)"
  shows
    "generic_task_set (list_remove_abs (Generic task) q) =
       generic_task_set q - {task}"
  using distinct
  by (auto simp: generic_task_set_def list_remove_abs_def
      set_remove1_eq)

lemma due_loop_generic_task_set_insert_end:
  assumes wf: "xlist_wf q"
  shows
    "generic_task_set (list_insert_end_abs (Generic task) k q) =
       insert task (generic_task_set q)"
  using list_insert_end_abs_ring_set[OF wf]
  by (auto simp: generic_task_set_def)

lemma due_loop_generic_ring_remove:
  assumes generic: "generic_ring q"
  shows "generic_ring (list_remove_abs x q)"
  using generic list_remove_abs_ring_subset[of x q]
  by (auto simp: generic_ring_def)

lemma due_loop_generic_ring_insert_end:
  assumes wf: "xlist_wf q"
    and generic: "generic_ring q"
  shows "generic_ring (list_insert_end_abs (Generic task) k q)"
  using generic list_insert_end_abs_ring_set[OF wf]
  by (auto simp: generic_ring_def)

text \<open>
  Empty pending is the exact extra premise needed for membership preservation.
  Without it, membership_wf permits the due task to have an Event node in the
  pending ring while its Generic node is delayed.  This Result step moves only
  the Generic node to ready, so such an Event node would cease to satisfy the
  required pending-subset-of-blocked condition.  DueLoopStrongHeadRel supplies
  the empty-pending premise directly.
\<close>

theorem due_prefix_result_step_preserves_due_loop_core_wf:
  assumes core: "due_loop_core_wf current"
    and loop:
      "due_prefix_loop_inv now entry processed
        (Generic task # remaining) future current"
    and pending_empty: "ring (sa_pending current) = []"
  shows
    "due_loop_core_wf
      (due_prefix_result_step_abs entry processed (Generic task))"
proof -
  let ?after =
    "due_prefix_result_step_abs entry processed (Generic task)"
  let ?q = "current_delayed_ring current"
  let ?p = "sa_priority current task"
  let ?k =
    "case sa_wake current task of None \<Rightarrow> 0 | Some w \<Rightarrow> w"
  let ?ready' =
    "list_insert_end_abs (Generic task) ?k (sa_ready current ?p)"
  have current_eq:
    "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop])
  have step_eq:
    "?after =
      (if sa_current_role_a current
       then
         (current\<lparr>sa_delayed_a :=
            list_remove_abs (Generic task) ?q\<rparr>)
           \<lparr>sa_ready := (sa_ready current)(?p := ?ready'),
             sa_wake := (sa_wake current)(task := None),
             sa_event_waiting := sa_event_waiting current - {task},
             sa_top_ready := max (sa_top_ready current) ?p\<rparr>
       else
         (current\<lparr>sa_delayed_b :=
            list_remove_abs (Generic task) ?q\<rparr>)
           \<lparr>sa_ready := (sa_ready current)(?p := ?ready'),
             sa_wake := (sa_wake current)(task := None),
             sa_event_waiting := sa_event_waiting current - {task},
             sa_top_ready := max (sa_top_ready current) ?p\<rparr>)"
    using due_prefix_result_step_generic_state_eq[OF current_eq,
        where task=task]
    by (simp add: Let_def)
  have current_ring:
    "ring ?q = Generic task # remaining @ future"
    using due_prefix_loop_inv_ringD[OF loop] by simp
  have task_node_member: "Generic task \<in> set (ring ?q)"
    using current_ring by simp

  have shapes: "ring_shape_wf current"
    and roles: "role_wf current"
    and members: "membership_wf current"
    and cache: "ready_cache_wf current"
    and current_well_formed: "current_wf current"
    using core by (simp_all add: due_loop_core_wf_def)
  have wf_ready:
    "\<And>p. p < 4 \<Longrightarrow> xlist_wf (sa_ready current p)"
    using shapes by (simp add: ring_shape_wf_def)
  have wf_da: "xlist_wf (sa_delayed_a current)"
    and wf_db: "xlist_wf (sa_delayed_b current)"
    and wf_pending: "xlist_wf (sa_pending current)"
    and wf_suspended: "xlist_wf (sa_suspended current)"
    using shapes by (simp_all add: ring_shape_wf_def)
  have wf_q: "xlist_wf ?q"
    using wf_da wf_db
    by (simp add: current_delayed_ring_def)
  have distinct_da: "distinct (ring (sa_delayed_a current))"
    and distinct_db: "distinct (ring (sa_delayed_b current))"
    using wf_da wf_db by (simp_all add: xlist_wf_def)
  have distinct_q: "distinct (ring ?q)"
    using wf_q by (simp add: xlist_wf_def)
  have task_current_set: "task \<in> generic_task_set ?q"
    using task_node_member by (simp add: generic_task_set_def)
  have task_physical:
    "task \<in> generic_task_set (sa_delayed_a current) \<union>
              generic_task_set (sa_delayed_b current)"
    using task_current_set
    by (simp add: current_delayed_ring_def split: if_splits)
  have task_live: "task \<in> sa_live current"
    using members task_physical
    by (auto simp: membership_wf_def Let_def)
  have priority_bound: "?p < 4"
    using core task_live by (simp add: due_loop_core_wf_def)
  have task_not_ready: "task \<notin> ready_task_set current"
    using members task_physical
    by (auto simp: membership_wf_def Let_def)
  have fresh_ready:
    "Generic task \<notin> set (ring (sa_ready current ?p))"
    using task_not_ready priority_bound
    by (auto simp: ready_task_set_def generic_task_set_def)

  have removed_wf:
    "xlist_wf (list_remove_abs (Generic task) ?q)"
    by (rule list_remove_preserves_wf[OF wf_q task_node_member])
  have inserted_wf: "xlist_wf ?ready'"
    by (rule list_insert_end_preserves_wf[
          OF wf_ready[OF priority_bound] fresh_ready])
  have ready_wf_after:
    "\<And>p. p < 4 \<Longrightarrow> xlist_wf (sa_ready ?after p)"
  proof -
    fix p :: nat
    assume p4: "p < 4"
    show "xlist_wf (sa_ready ?after p)"
    proof (cases "p = ?p")
      case True
      show ?thesis
        using inserted_wf True
        by (cases "sa_current_role_a current")
           (simp_all add: step_eq)
    next
      case False
      show ?thesis
        using wf_ready[OF p4] False
        by (cases "sa_current_role_a current")
           (simp_all add: step_eq)
    qed
  qed
  have delayed_a_wf_after: "xlist_wf (sa_delayed_a ?after)"
    using removed_wf wf_da
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)
  have delayed_b_wf_after: "xlist_wf (sa_delayed_b ?after)"
    using removed_wf wf_db
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)
  have pending_wf_after: "xlist_wf (sa_pending ?after)"
    using wf_pending
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)
  have suspended_wf_after: "xlist_wf (sa_suspended ?after)"
    using wf_suspended
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)
  have shape_after: "ring_shape_wf ?after"
    using ready_wf_after delayed_a_wf_after delayed_b_wf_after
      pending_wf_after suspended_wf_after
    by (simp add: ring_shape_wf_def)

  have priority_frame: "sa_priority ?after = sa_priority current"
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)

  have ready_payload:
    "\<And>p u. p < 4 \<Longrightarrow>
       u \<in> generic_task_set (sa_ready ?after p) \<Longrightarrow>
       sa_priority ?after u = p"
  proof -
    fix p :: nat and u
    assume p4: "p < 4"
      and membership: "u \<in> generic_task_set (sa_ready ?after p)"
    show "sa_priority ?after u = p"
    proof (cases "p = ?p")
      case True
      have expanded:
        "u \<in> insert task
          (generic_task_set (sa_ready current ?p))"
        using membership True
          due_loop_generic_task_set_insert_end[
            OF wf_ready[OF priority_bound], of task ?k]
        by (cases "sa_current_role_a current")
           (simp_all add: step_eq)
      show ?thesis
      proof -
        from expanded have alternatives:
          "u = task \<or>
           u \<in> generic_task_set (sa_ready current ?p)"
          by simp
        show ?thesis
        proof (rule disjE[OF alternatives])
          assume task_case: "u = task"
          show ?thesis
          proof -
            have point_frame:
              "sa_priority ?after u = sa_priority current u"
              by (rule fun_cong[OF priority_frame])
            show ?thesis
            proof (rule trans)
              show "sa_priority ?after u = sa_priority current u"
                by (rule point_frame)
              show "sa_priority current u = p"
                using task_case True by simp
            qed
          qed
        next
          assume old_member:
            "u \<in> generic_task_set (sa_ready current ?p)"
          have old_priority: "sa_priority current u = ?p"
            using roles priority_bound old_member
            by (simp add: role_wf_def)
          show ?thesis
          proof -
            have point_frame:
              "sa_priority ?after u = sa_priority current u"
              by (rule fun_cong[OF priority_frame])
            show ?thesis
            proof (rule trans)
              show "sa_priority ?after u = sa_priority current u"
                by (rule point_frame)
              show "sa_priority current u = p"
                using old_priority True by simp
            qed
          qed
        qed
      qed
    next
      case False
      have old_member:
        "u \<in> generic_task_set (sa_ready current p)"
        using membership False
        by (cases "sa_current_role_a current")
           (simp_all add: step_eq)
      have old_priority: "sa_priority current u = p"
        using roles p4 old_member by (simp add: role_wf_def)
      show ?thesis
      proof -
        have point_frame:
          "sa_priority ?after u = sa_priority current u"
          by (rule fun_cong[OF priority_frame])
        show ?thesis
        proof (rule trans)
          show "sa_priority ?after u = sa_priority current u"
            by (rule point_frame)
          show "sa_priority current u = p"
            by (rule old_priority)
        qed
      qed
    qed
  qed
  have ready_generic:
    "\<And>p. p < 4 \<Longrightarrow> generic_ring (sa_ready ?after p)"
  proof -
    fix p :: nat
    assume p4: "p < 4"
    have old: "generic_ring (sa_ready current p)"
      using roles p4 by (simp add: role_wf_def)
    show "generic_ring (sa_ready ?after p)"
    proof (cases "p = ?p")
      case True
      have inserted:
        "generic_ring ?ready'"
        by (rule due_loop_generic_ring_insert_end[
              OF wf_ready[OF priority_bound]])
           (use old True in simp)
      show ?thesis
        using inserted True
        by (cases "sa_current_role_a current")
           (simp_all add: step_eq)
    next
      case False
      show ?thesis
        using old False
        by (cases "sa_current_role_a current")
           (simp_all add: step_eq)
    qed
  qed
  have delayed_a_generic:
    "generic_ring (sa_delayed_a ?after)"
    using roles due_loop_generic_ring_remove[
      of "sa_delayed_a current" "Generic task"]
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq role_wf_def current_delayed_ring_def)
  have delayed_b_generic:
    "generic_ring (sa_delayed_b ?after)"
    using roles due_loop_generic_ring_remove[
      of "sa_delayed_b current" "Generic task"]
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq role_wf_def current_delayed_ring_def)
  have delayed_a_cursor: "cursor (sa_delayed_a ?after) = None"
    using roles
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq role_wf_def current_delayed_ring_def
          list_remove_abs_def)
  have delayed_b_cursor: "cursor (sa_delayed_b ?after) = None"
    using roles
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq role_wf_def current_delayed_ring_def
          list_remove_abs_def)
  have pending_frame: "sa_pending ?after = sa_pending current"
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)
  have suspended_frame: "sa_suspended ?after = sa_suspended current"
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)
  have pending_event_after: "event_ring (sa_pending ?after)"
    using roles pending_frame by (simp add: role_wf_def)
  have suspended_generic_after: "generic_ring (sa_suspended ?after)"
    using roles suspended_frame by (simp add: role_wf_def)
  have pending_tail_after: "tail_cursor_wf (sa_pending ?after)"
    using roles pending_frame by (simp add: role_wf_def)
  have suspended_tail_after: "tail_cursor_wf (sa_suspended ?after)"
    using roles suspended_frame by (simp add: role_wf_def)
  have role_after: "role_wf ?after"
    unfolding role_wf_def
    using ready_generic ready_payload delayed_a_generic delayed_b_generic
      pending_event_after suspended_generic_after delayed_a_cursor
      delayed_b_cursor pending_tail_after suspended_tail_after
    by blast

  have ready_per_priority:
    "\<And>p. generic_task_set (sa_ready ?after p) =
       (if p = ?p
        then insert task (generic_task_set (sa_ready current p))
        else generic_task_set (sa_ready current p))"
    using due_loop_generic_task_set_insert_end[
      OF wf_ready[OF priority_bound], of task ?k]
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)
  have ready_sets:
    "ready_task_set ?after = insert task (ready_task_set current)"
    unfolding ready_task_set_def
    using priority_bound
    by (auto simp: ready_per_priority split: if_splits)
  have a_set:
    "generic_task_set (sa_delayed_a ?after) =
       (if sa_current_role_a current
        then generic_task_set (sa_delayed_a current) - {task}
        else generic_task_set (sa_delayed_a current))"
    using due_loop_generic_task_set_remove[OF distinct_da, of task]
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq current_delayed_ring_def)
  have b_set:
    "generic_task_set (sa_delayed_b ?after) =
       (if sa_current_role_a current
        then generic_task_set (sa_delayed_b current)
        else generic_task_set (sa_delayed_b current) - {task})"
    using due_loop_generic_task_set_remove[OF distinct_db, of task]
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq current_delayed_ring_def)
  have old_members:
    "ready_task_set current \<union>
       generic_task_set (sa_delayed_a current) \<union>
       generic_task_set (sa_delayed_b current) \<union>
       generic_task_set (sa_suspended current) = sa_live current"
    "ready_task_set current \<inter>
       generic_task_set (sa_delayed_a current) = {}"
    "ready_task_set current \<inter>
       generic_task_set (sa_delayed_b current) = {}"
    "ready_task_set current \<inter>
       generic_task_set (sa_suspended current) = {}"
    "generic_task_set (sa_delayed_a current) \<inter>
       generic_task_set (sa_delayed_b current) = {}"
    "generic_task_set (sa_delayed_a current) \<inter>
       generic_task_set (sa_suspended current) = {}"
    "generic_task_set (sa_delayed_b current) \<inter>
       generic_task_set (sa_suspended current) = {}"
    "event_task_set (sa_pending current) \<subseteq> sa_live current"
    "sa_event_waiting current \<subseteq> sa_live current"
    "event_task_set (sa_pending current) \<inter>
       sa_event_waiting current = {}"
    "event_task_set (sa_pending current) \<subseteq>
       generic_task_set (sa_delayed_a current) \<union>
       generic_task_set (sa_delayed_b current) \<union>
       generic_task_set (sa_suspended current)"
    "ready_task_set current \<inter> sa_event_waiting current = {}"
    using members by (auto simp: membership_wf_def Let_def)
  have live_frame: "sa_live ?after = sa_live current"
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)
  have current_live_entry: "sa_live current = sa_live entry"
    using due_prefix_fold_state_control_frame[of entry processed]
      current_eq
    by (simp add: due_prefix_abstract_control_frame_def)
  have event_waiting_frame:
    "sa_event_waiting ?after = sa_event_waiting current - {task}"
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)
  have suspended_set_frame:
    "generic_task_set (sa_suspended ?after) =
       generic_task_set (sa_suspended current)"
    using suspended_frame by simp
  have pending_set_empty:
    "event_task_set (sa_pending ?after) = {}"
    using pending_frame pending_empty
    by (simp add: event_task_set_def)
  have coverage_after:
    "ready_task_set ?after \<union>
       generic_task_set (sa_delayed_a ?after) \<union>
       generic_task_set (sa_delayed_b ?after) \<union>
       generic_task_set (sa_suspended ?after) = sa_live ?after"
    using old_members task_current_set current_live_entry
    by (cases "sa_current_role_a current")
       (auto simp: ready_sets a_set b_set suspended_set_frame live_frame
          current_delayed_ring_def)
  have ready_a_disjoint_after:
    "ready_task_set ?after \<inter>
       generic_task_set (sa_delayed_a ?after) = {}"
    using old_members task_current_set
    by (cases "sa_current_role_a current")
       (auto simp: ready_sets a_set current_delayed_ring_def)
  have ready_b_disjoint_after:
    "ready_task_set ?after \<inter>
       generic_task_set (sa_delayed_b ?after) = {}"
    using old_members task_current_set
    by (cases "sa_current_role_a current")
       (auto simp: ready_sets b_set current_delayed_ring_def)
  have ready_suspended_disjoint_after:
    "ready_task_set ?after \<inter>
       generic_task_set (sa_suspended ?after) = {}"
    using old_members task_current_set
    by (cases "sa_current_role_a current")
       (auto simp: ready_sets suspended_set_frame
          current_delayed_ring_def)
  have delayed_disjoint_after:
    "generic_task_set (sa_delayed_a ?after) \<inter>
       generic_task_set (sa_delayed_b ?after) = {}"
    using old_members
    by (cases "sa_current_role_a current")
       (auto simp: a_set b_set)
  have delayed_a_suspended_disjoint_after:
    "generic_task_set (sa_delayed_a ?after) \<inter>
       generic_task_set (sa_suspended ?after) = {}"
    using old_members
    by (cases "sa_current_role_a current")
       (auto simp: a_set suspended_set_frame)
  have delayed_b_suspended_disjoint_after:
    "generic_task_set (sa_delayed_b ?after) \<inter>
       generic_task_set (sa_suspended ?after) = {}"
    using old_members
    by (cases "sa_current_role_a current")
       (auto simp: b_set suspended_set_frame)
  have pending_live_after:
    "event_task_set (sa_pending ?after) \<subseteq> sa_live ?after"
    using pending_set_empty by simp
  have event_waiting_live_after:
    "sa_event_waiting ?after \<subseteq> sa_live ?after"
    using old_members event_waiting_frame live_frame by auto
  have pending_event_disjoint_after:
    "event_task_set (sa_pending ?after) \<inter>
       sa_event_waiting ?after = {}"
    using pending_set_empty by simp
  have pending_blocked_after:
    "event_task_set (sa_pending ?after) \<subseteq>
       generic_task_set (sa_delayed_a ?after) \<union>
       generic_task_set (sa_delayed_b ?after) \<union>
       generic_task_set (sa_suspended ?after)"
    using pending_set_empty by simp
  have ready_event_disjoint_after:
    "ready_task_set ?after \<inter> sa_event_waiting ?after = {}"
    using old_members ready_sets event_waiting_frame by auto
  have membership_after: "membership_wf ?after"
    unfolding membership_wf_def Let_def
    using coverage_after ready_a_disjoint_after ready_b_disjoint_after
      ready_suspended_disjoint_after delayed_disjoint_after
      delayed_a_suspended_disjoint_after
      delayed_b_suspended_disjoint_after pending_live_after
      event_waiting_live_after pending_event_disjoint_after
      pending_blocked_after ready_event_disjoint_after
    by blast

  have inserted_nonempty: "ring ?ready' \<noteq> []"
    using list_insert_end_abs_ring_set[
      OF wf_ready[OF priority_bound], of "Generic task" ?k]
    by (metis empty_set insert_not_empty)
  have cache_after: "ready_cache_wf ?after"
    using cache priority_bound inserted_nonempty
    unfolding ready_cache_wf_def
    by (cases "sa_current_role_a current")
       (auto simp: step_eq max_def)
  have current_after: "current_wf ?after"
    using current_well_formed
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq current_wf_def split: option.splits)

  show ?thesis
    unfolding due_loop_core_wf_def
    using core shape_after role_after membership_after cache_after
      current_after
    by (cases "sa_current_role_a current")
       (simp_all add: due_loop_core_wf_def step_eq)
qed

theorem due_prefix_result_step_preserves_due_loop_time_wf:
  assumes core: "due_loop_core_wf current"
    and time:
      "due_loop_time_wf now (Generic task # remaining) future current"
    and loop:
      "due_prefix_loop_inv now entry processed
        (Generic task # remaining) future current"
  shows
    "due_loop_time_wf now remaining future
      (due_prefix_result_step_abs entry processed (Generic task))"
proof -
  let ?after =
    "due_prefix_result_step_abs entry processed (Generic task)"
  let ?q = "current_delayed_ring current"
  let ?p = "sa_priority current task"
  let ?k =
    "case sa_wake current task of None \<Rightarrow> 0 | Some w \<Rightarrow> w"
  let ?ready' =
    "list_insert_end_abs (Generic task) ?k (sa_ready current ?p)"
  have current_eq:
    "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop])
  have step_eq:
    "?after =
      (if sa_current_role_a current
       then
         (current\<lparr>sa_delayed_a :=
            list_remove_abs (Generic task) ?q\<rparr>)
           \<lparr>sa_ready := (sa_ready current)(?p := ?ready'),
             sa_wake := (sa_wake current)(task := None),
             sa_event_waiting := sa_event_waiting current - {task},
             sa_top_ready := max (sa_top_ready current) ?p\<rparr>
       else
         (current\<lparr>sa_delayed_b :=
            list_remove_abs (Generic task) ?q\<rparr>)
           \<lparr>sa_ready := (sa_ready current)(?p := ?ready'),
             sa_wake := (sa_wake current)(task := None),
             sa_event_waiting := sa_event_waiting current - {task},
             sa_top_ready := max (sa_top_ready current) ?p\<rparr>)"
    using due_prefix_result_step_generic_state_eq[OF current_eq,
        where task=task]
    by (simp add: Let_def)
  have current_ring:
    "ring ?q = Generic task # remaining @ future"
    using due_prefix_loop_inv_ringD[OF loop] by simp
  have task_node_member: "Generic task \<in> set (ring ?q)"
    using current_ring by simp

  have shapes: "ring_shape_wf current"
    and members: "membership_wf current"
    using core by (simp_all add: due_loop_core_wf_def)
  have wf_ready:
    "\<And>p. p < 4 \<Longrightarrow> xlist_wf (sa_ready current p)"
    using shapes by (simp add: ring_shape_wf_def)
  have wf_da: "xlist_wf (sa_delayed_a current)"
    and wf_db: "xlist_wf (sa_delayed_b current)"
    using shapes by (simp_all add: ring_shape_wf_def)
  have distinct_da: "distinct (ring (sa_delayed_a current))"
    and distinct_db: "distinct (ring (sa_delayed_b current))"
    using wf_da wf_db by (simp_all add: xlist_wf_def)
  have task_current_set: "task \<in> generic_task_set ?q"
    using task_node_member by (simp add: generic_task_set_def)
  have task_physical:
    "task \<in> generic_task_set (sa_delayed_a current) \<union>
              generic_task_set (sa_delayed_b current)"
    using task_current_set
    by (simp add: current_delayed_ring_def split: if_splits)
  have task_live: "task \<in> sa_live current"
    using members task_physical
    by (auto simp: membership_wf_def Let_def)
  have priority_bound: "?p < 4"
    using core task_live by (simp add: due_loop_core_wf_def)
  have task_not_ready: "task \<notin> ready_task_set current"
    using members task_physical
    by (auto simp: membership_wf_def Let_def)
  have delayed_disjoint:
    "generic_task_set (sa_delayed_a current) \<inter>
       generic_task_set (sa_delayed_b current) = {}"
    using members by (auto simp: membership_wf_def Let_def)
  have task_not_overflow:
    "task \<notin> generic_task_set (overflow_delayed_ring current)"
    using task_current_set delayed_disjoint
    by (cases "sa_current_role_a current")
       (auto simp: current_delayed_ring_def overflow_delayed_ring_def)

  have ready_per_priority:
    "\<And>p. generic_task_set (sa_ready ?after p) =
       (if p = ?p
        then insert task (generic_task_set (sa_ready current p))
        else generic_task_set (sa_ready current p))"
    using due_loop_generic_task_set_insert_end[
      OF wf_ready[OF priority_bound], of task ?k]
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq)
  have ready_sets:
    "ready_task_set ?after = insert task (ready_task_set current)"
    unfolding ready_task_set_def
    using priority_bound
    by (auto simp: ready_per_priority split: if_splits)

  have agree_a:
    "delayed_key_agrees ?after (sa_delayed_a ?after)"
    using time delayed_disjoint task_current_set
    by (cases "sa_current_role_a current")
       (auto simp: due_loop_time_wf_def delayed_key_agrees_def
          step_eq current_delayed_ring_def
          due_loop_generic_task_set_remove[OF distinct_da]
          list_remove_abs_item_key)
  have agree_b:
    "delayed_key_agrees ?after (sa_delayed_b ?after)"
    using time delayed_disjoint task_current_set
    by (cases "sa_current_role_a current")
       (auto simp: due_loop_time_wf_def delayed_key_agrees_def
          step_eq current_delayed_ring_def
          due_loop_generic_task_set_remove[OF distinct_db]
          list_remove_abs_item_key)
  have old_sorted_a:
    "sorted (map (item_key (sa_delayed_a current))
       (ring (sa_delayed_a current)))"
    using time by (simp add: due_loop_time_wf_def)
  have old_sorted_b:
    "sorted (map (item_key (sa_delayed_b current))
       (ring (sa_delayed_b current)))"
    using time by (simp add: due_loop_time_wf_def)
  have removed_sorted_a:
    "sorted (map
       (item_key (list_remove_abs (Generic task)
          (sa_delayed_a current)))
       (ring (list_remove_abs (Generic task)
          (sa_delayed_a current))))"
  proof -
    have tail_sorted:
      "sorted (map (item_key (sa_delayed_a current))
         (remove1 (Generic task) (ring (sa_delayed_a current))))"
      by (rule sorted_map_remove1[OF old_sorted_a])
    show ?thesis
      using tail_sorted
      by (simp add: list_remove_abs_item_key list_remove_abs_def)
  qed
  have removed_sorted_b:
    "sorted (map
       (item_key (list_remove_abs (Generic task)
          (sa_delayed_b current)))
       (ring (list_remove_abs (Generic task)
          (sa_delayed_b current))))"
  proof -
    have tail_sorted:
      "sorted (map (item_key (sa_delayed_b current))
         (remove1 (Generic task) (ring (sa_delayed_b current))))"
      by (rule sorted_map_remove1[OF old_sorted_b])
    show ?thesis
      using tail_sorted
      by (simp add: list_remove_abs_item_key list_remove_abs_def)
  qed
  have sorted_a:
    "sorted (map (item_key (sa_delayed_a ?after))
       (ring (sa_delayed_a ?after)))"
    using old_sorted_a removed_sorted_a
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq current_delayed_ring_def)
  have sorted_b:
    "sorted (map (item_key (sa_delayed_b ?after))
       (ring (sa_delayed_b ?after)))"
    using old_sorted_b removed_sorted_b
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq current_delayed_ring_def)
  have inactive_after:
    "\<forall>u\<in>ready_task_set ?after \<union>
              generic_task_set (sa_suspended ?after).
       sa_wake ?after u = None"
    using time ready_sets
    by (cases "sa_current_role_a current")
       (auto simp: due_loop_time_wf_def step_eq)

  have loop_after:
    "due_prefix_loop_inv now entry (processed @ [Generic task])
      remaining future ?after"
    by (rule due_prefix_result_step_preserves_inv[OF loop])
  have successor_ring:
    "ring (current_delayed_ring ?after) = remaining @ future"
    by (rule due_prefix_loop_inv_ringD[OF loop_after])
  have current_key_frame:
    "item_key (current_delayed_ring ?after) = item_key ?q"
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq current_delayed_ring_def
          list_remove_abs_item_key)
  have remaining_due:
    "\<forall>n\<in>set remaining.
       (\<exists>t. n = Generic t) \<and>
       item_key (current_delayed_ring ?after) n \<le> now"
    using time current_key_frame
    by (auto simp: due_loop_time_wf_def)
  have future_strict:
    "\<forall>n\<in>set future.
       (\<exists>t. n = Generic t) \<and>
       now < item_key (current_delayed_ring ?after) n"
    using time current_key_frame
    by (auto simp: due_loop_time_wf_def)
  have overflow_ring_frame:
    "overflow_delayed_ring ?after = overflow_delayed_ring current"
    by (cases "sa_current_role_a current")
       (simp_all add: step_eq overflow_delayed_ring_def)
  have overflow_before:
    "\<forall>u\<in>generic_task_set (overflow_delayed_ring current).
       case sa_wake current u of
         None \<Rightarrow> False
       | Some k \<Rightarrow> k < now"
    using time by (simp add: due_loop_time_wf_def)
  have overflow_after:
    "\<forall>u\<in>generic_task_set (overflow_delayed_ring ?after).
       case sa_wake ?after u of
         None \<Rightarrow> False
       | Some k \<Rightarrow> k < now"
    using overflow_before task_not_overflow overflow_ring_frame
    by (cases "sa_current_role_a current")
       (auto simp: step_eq split: option.splits)

  show ?thesis
    unfolding due_loop_time_wf_def
    using agree_a agree_b sorted_a sorted_b inactive_after successor_ring
      remaining_due future_strict overflow_after
    by blast
qed

corollary DueLoopStrongHeadRel_result_step_preserves_due_loop_wf:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       generic_raw generic_abs event_raw event_abs K_G K_E S
       now entry processed (Generic task # remaining) future
       phase next pxTCB"
  shows
    "due_loop_core_wf
       (due_prefix_result_step_abs entry processed (Generic task)) \<and>
     due_loop_time_wf now remaining future
       (due_prefix_result_step_abs entry processed (Generic task))"
proof -
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  have core: "due_loop_core_wf current"
    and time:
      "due_loop_time_wf now (Generic task # remaining) future current"
    using snapshot
    by (simp_all add: DueLoopSchedulerSnapshotRel_def Let_def)
  note exit = DueLoopStrongHeadRel_exitD[OF strong]
  have loop:
    "due_prefix_loop_inv now entry processed
      (Generic task # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit])
  have pending_empty: "ring (sa_pending current) = []"
    using strong by (simp add: DueLoopStrongHeadRel_def)
  have core_after:
    "due_loop_core_wf
      (due_prefix_result_step_abs entry processed (Generic task))"
    by (rule due_prefix_result_step_preserves_due_loop_core_wf[
          OF core loop pending_empty])
  have time_after:
    "due_loop_time_wf now remaining future
      (due_prefix_result_step_abs entry processed (Generic task))"
    by (rule due_prefix_result_step_preserves_due_loop_time_wf[
          OF core time loop])
  show ?thesis using core_after time_after by simp
qed

definition StrongDuePrefixResultComponentPost ::
  "'tid scheduler_decode \<Rightarrow> scheduler_roots \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid \<Rightarrow> 'tid \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "StrongDuePrefixResultComponentPost D R now entry processed task u
       remaining future before managed termination r t \<longleftrightarrow>
     (let after =
        due_prefix_result_step_abs entry processed (Generic task)
      in r = Result (sd_tcb_ptr D u) \<and>
         due_prefix_exit_inv now entry (processed @ [Generic task])
           (Generic u # remaining) future after
           DueGate (Some (Generic u)) \<and>
         strong_managed_domain_rel after termination managed \<and>
         due_prefix_abstract_control_frame before after \<and>
         sa_tick after = now \<and>
         sa_suspend_depth after = 0 \<and>
         ring (sa_pending after) = [] \<and>
         TaskObservationRel D
           (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t)) after \<and>
         scheduler_decode_rel D after \<and>
         strong_due_next_ptr_rel D (Some (Generic u))
           (sd_tcb_ptr D u) \<and>
         (\<exists>C' branch' S' generic_raw' event_raw'.
           odc_task C' = u \<and>
           due_prefix_gate_inv D R t now entry
             (processed @ [Generic task]) (Generic u # remaining) future
             after C' branch' S' generic_raw' event_raw'))"

text \<open>
  This theorem opens the generated body only through the existing exact
  source-result certificate.  It recovers the successor Gate-H package and
  additionally proves the strong managed-domain and control ledger.  It does
  not claim that retired-task bytes or roots outside the local Gate-H universe
  were framed; those are named separately below.
\<close>

theorem DueLoopStrongHeadRel_nonlast_result_components:
  assumes strong:
    "DueLoopStrongHeadRel D c current managed termination external
       strong_generic_raw strong_generic_abs strong_event_raw strong_event_abs
       K_G K_E strong_S now entry processed
       (Generic task # Generic u # remaining) future phase next pxTCB"
    and local:
      "due_prefix_gate_inv D R c now entry processed
        (Generic task # Generic u # remaining) future current
        C branch S generic_raw event_raw"
    and selector: "odc_task C = task"
    and roots: "R = generated_scheduler_roots"
  shows
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>StrongDuePrefixResultComponentPost D R now entry processed
       task u remaining future current managed termination\<rbrace>"
proof -
  have local':
    "due_prefix_gate_inv D R c now entry processed
       (Generic (odc_task C) # Generic u # remaining) future current
       C branch S generic_raw event_raw"
    using local selector by simp
  note exact = due_prefix_generated_source_result_step[OF local' roots]
  have source:
    "one_due_tick_loop_body_source (sd_tcb_ptr D task) \<bullet> c
     \<lbrace>\<lambda>r t. \<exists>branch'.
       r = Result (sd_tcb_ptr D u) \<and>
       due_prefix_gate_inv D R t now entry
         (processed @ [Generic task]) (Generic u # remaining) future
         (due_prefix_result_step_abs entry processed (Generic task))
         (one_due_reentry_context C u) branch'
         (one_due_reentry_snapshot C branch S)
         (one_due_reentry_generic_raw D C
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
           generic_raw)
         (one_due_event_raw_after_remove D C branch event_raw)\<rbrace>"
    using exact selector by simp
  note snapshot = DueLoopStrongHeadRel_snapshotD[OF strong]
  have domain_before:
    "strong_managed_domain_rel current termination managed"
    by (rule DueLoopSchedulerSnapshotRel_domainD[OF snapshot])
  note exit_before = DueLoopStrongHeadRel_exitD[OF strong]
  have loop_before:
    "due_prefix_loop_inv now entry processed
       (Generic task # Generic u # remaining) future current"
    by (rule due_prefix_exit_inv_baseD[OF exit_before])
  have current:
    "current = due_prefix_fold_state entry processed"
    by (rule due_prefix_loop_inv_currentD[OF loop_before])
  have control_frame:
    "due_prefix_abstract_control_frame current
       (due_prefix_result_step_abs entry processed (Generic task))"
    by (rule due_prefix_result_step_control_frame[OF current])
  have quiet_before: "sa_suspend_depth current = 0"
    and pending_before: "ring (sa_pending current) = []"
    using strong by (simp_all add: DueLoopStrongHeadRel_def)
  show ?thesis
  proof (rule runs_to_weaken[OF source])
    fix r ::
      "(unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval"
    fix t :: Scheduler_V611_Parse.globals
    assume post:
      "\<exists>branch'.
       r = Result (sd_tcb_ptr D u) \<and>
       due_prefix_gate_inv D R t now entry
         (processed @ [Generic task]) (Generic u # remaining) future
         (due_prefix_result_step_abs entry processed (Generic task))
         (one_due_reentry_context C u) branch'
         (one_due_reentry_snapshot C branch S)
         (one_due_reentry_generic_raw D C
           (one_due_event_remove_heap D C branch
             (one_due_generic_remove_heap D C
               (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
           generic_raw)
         (one_due_event_raw_after_remove D C branch event_raw)"
    obtain branch' where result:
        "r = Result (sd_tcb_ptr D u)"
      and gate_after:
        "due_prefix_gate_inv D R t now entry
          (processed @ [Generic task]) (Generic u # remaining) future
          (due_prefix_result_step_abs entry processed (Generic task))
          (one_due_reentry_context C u) branch'
          (one_due_reentry_snapshot C branch S)
          (one_due_reentry_generic_raw D C
            (one_due_event_remove_heap D C branch
              (one_due_generic_remove_heap D C
                (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
            generic_raw)
          (one_due_event_raw_after_remove D C branch event_raw)"
      using post by blast
    let ?after =
      "due_prefix_result_step_abs entry processed (Generic task)"
    have loop_after:
      "due_prefix_loop_inv now entry (processed @ [Generic task])
        (Generic u # remaining) future ?after"
      using gate_after by (simp add: due_prefix_gate_inv_def)
    have exit_after:
      "due_prefix_exit_inv now entry (processed @ [Generic task])
        (Generic u # remaining) future ?after
        DueGate (Some (Generic u))"
      using loop_after by (simp add: due_prefix_exit_inv_def)
    have live_eq: "sa_live ?after = sa_live current"
      using control_frame
      by (simp add: due_prefix_abstract_control_frame_def)
    have domain_after:
      "strong_managed_domain_rel ?after termination managed"
      using domain_before live_eq
      by (simp add: strong_managed_domain_rel_def)
    have tick_after: "sa_tick ?after = now"
      using gate_after by (simp add: due_prefix_gate_inv_def)
    have quiet_after: "sa_suspend_depth ?after = 0"
      using control_frame quiet_before
      by (simp add: due_prefix_abstract_control_frame_def)
    have pending_after: "ring (sa_pending ?after) = []"
      using control_frame pending_before
      by (simp add: due_prefix_abstract_control_frame_def)
    have gate_rel_after:
      "one_due_gateH_entry_rel D R t ?after
        (one_due_reentry_context C u) branch'
        (one_due_reentry_snapshot C branch S)
        (one_due_reentry_generic_raw D C
          (one_due_event_remove_heap D C branch
            (one_due_generic_remove_heap D C
              (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
          generic_raw)
        (one_due_event_raw_after_remove D C branch event_raw)"
      using gate_after by (simp add: due_prefix_gate_inv_def)
    have observation_after:
      "TaskObservationRel D
        (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' t)) ?after"
      by (rule one_due_gateH_task_observationD[OF gate_rel_after])
    have decode_after: "scheduler_decode_rel D ?after"
      by (rule one_due_gateH_decoder_relD[OF gate_rel_after])
    have ptr_after:
      "strong_due_next_ptr_rel D (Some (Generic u))
        (sd_tcb_ptr D u)"
      by (simp add: strong_due_next_ptr_rel_def)
    have local_after:
      "\<exists>C' branch'' S' generic_raw' event_raw'.
        odc_task C' = u \<and>
        due_prefix_gate_inv D R t now entry
          (processed @ [Generic task]) (Generic u # remaining) future
          ?after C' branch'' S' generic_raw' event_raw'"
    proof -
      show ?thesis
      apply (rule exI[where x="one_due_reentry_context C u"])
      apply (rule exI[where x=branch'])
      apply (rule exI[where x="one_due_reentry_snapshot C branch S"])
      apply (rule exI[where x=
        "one_due_reentry_generic_raw D C
          (one_due_event_remove_heap D C branch
            (one_due_generic_remove_heap D C
              (hrs_mem (Scheduler_V611_Parse.globals.t_hrs_' c))))
          generic_raw"])
      apply (rule exI[where x=
        "one_due_event_raw_after_remove D C branch event_raw"])
      apply (rule conjI)
      subgoal by (simp add: one_due_reentry_context_components)
      subgoal by (rule gate_after)
      done
    qed
    show
      "StrongDuePrefixResultComponentPost D R now entry processed task u
        remaining future current managed termination r t"
      unfolding StrongDuePrefixResultComponentPost_def Let_def
      apply (intro conjI)
      subgoal by (rule result)
      subgoal by (rule exit_after)
      subgoal by (rule domain_after)
      subgoal by (rule control_frame)
      subgoal by (rule tick_after)
      subgoal by (rule quiet_after)
      subgoal by (rule pending_after)
      subgoal by (rule observation_after)
      subgoal by (rule decode_after)
      subgoal by (rule ptr_after)
      subgoal by (rule local_after)
      done
  qed
qed

text \<open>
  Named remaining obligation.  This is not used as a premise above: it is the
  postcondition the next footprint/frame theorem must establish.  Compared
  with StrongDuePrefixResultComponentPost it additionally requires:

    * GenericRootFamilyCoverage for every GenericRootUniverse root, including
      the unchanged termination root;
    * EventRootFamilyCoverage for pending plus every arbitrary external root,
      reconstructing the optional removed owner and framing all siblings;
    * strong generic/event role projections, wake payload projection and the
      one-due snapshot projection for the post families;
    * managed observations for retired as well as runnable tasks;
    * all concrete role/scalar/current/boundary pins and cross-family storage;
    * due_loop_core_wf and the successor due_loop_time_wf partition, not the
      stable core_wf/time_wf pair; core_wf is restored only after remaining
      becomes empty;
    * the explicit tail_cursor_wf termination conjunct already carried by
      strong_managed_domain_rel.
\<close>

definition DueLoopResultFamilyFramePost ::
  "'tid scheduler_decode \<Rightarrow> 32 word \<Rightarrow>
   'tid scheduler_abs \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid \<Rightarrow> 'tid \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid set \<Rightarrow> 'tid node_ring \<Rightarrow>
   xLIST_C ptr set \<Rightarrow>
   (unit, Scheduler_V611_Parse.tskTaskControlBlock_C ptr) xval \<Rightarrow>
   Scheduler_V611_Parse.globals \<Rightarrow> bool"
where
  "DueLoopResultFamilyFramePost D now entry processed task u
       remaining future managed termination external r t \<longleftrightarrow>
     r = Result (sd_tcb_ptr D u) \<and>
     (\<exists>phase next generic_raw generic_abs event_raw event_abs K_G K_E S.
       DueLoopStrongHeadRel D t
         (due_prefix_result_step_abs entry processed (Generic task))
         managed termination external generic_raw generic_abs
         event_raw event_abs K_G K_E S now entry
         (processed @ [Generic task]) (Generic u # remaining) future
         phase next (sd_tcb_ptr D u))"

end
