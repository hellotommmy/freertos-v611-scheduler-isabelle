theory Scheduler_Due_Prefix_Exit_Aware_Invariant
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Invariant.Scheduler_Due_Prefix_Invariant"
begin

text \<open>
  Exit-aware pure control layer for the generated delayed-task loop.  It keeps
  the complete ghost ledger at every loop head: the already processed due
  prefix, the still-unprocessed due suffix, and the untouched future suffix.
  No task, key, priority, tick, queue length, cursor, heap address or wrap
  branch is fixed.

  The three phases deliberately follow source control, not just abstract
  queue shape.  Both DueGate and FutureExit have a nonempty next node, hence
  the generated while guard ``pxTCB is non-NULL'' is true.  A future head
  exits only after entering the body and taking its key comparison's Exn-unit
  branch.  Only EmptyExit has a null next node and leaves through the false
  while guard with a normal null result.  The enclosing exception handler
  normalises both terminal controls to the public unit result.

  The result/exn names below are a small pure control alphabet.  They record
  the exact generated-source obligations to be discharged later; they do not
  assert execution of the C-derived monad.
\<close>

datatype due_prefix_exit_phase =
    DueGate
  | FutureExit
  | EmptyExit

datatype due_prefix_bare_terminal =
    DueBareFutureExn
  | DueBareEmptyResultNull

datatype due_prefix_public_terminal =
    DuePublicResultUnit

fun due_prefix_exit_phase_of ::
  "'a list \<Rightarrow> 'a list \<Rightarrow> due_prefix_exit_phase"
where
  "due_prefix_exit_phase_of (n # remaining) future = DueGate"
| "due_prefix_exit_phase_of [] (n # future) = FutureExit"
| "due_prefix_exit_phase_of [] [] = EmptyExit"

fun due_prefix_next_node_of ::
  "'a list \<Rightarrow> 'a list \<Rightarrow> 'a option"
where
  "due_prefix_next_node_of (n # remaining) future = Some n"
| "due_prefix_next_node_of [] (n # future) = Some n"
| "due_prefix_next_node_of [] [] = None"

fun due_prefix_phase_guard :: "due_prefix_exit_phase \<Rightarrow> bool"
where
  "due_prefix_phase_guard DueGate = True"
| "due_prefix_phase_guard FutureExit = True"
| "due_prefix_phase_guard EmptyExit = False"

fun due_prefix_terminal_of_phase ::
  "due_prefix_exit_phase \<Rightarrow> due_prefix_bare_terminal option"
where
  "due_prefix_terminal_of_phase DueGate = None"
| "due_prefix_terminal_of_phase FutureExit = Some DueBareFutureExn"
| "due_prefix_terminal_of_phase EmptyExit =
     Some DueBareEmptyResultNull"

fun due_prefix_terminal_for_future ::
  "'a list \<Rightarrow> due_prefix_bare_terminal"
where
  "due_prefix_terminal_for_future [] = DueBareEmptyResultNull"
| "due_prefix_terminal_for_future (n # future) = DueBareFutureExn"

fun due_prefix_finally_of_phase ::
  "due_prefix_exit_phase \<Rightarrow> due_prefix_public_terminal option"
where
  "due_prefix_finally_of_phase DueGate = None"
| "due_prefix_finally_of_phase FutureExit = Some DuePublicResultUnit"
| "due_prefix_finally_of_phase EmptyExit = Some DuePublicResultUnit"

fun due_prefix_control_of_exit_phase ::
  "due_prefix_exit_phase \<Rightarrow> due_prefix_control"
where
  "due_prefix_control_of_exit_phase DueGate = DueLoopBodyResult"
| "due_prefix_control_of_exit_phase FutureExit = DueLoopFutureHeadExn"
| "due_prefix_control_of_exit_phase EmptyExit = DueLoopGuardNormal"

definition due_prefix_bare_terminal_rel ::
  "due_prefix_exit_phase \<Rightarrow> 'state \<Rightarrow>
   due_prefix_bare_terminal \<Rightarrow> 'state \<Rightarrow> bool"
where
  "due_prefix_bare_terminal_rel phase before outcome after \<longleftrightarrow>
     (phase = FutureExit \<and>
       outcome = DueBareFutureExn \<and> after = before) \<or>
     (phase = EmptyExit \<and>
       outcome = DueBareEmptyResultNull \<and> after = before)"

text \<open>
  The exit-aware invariant is the control refinement of the already checked
  arbitrary-prefix algebra.  Its explicit future parameter is not recomputed
  from the current residual queue: the base invariant pins it to the entry
  queue's canonical future suffix, so it is an exact untouched suffix
  throughout the fold.
\<close>

definition due_prefix_exit_inv ::
  "32 word \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid node_kind list \<Rightarrow>
   'tid node_kind list \<Rightarrow> 'tid scheduler_abs \<Rightarrow>
   due_prefix_exit_phase \<Rightarrow> 'tid node_kind option \<Rightarrow> bool"
where
  "due_prefix_exit_inv now entry processed remaining future current
       phase next \<longleftrightarrow>
     due_prefix_loop_inv now entry processed remaining future current \<and>
     phase = due_prefix_exit_phase_of remaining future \<and>
     next = due_prefix_next_node_of remaining future"

lemma due_prefix_exit_inv_baseD:
  assumes inv:
    "due_prefix_exit_inv now entry processed remaining future current
       phase next"
  shows
    "due_prefix_loop_inv now entry processed remaining future current"
  using inv by (simp add: due_prefix_exit_inv_def)

lemma due_prefix_exit_inv_phaseD:
  assumes inv:
    "due_prefix_exit_inv now entry processed remaining future current
       phase next"
  shows "phase = due_prefix_exit_phase_of remaining future"
  using inv by (simp add: due_prefix_exit_inv_def)

lemma due_prefix_exit_inv_nextD:
  assumes inv:
    "due_prefix_exit_inv now entry processed remaining future current
       phase next"
  shows "next = due_prefix_next_node_of remaining future"
  using inv by (simp add: due_prefix_exit_inv_def)

lemma due_prefix_exit_phase_DueGate_iff [simp]:
  "due_prefix_exit_phase_of remaining future = DueGate \<longleftrightarrow>
   remaining \<noteq> []"
  by (cases remaining; cases future) simp_all

lemma due_prefix_exit_phase_FutureExit_iff [simp]:
  "due_prefix_exit_phase_of remaining future = FutureExit \<longleftrightarrow>
   remaining = [] \<and> future \<noteq> []"
  by (cases remaining; cases future) simp_all

lemma due_prefix_exit_phase_EmptyExit_iff [simp]:
  "due_prefix_exit_phase_of remaining future = EmptyExit \<longleftrightarrow>
   remaining = [] \<and> future = []"
  by (cases remaining; cases future) simp_all

lemma due_prefix_next_node_None_iff [simp]:
  "due_prefix_next_node_of remaining future = None \<longleftrightarrow>
   remaining = [] \<and> future = []"
  by (cases remaining; cases future) simp_all

lemma due_prefix_guard_matches_next:
  "due_prefix_phase_guard
      (due_prefix_exit_phase_of remaining future) \<longleftrightarrow>
   due_prefix_next_node_of remaining future \<noteq> None"
  by (cases remaining; cases future) simp_all

lemma due_prefix_exit_phase_matches_existing_control:
  "due_prefix_control_of remaining future =
   due_prefix_control_of_exit_phase
     (due_prefix_exit_phase_of remaining future)"
  by (cases remaining; cases future) simp_all

lemma due_prefix_exit_phase_matches_existing_finally:
  "due_prefix_finally_returns (due_prefix_control_of remaining future) \<longleftrightarrow>
   due_prefix_exit_phase_of remaining future \<noteq> DueGate"
  by (cases remaining; cases future) simp_all

lemma due_prefix_exit_inv_control_cases:
  assumes inv:
    "due_prefix_exit_inv now entry processed remaining future current
       phase next"
  shows
    "(\<exists>n rest.
        remaining = n # rest \<and> phase = DueGate \<and> next = Some n) \<or>
     (\<exists>n rest.
        remaining = [] \<and> future = n # rest \<and>
        phase = FutureExit \<and> next = Some n) \<or>
     (remaining = [] \<and> future = [] \<and>
        phase = EmptyExit \<and> next = None)"
  using inv
  unfolding due_prefix_exit_inv_def
  by (cases remaining; cases future) auto

theorem due_prefix_exit_inv_initial:
  assumes ordered:
    "ordered_generic_delayed_ring (current_delayed_ring entry)"
  shows
    "due_prefix_exit_inv now entry []
       (due_nodes now (current_delayed_ring entry))
       (due_future_nodes now (current_delayed_ring entry)) entry
       (due_prefix_exit_phase_of
         (due_nodes now (current_delayed_ring entry))
         (due_future_nodes now (current_delayed_ring entry)))
       (due_prefix_next_node_of
         (due_nodes now (current_delayed_ring entry))
         (due_future_nodes now (current_delayed_ring entry)))"
  using due_prefix_loop_inv_initial[OF ordered]
  by (simp add: due_prefix_exit_inv_def)

theorem due_prefix_exit_inv_due_gateD:
  assumes inv:
    "due_prefix_exit_inv now entry processed remaining future current
       DueGate next"
  obtains n rest t where
      "remaining = n # rest"
      "next = Some n"
      "n = Generic t"
      "item_key (current_delayed_ring entry) n \<le> now"
proof -
  have base:
    "due_prefix_loop_inv now entry processed remaining future current"
    by (rule due_prefix_exit_inv_baseD[OF inv])
  have nonempty: "remaining \<noteq> []"
    using due_prefix_exit_inv_phaseD[OF inv]
    by (cases remaining; cases future) simp_all
  obtain n rest where remaining: "remaining = n # rest"
    using nonempty by (cases remaining) auto
  have next_eq: "next = Some n"
    using due_prefix_exit_inv_nextD[OF inv] remaining by simp
  have base_head:
    "due_prefix_loop_inv now entry processed (n # rest) future current"
    using base remaining by simp
  have head:
    "item_key (current_delayed_ring entry) n \<le> now \<and>
     (\<exists>t. n = Generic t)"
    using due_prefix_loop_inv_result_head[OF base_head] by blast
  then obtain t where
      generic: "n = Generic t"
    and due: "item_key (current_delayed_ring entry) n \<le> now"
    by blast
  show thesis
    by (rule that[OF remaining next_eq generic due])
qed

theorem due_prefix_exit_inv_due_gate_step:
  assumes inv:
    "due_prefix_exit_inv now entry processed remaining future current
       DueGate next"
  obtains n rest t where
      "remaining = n # rest"
      "next = Some n"
      "n = Generic t"
      "item_key (current_delayed_ring entry) n \<le> now"
      "due_prefix_exit_inv now entry (processed @ [n]) rest future
         (due_prefix_result_step_abs entry processed n)
         (due_prefix_exit_phase_of rest future)
         (due_prefix_next_node_of rest future)"
      "due_prefix_measure rest < due_prefix_measure remaining"
proof -
  obtain n rest t where
      remaining: "remaining = n # rest"
    and next_eq: "next = Some n"
    and generic: "n = Generic t"
    and due: "item_key (current_delayed_ring entry) n \<le> now"
    by (rule due_prefix_exit_inv_due_gateD[OF inv])
  have base:
    "due_prefix_loop_inv now entry processed (n # rest) future current"
    using due_prefix_exit_inv_baseD[OF inv] remaining by simp
  have post_base:
    "due_prefix_loop_inv now entry (processed @ [n]) rest future
       (due_prefix_result_step_abs entry processed n)"
    by (rule due_prefix_result_step_preserves_inv[OF base])
  have post:
    "due_prefix_exit_inv now entry (processed @ [n]) rest future
       (due_prefix_result_step_abs entry processed n)
       (due_prefix_exit_phase_of rest future)
       (due_prefix_next_node_of rest future)"
    using post_base by (simp add: due_prefix_exit_inv_def)
  have decrease:
    "due_prefix_measure rest < due_prefix_measure remaining"
    using remaining due_prefix_result_step_decreases[of rest n] by simp
  show thesis
    by (rule that[OF remaining next_eq generic due post decrease])
qed

theorem due_prefix_exit_inv_future_exitD:
  assumes inv:
    "due_prefix_exit_inv now entry processed remaining future current
       FutureExit next"
  obtains n rest where
      "remaining = []"
      "future = n # rest"
      "next = Some n"
      "now < item_key (current_delayed_ring entry) n"
      "\<forall>x\<in>set future.
         now < item_key (current_delayed_ring entry) x"
      "processed = due_nodes now (current_delayed_ring entry)"
      "current = due_prefix_fold_state entry
         (due_nodes now (current_delayed_ring entry))"
      "ring (current_delayed_ring current) = future"
      "due_prefix_phase_guard FutureExit"
      "due_prefix_terminal_of_phase FutureExit =
         Some DueBareFutureExn"
      "due_prefix_bare_terminal_rel FutureExit current
         DueBareFutureExn current"
      "due_prefix_finally_of_phase FutureExit =
         Some DuePublicResultUnit"
proof -
  have remaining: "remaining = []"
    using due_prefix_exit_inv_phaseD[OF inv]
    by (cases remaining) simp_all
  have future_nonempty: "future \<noteq> []"
    using due_prefix_exit_inv_phaseD[OF inv] remaining
    by (cases future) simp_all
  obtain n rest where future: "future = n # rest"
    using future_nonempty by (cases future) auto
  have next_eq: "next = Some n"
    using due_prefix_exit_inv_nextD[OF inv] remaining future by simp
  have base:
    "due_prefix_loop_inv now entry processed [] (n # rest) current"
    using due_prefix_exit_inv_baseD[OF inv] remaining future by simp
  note terminal = due_prefix_future_head_exception_exit[OF base]
  have head_future:
    "now < item_key (current_delayed_ring entry) n"
    using terminal by blast
  have all_future:
    "\<forall>x\<in>set future.
       now < item_key (current_delayed_ring entry) x"
    using terminal future by simp
  have processed:
    "processed = due_nodes now (current_delayed_ring entry)"
    using terminal by blast
  have current:
    "current = due_prefix_fold_state entry
       (due_nodes now (current_delayed_ring entry))"
    using terminal by blast
  have ring: "ring (current_delayed_ring current) = future"
    using terminal future by blast
  have guard: "due_prefix_phase_guard FutureExit"
    by simp
  have outcome:
    "due_prefix_terminal_of_phase FutureExit =
       Some DueBareFutureExn"
    by simp
  have unchanged_exn:
    "due_prefix_bare_terminal_rel FutureExit current
       DueBareFutureExn current"
    by (simp add: due_prefix_bare_terminal_rel_def)
  have public:
    "due_prefix_finally_of_phase FutureExit =
       Some DuePublicResultUnit"
    by simp
  show thesis
    by (rule that[OF remaining future next_eq head_future all_future processed
          current ring guard outcome unchanged_exn public])
qed

theorem due_prefix_exit_inv_empty_exitD:
  assumes inv:
    "due_prefix_exit_inv now entry processed remaining future current
       EmptyExit next"
  shows
    "remaining = [] \<and>
     future = [] \<and>
     next = None \<and>
     processed = due_nodes now (current_delayed_ring entry) \<and>
     current = due_prefix_fold_state entry
       (due_nodes now (current_delayed_ring entry)) \<and>
     ring (current_delayed_ring current) = [] \<and>
     \<not> due_prefix_phase_guard EmptyExit \<and>
     due_prefix_terminal_of_phase EmptyExit =
       Some DueBareEmptyResultNull \<and>
     due_prefix_bare_terminal_rel EmptyExit current
       DueBareEmptyResultNull current \<and>
     due_prefix_finally_of_phase EmptyExit =
       Some DuePublicResultUnit"
proof -
  have remaining: "remaining = []"
    using due_prefix_exit_inv_phaseD[OF inv]
    by (cases remaining) simp_all
  have future: "future = []"
    using due_prefix_exit_inv_phaseD[OF inv] remaining
    by (cases future) simp_all
  have next_eq: "next = None"
    using due_prefix_exit_inv_nextD[OF inv] remaining future by simp
  have base:
    "due_prefix_loop_inv now entry processed [] [] current"
    using due_prefix_exit_inv_baseD[OF inv] remaining future by simp
  note terminal = due_prefix_empty_normal_exit[OF base]
  show ?thesis
    using remaining future next_eq terminal
    by (auto simp: due_prefix_bare_terminal_rel_def)
qed

text \<open>
  Consuming the arbitrary remaining due suffix reaches one of exactly two
  terminal phases.  This is a list-parametric fold theorem, so it covers zero
  due nodes, a singleton, any finite all-due ring, and a due prefix followed by
  any nonempty future suffix without introducing separate fixed-size proof
  inventory.
\<close>

theorem due_prefix_exit_inv_consume_all_due_terminal:
  assumes inv:
    "due_prefix_exit_inv now entry processed remaining future current
       phase next"
  defines terminal_current:
    "terminal_current \<equiv>
       due_prefix_fold_state entry (processed @ remaining)"
  shows
    "due_prefix_exit_inv now entry (processed @ remaining) [] future
       terminal_current (due_prefix_exit_phase_of [] future)
       (due_prefix_next_node_of [] future) \<and>
     processed @ remaining =
       due_nodes now (current_delayed_ring entry) \<and>
     future = due_future_nodes now (current_delayed_ring entry) \<and>
     ring (current_delayed_ring terminal_current) = future \<and>
     due_prefix_exit_phase_of [] future \<noteq> DueGate \<and>
     due_prefix_terminal_of_phase (due_prefix_exit_phase_of [] future) =
       Some (due_prefix_terminal_for_future future) \<and>
     due_prefix_bare_terminal_rel
       (due_prefix_exit_phase_of [] future) terminal_current
       (due_prefix_terminal_for_future future) terminal_current \<and>
     due_prefix_finally_of_phase (due_prefix_exit_phase_of [] future) =
       Some DuePublicResultUnit"
proof -
  have base:
    "due_prefix_loop_inv now entry processed remaining future current"
    by (rule due_prefix_exit_inv_baseD[OF inv])
  have ordered:
    "ordered_generic_delayed_ring (current_delayed_ring entry)"
    using base
    unfolding due_prefix_loop_inv_def Let_def
    by blast
  have future_def:
    "future = due_future_nodes now (current_delayed_ring entry)"
    using base
    unfolding due_prefix_loop_inv_def Let_def
    by blast
  have due_split:
    "due_nodes now (current_delayed_ring entry) = processed @ remaining"
    by (rule due_prefix_loop_inv_due_splitD[OF base])
  have terminal_base:
    "due_prefix_loop_inv now entry (processed @ remaining) [] future
       (due_prefix_fold_state entry (processed @ remaining))"
    by (rule due_prefix_loop_inv_at_any_split[OF ordered future_def])
       (simp add: due_split)
  have terminal_inv:
    "due_prefix_exit_inv now entry (processed @ remaining) [] future
       terminal_current (due_prefix_exit_phase_of [] future)
       (due_prefix_next_node_of [] future)"
    using terminal_base
    by (simp add: due_prefix_exit_inv_def terminal_current)
  have terminal_ring:
    "ring (current_delayed_ring terminal_current) = future"
    using due_prefix_loop_inv_finished[OF terminal_base]
    unfolding terminal_current
    by blast
  have terminal_control:
    "due_prefix_exit_phase_of [] future \<noteq> DueGate \<and>
     due_prefix_terminal_of_phase (due_prefix_exit_phase_of [] future) =
       Some (due_prefix_terminal_for_future future) \<and>
     due_prefix_bare_terminal_rel
       (due_prefix_exit_phase_of [] future) terminal_current
       (due_prefix_terminal_for_future future) terminal_current \<and>
     due_prefix_finally_of_phase (due_prefix_exit_phase_of [] future) =
       Some DuePublicResultUnit"
    by (cases future)
       (simp_all add: due_prefix_bare_terminal_rel_def)
  have processed_all:
    "processed @ remaining =
       due_nodes now (current_delayed_ring entry)"
    using due_split by simp
  show ?thesis
    using terminal_inv processed_all future_def terminal_ring terminal_control
    by blast
qed

theorem due_prefix_exit_inv_terminal_cases:
  assumes inv:
    "due_prefix_exit_inv now entry processed remaining future current
       phase next"
    and terminal: "phase \<noteq> DueGate"
  shows
    "(\<exists>n rest.
        remaining = [] \<and> future = n # rest \<and>
        phase = FutureExit \<and> next = Some n \<and>
        now < item_key (current_delayed_ring entry) n \<and>
        due_prefix_bare_terminal_rel FutureExit current
          DueBareFutureExn current) \<or>
     (remaining = [] \<and> future = [] \<and>
        phase = EmptyExit \<and> next = None \<and>
        due_prefix_bare_terminal_rel EmptyExit current
          DueBareEmptyResultNull current)"
proof (cases phase)
  case DueGate
  then show ?thesis using terminal by simp
next
  case FutureExit
  have inv':
    "due_prefix_exit_inv now entry processed remaining future current
       FutureExit next"
    using inv FutureExit by simp
  obtain n rest where
      remaining: "remaining = []"
    and future: "future = n # rest"
    and next_eq: "next = Some n"
    and head_future:
      "now < item_key (current_delayed_ring entry) n"
    and unchanged:
      "due_prefix_bare_terminal_rel FutureExit current
        DueBareFutureExn current"
    using due_prefix_exit_inv_future_exitD[OF inv']
    by blast
  show ?thesis
    using FutureExit remaining future next_eq head_future unchanged by blast
next
  case EmptyExit
  have inv':
    "due_prefix_exit_inv now entry processed remaining future current
       EmptyExit next"
    using inv EmptyExit by simp
  have facts:
    "remaining = [] \<and> future = [] \<and> next = None \<and>
     due_prefix_bare_terminal_rel EmptyExit current
       DueBareEmptyResultNull current"
    using due_prefix_exit_inv_empty_exitD[OF inv']
    by blast
  show ?thesis using EmptyExit facts by blast
qed

text \<open>
  Deliberate boundary.  A generated-source lifting still needs a strong
  snapshot relation indexed by processed, remaining and future.  That
  relation must connect the concrete pxTCB local to due_prefix_next_node_of,
  preserve every represented Generic and Event root plus
  cursors/counts/payloads, carry tick/root-role/scalar globals, and reconstruct
  the abstract scheduler endpoint.  Gate-H observes enough to execute one due
  task, but by itself is not that whole-scheduler relation.

  The missing semantic connector is therefore a preservation theorem for that
  strong relation across the existing one-due generated Result step, followed
  by two source terminal theorems: FutureExit maps a non-NULL future node to
  a state-unchanged Exn-unit outcome; EmptyExit maps NULL to a state-unchanged
  normal null result.  Only after composing the real generated while and its
  exception handler may these pure controls be reported as vTaskIncrementTick
  functional correctness.
\<close>

end
