theory Scheduler_Unlocked_Tick_Pure_Entry_Phase
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Due_Prefix_Strong_While_Connector.Scheduler_Due_Prefix_Strong_While_Connector"
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Scaffold.Scheduler_Unlocked_Tick_Scaffold"
begin

text \<open>
  Pure entry phase for the generated unlocked tick prefix.  All tasks, rings,
  priorities, payloads, ticks and wrap choices remain symbolic.  The key wrap
  fact is derived from the stable pre-state: at the maximum word, the old
  current delayed ring must be empty because @{const time_wf} requires every
  one of its keys to be strictly greater than the current tick.

  This theory does not open generated source.  It establishes the canonical
  abstract due/future phase that the generated prefix theorem must expose.
\<close>

lemma tick_role_entry_abs_eq_due_tick_entry_abs [simp]:
  "tick_role_entry_abs s = due_tick_entry_abs s"
  by (simp add: tick_role_entry_abs_def due_tick_entry_abs_def)

lemma tick_due_sequence_abs_eq_due_tick_sequence_abs [simp]:
  "tick_due_sequence_abs s = due_tick_sequence_abs s"
  by (simp add: tick_due_sequence_abs_def due_tick_sequence_abs_def Let_def)

lemma word32_successor_strict:
  fixes w :: "32 word"
  assumes no_wrap: "w + 1 \<noteq> 0"
  shows "w < w + 1"
proof -
  have successor: "unat (w + 1) = Suc (unat w)"
    using no_wrap by (metis add.commute unatSuc)
  show ?thesis
    using successor by (simp add: word_less_nat_alt)
qed

lemma due_tick_entry_frames [simp]:
  "sa_live (due_tick_entry_abs s) = sa_live s"
  "sa_priority (due_tick_entry_abs s) = sa_priority s"
  "sa_wake (due_tick_entry_abs s) = sa_wake s"
  "sa_event_waiting (due_tick_entry_abs s) = sa_event_waiting s"
  "sa_ready (due_tick_entry_abs s) = sa_ready s"
  "sa_delayed_a (due_tick_entry_abs s) = sa_delayed_a s"
  "sa_delayed_b (due_tick_entry_abs s) = sa_delayed_b s"
  "sa_pending (due_tick_entry_abs s) = sa_pending s"
  "sa_suspended (due_tick_entry_abs s) = sa_suspended s"
  "sa_missed_ticks (due_tick_entry_abs s) = sa_missed_ticks s"
  "sa_suspend_depth (due_tick_entry_abs s) = sa_suspend_depth s"
  "sa_missed_yield (due_tick_entry_abs s) = sa_missed_yield s"
  "sa_top_ready (due_tick_entry_abs s) = sa_top_ready s"
  "sa_current (due_tick_entry_abs s) = sa_current s"
  "sa_yield_count (due_tick_entry_abs s) = sa_yield_count s"
  by (simp_all add: due_tick_entry_abs_def swap_delayed_roles_def Let_def)

lemma due_tick_entry_no_wrap_delayed_roles:
  assumes no_wrap: "sa_tick s + 1 \<noteq> 0"
  shows
    "current_delayed_ring (due_tick_entry_abs s) =
       current_delayed_ring s \<and>
     overflow_delayed_ring (due_tick_entry_abs s) =
       overflow_delayed_ring s"
  using no_wrap
  by (simp add: due_tick_entry_abs_def current_delayed_ring_def
      overflow_delayed_ring_def Let_def)

lemma due_tick_entry_wrap_delayed_roles:
  assumes wrap: "sa_tick s + 1 = 0"
  shows
    "current_delayed_ring (due_tick_entry_abs s) =
       overflow_delayed_ring s \<and>
     overflow_delayed_ring (due_tick_entry_abs s) =
       current_delayed_ring s \<and>
     sa_tick (due_tick_entry_abs s) = 0"
proof -
  have current:
    "current_delayed_ring (due_tick_entry_abs s) =
       overflow_delayed_ring s"
    using wrap
    by (simp add: due_tick_entry_abs_def Let_def
        current_delayed_after_role_swap overflow_delayed_ring_def)
  have overflow:
    "overflow_delayed_ring (due_tick_entry_abs s) =
       current_delayed_ring s"
    using wrap
    by (simp add: due_tick_entry_abs_def Let_def
        overflow_delayed_after_role_swap current_delayed_ring_def)
  have tick: "sa_tick (due_tick_entry_abs s) = 0"
    using wrap due_tick_entry_tick by simp
  show ?thesis
    using current overflow tick by blast
qed

lemma core_wf_wrap_old_current_delayed_empty:
  assumes core: "core_wf s"
    and wrap: "sa_tick s + 1 = 0"
  shows "ring (current_delayed_ring s) = []"
proof (rule ccontr)
  assume nonempty: "ring (current_delayed_ring s) \<noteq> []"
  then obtain n ns where ring:
    "ring (current_delayed_ring s) = n # ns"
    by (cases "ring (current_delayed_ring s)") auto
  have role: "role_wf s"
    using core by (simp add: core_wf_def)
  have generic: "generic_ring (current_delayed_ring s)"
    using role
    by (cases "sa_current_role_a s")
       (simp_all add: role_wf_def current_delayed_ring_def)
  then obtain t where node: "n = Generic t"
    using ring by (auto simp: generic_ring_def)
  have member: "t \<in> generic_task_set (current_delayed_ring s)"
    using ring node by (auto simp: generic_task_set_def)
  have time: "time_wf s"
    using core by (simp add: core_wf_def)
  have temporal:
    "case sa_wake s t of
       None \<Rightarrow> False
     | Some k \<Rightarrow> sa_tick s < k"
    using time member by (auto simp: time_wf_def)
  then obtain k where wake: "sa_wake s t = Some k"
    and strict: "sa_tick s < k"
    by (cases "sa_wake s t") auto
  have maximum: "sa_tick s = (-1 :: 32 word)"
    by (rule max_word_wrap[OF wrap])
  have upper: "k \<le> sa_tick s"
    using maximum by simp
  show False
    using strict upper by auto
qed

lemma core_wf_physical_delayed_ordered:
  assumes core: "core_wf s"
  shows
    "ordered_generic_delayed_ring (sa_delayed_a s)"
    "ordered_generic_delayed_ring (sa_delayed_b s)"
  using core
  by (simp_all add: core_wf_def ordered_generic_delayed_ring_def
      ring_shape_wf_def role_wf_def time_wf_def)

lemma core_wf_due_tick_entry_ordered:
  assumes core: "core_wf s"
  shows
    "ordered_generic_delayed_ring
       (current_delayed_ring (due_tick_entry_abs s))"
proof -
  have a: "ordered_generic_delayed_ring (sa_delayed_a s)"
    by (rule core_wf_physical_delayed_ordered(1)[OF core])
  have b: "ordered_generic_delayed_ring (sa_delayed_b s)"
    by (rule core_wf_physical_delayed_ordered(2)[OF core])
  show ?thesis
    using a b
    by (cases "sa_current_role_a (due_tick_entry_abs s)")
       (simp_all add: current_delayed_ring_def)
qed

lemma due_tick_entry_due_loop_core_wf_iff [simp]:
  "due_loop_core_wf (due_tick_entry_abs s) \<longleftrightarrow>
   due_loop_core_wf s"
proof -
  let ?entry = "due_tick_entry_abs s"
  have ready_set: "ready_task_set ?entry = ready_task_set s"
    by (simp only: ready_task_set_def due_tick_entry_frames)
  have ring_shape: "ring_shape_wf ?entry \<longleftrightarrow> ring_shape_wf s"
    by (simp only: ring_shape_wf_def due_tick_entry_frames)
  have role: "role_wf ?entry \<longleftrightarrow> role_wf s"
    by (simp only: role_wf_def due_tick_entry_frames)
  have membership: "membership_wf ?entry \<longleftrightarrow> membership_wf s"
    unfolding membership_wf_def Let_def
    using ready_set by (simp only: due_tick_entry_frames)
  have ready_cache:
    "ready_cache_wf ?entry \<longleftrightarrow> ready_cache_wf s"
    unfolding ready_cache_wf_def
    by (simp only: due_tick_entry_frames)
  have current: "current_wf ?entry \<longleftrightarrow> current_wf s"
    unfolding current_wf_def
    by (simp only: due_tick_entry_frames)
  show ?thesis
    unfolding due_loop_core_wf_def
    using ring_shape role membership ready_cache current
    by (simp only: due_tick_entry_frames)
qed

lemma core_wf_due_tick_entry_due_loop_core_wf:
  assumes core: "core_wf s"
  shows "due_loop_core_wf (due_tick_entry_abs s)"
proof -
  have "due_loop_core_wf s"
    using core by (simp add: core_wf_def due_loop_core_wf_def)
  then show ?thesis by simp
qed

lemma ordered_due_future_node_is_generic:
  assumes ordered: "ordered_generic_delayed_ring q"
    and member: "n \<in> set (due_future_nodes now q)"
  shows "\<exists>t. n = Generic t"
proof -
  have decomposition:
    "ring q = due_nodes now q @ due_future_nodes now q"
    by (rule due_nodes_future_decomposition)
  have in_ring: "n \<in> set (ring q)"
    using member decomposition by auto
  show ?thesis
    using ordered in_ring
    by (auto simp: ordered_generic_delayed_ring_def generic_ring_def)
qed

lemma core_wf_due_tick_entry_overflow_past:
  assumes core: "core_wf s"
  shows
    "\<forall>t\<in>generic_task_set
        (overflow_delayed_ring (due_tick_entry_abs s)).
       case sa_wake (due_tick_entry_abs s) t of
         None \<Rightarrow> False
       | Some k \<Rightarrow> k < sa_tick (due_tick_entry_abs s)"
proof (cases "sa_tick s + 1 = 0")
  case True
  have roles:
    "overflow_delayed_ring (due_tick_entry_abs s) =
       current_delayed_ring s"
    using due_tick_entry_wrap_delayed_roles[OF True] by blast
  have empty: "ring (current_delayed_ring s) = []"
    by (rule core_wf_wrap_old_current_delayed_empty[OF core True])
  show ?thesis
    using roles empty by (auto simp: generic_task_set_def)
next
  case False
  have roles:
    "overflow_delayed_ring (due_tick_entry_abs s) =
       overflow_delayed_ring s"
    using due_tick_entry_no_wrap_delayed_roles[OF False] by blast
  have successor:
    "sa_tick s < sa_tick (due_tick_entry_abs s)"
    using word32_successor_strict[OF False] by simp
  have time: "time_wf s"
    using core by (simp add: core_wf_def)
  have old_past:
    "\<forall>t\<in>generic_task_set (overflow_delayed_ring s).
       case sa_wake s t of
         None \<Rightarrow> False
       | Some k \<Rightarrow> k < sa_tick s"
    using time by (simp add: time_wf_def)
  show ?thesis
  proof (intro ballI)
    fix t
    assume member:
      "t \<in> generic_task_set
        (overflow_delayed_ring (due_tick_entry_abs s))"
    have member_old:
      "t \<in> generic_task_set (overflow_delayed_ring s)"
      using member roles by simp
    have old: "case sa_wake s t of
        None \<Rightarrow> False
      | Some k \<Rightarrow> k < sa_tick s"
      by (rule bspec[OF old_past member_old])
    show "case sa_wake (due_tick_entry_abs s) t of
        None \<Rightarrow> False
      | Some k \<Rightarrow> k < sa_tick (due_tick_entry_abs s)"
    proof (cases "sa_wake s t")
      case None
      then show ?thesis using old by simp
    next
      case (Some k)
      have old_less: "k < sa_tick s"
        using old Some by simp
      have new_less: "k < sa_tick (due_tick_entry_abs s)"
        by (rule less_trans[OF old_less successor])
      show ?thesis using Some new_less by simp
    qed
  qed
qed

theorem core_wf_due_tick_entry_due_loop_time_wf:
  assumes core: "core_wf s"
  shows
    "due_loop_time_wf
       (sa_tick (due_tick_entry_abs s))
       (due_nodes (sa_tick (due_tick_entry_abs s))
         (current_delayed_ring (due_tick_entry_abs s)))
       (due_future_nodes (sa_tick (due_tick_entry_abs s))
         (current_delayed_ring (due_tick_entry_abs s)))
       (due_tick_entry_abs s)"
proof -
  let ?entry = "due_tick_entry_abs s"
  let ?now = "sa_tick ?entry"
  let ?q = "current_delayed_ring ?entry"
  let ?remaining = "due_nodes ?now ?q"
  let ?future = "due_future_nodes ?now ?q"
  have time: "time_wf s"
    using core by (simp add: core_wf_def)
  have agree_a:
    "delayed_key_agrees ?entry (sa_delayed_a ?entry)"
    using time by (simp add: time_wf_def delayed_key_agrees_def)
  have agree_b:
    "delayed_key_agrees ?entry (sa_delayed_b ?entry)"
    using time by (simp add: time_wf_def delayed_key_agrees_def)
  have sorted_a:
    "sorted (map (item_key (sa_delayed_a ?entry))
      (ring (sa_delayed_a ?entry)))"
    using time by (simp add: time_wf_def)
  have sorted_b:
    "sorted (map (item_key (sa_delayed_b ?entry))
      (ring (sa_delayed_b ?entry)))"
    using time by (simp add: time_wf_def)
  have ready_suspended:
    "\<forall>t\<in>ready_task_set ?entry \<union>
                generic_task_set (sa_suspended ?entry).
       sa_wake ?entry t = None"
    using time
    by (simp add: time_wf_def ready_task_set_def generic_task_set_def)
  have ordered: "ordered_generic_delayed_ring ?q"
    by (rule core_wf_due_tick_entry_ordered[OF core])
  have decomposition: "ring ?q = ?remaining @ ?future"
    by (rule due_nodes_future_decomposition)
  have remaining_phase:
    "\<forall>n\<in>set ?remaining.
       (\<exists>t. n = Generic t) \<and> item_key ?q n \<le> ?now"
  proof (intro ballI conjI)
    fix n
    assume member: "n \<in> set ?remaining"
    show "\<exists>t. n = Generic t"
      by (rule ordered_due_node_is_generic[OF ordered member])
    show "item_key ?q n \<le> ?now"
      by (rule due_nodes_member_is_due[OF member])
  qed
  have future_phase:
    "\<forall>n\<in>set ?future.
       (\<exists>t. n = Generic t) \<and> ?now < item_key ?q n"
  proof (intro ballI conjI)
    fix n
    assume member: "n \<in> set ?future"
    show "\<exists>t. n = Generic t"
      by (rule ordered_due_future_node_is_generic[OF ordered member])
    show "?now < item_key ?q n"
      by (rule ordered_due_future_all_future[OF ordered member])
  qed
  have overflow_past:
    "\<forall>t\<in>generic_task_set (overflow_delayed_ring ?entry).
       case sa_wake ?entry t of
         None \<Rightarrow> False
       | Some k \<Rightarrow> k < ?now"
    by (rule core_wf_due_tick_entry_overflow_past[OF core])
  show ?thesis
    unfolding due_loop_time_wf_def
    using agree_a agree_b sorted_a sorted_b ready_suspended decomposition
      remaining_phase future_phase overflow_past
    by blast
qed

corollary core_wf_due_tick_entry_canonical_time_phase:
  assumes core: "core_wf s"
  shows
    "due_loop_time_wf
       (sa_tick (due_tick_entry_abs s))
       (due_tick_sequence_abs s)
       (due_future_nodes (sa_tick (due_tick_entry_abs s))
         (current_delayed_ring (due_tick_entry_abs s)))
       (due_tick_entry_abs s)"
  using core_wf_due_tick_entry_due_loop_time_wf[OF core]
  by (simp add: due_tick_sequence_abs_def)

corollary core_wf_due_tick_loop_initial:
  assumes core: "core_wf s"
  shows
    "due_prefix_loop_inv (sa_tick (due_tick_entry_abs s))
       (due_tick_entry_abs s) [] (due_tick_sequence_abs s)
       (due_future_nodes (sa_tick (due_tick_entry_abs s))
         (current_delayed_ring (due_tick_entry_abs s)))
       (due_tick_entry_abs s)"
  by (rule due_tick_loop_initial[OF
        core_wf_due_tick_entry_ordered[OF core]])

theorem core_wf_due_tick_entry_canonical_phase:
  assumes core: "core_wf s"
  shows
    "due_loop_core_wf (due_tick_entry_abs s) \<and>
     ordered_generic_delayed_ring
       (current_delayed_ring (due_tick_entry_abs s)) \<and>
     due_loop_time_wf
       (sa_tick (due_tick_entry_abs s))
       (due_tick_sequence_abs s)
       (due_future_nodes (sa_tick (due_tick_entry_abs s))
         (current_delayed_ring (due_tick_entry_abs s)))
       (due_tick_entry_abs s)"
  using core_wf_due_tick_entry_due_loop_core_wf[OF core]
    core_wf_due_tick_entry_ordered[OF core]
    core_wf_due_tick_entry_canonical_time_phase[OF core]
  by blast

end
