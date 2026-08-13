theory Scheduler_Delayed_Cursor_General_Unlocked_Pure_Entry
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Preservation.Scheduler_Delayed_Cursor_General_Preservation"
    "EAL6_FreeRTOS_V611_Scheduler_Unlocked_Tick_Pure_Entry_Phase.Scheduler_Unlocked_Tick_Pure_Entry_Phase"
begin

text \<open>
  The historical tick-entry phase is reused only on the proof-only canonical
  cursor shadow.  The resulting core/time facts are transported back to the
  real scheduler value.  In particular the delayed, pending, suspended and
  ready cursors in @{term "tick_role_entry_abs a"} are never normalised.
\<close>

lemma tick_role_entry_abs_ring_shape_wf_iff [simp]:
  "ring_shape_wf (tick_role_entry_abs a) \<longleftrightarrow> ring_shape_wf a"
  by (simp only: tick_role_entry_abs_eq_due_tick_entry_abs
      ring_shape_wf_def due_tick_entry_frames)

lemma tick_role_entry_abs_canonicalize_scheduler_cursors:
  "tick_role_entry_abs (canonicalize_scheduler_cursors a) =
   canonicalize_scheduler_cursors (tick_role_entry_abs a)"
  by (rule sym, rule canonicalize_scheduler_cursors_tick_role_entry_abs)

lemma due_tick_entry_abs_canonicalize_scheduler_cursors:
  "due_tick_entry_abs (canonicalize_scheduler_cursors a) =
   canonicalize_scheduler_cursors (due_tick_entry_abs a)"
  using tick_role_entry_abs_canonicalize_scheduler_cursors[of a]
  by simp

lemma tick_due_sequence_abs_canonicalize_scheduler_cursors [simp]:
  "tick_due_sequence_abs (canonicalize_scheduler_cursors a) =
   tick_due_sequence_abs a"
  unfolding tick_due_sequence_abs_def due_nodes_def
  by (simp add: due_tick_entry_abs_canonicalize_scheduler_cursors Let_def)

lemma tick_due_future_abs_canonicalize_scheduler_cursors [simp]:
  "due_future_nodes
      (sa_tick (tick_role_entry_abs (canonicalize_scheduler_cursors a)))
      (current_delayed_ring
        (tick_role_entry_abs (canonicalize_scheduler_cursors a))) =
   due_future_nodes
      (sa_tick (tick_role_entry_abs a))
      (current_delayed_ring (tick_role_entry_abs a))"
  unfolding due_future_nodes_def
  by (simp add: due_tick_entry_abs_canonicalize_scheduler_cursors Let_def)

lemma cursor_general_core_wf_tick_role_entry_ordered:
  assumes core: "cursor_general_core_wf a"
  shows
    "ordered_generic_delayed_ring
       (current_delayed_ring (tick_role_entry_abs a))"
proof -
  have shadow_core: "core_wf (canonicalize_scheduler_cursors a)"
    using core by (simp add: cursor_general_core_wf_def)
  have shadow_ordered:
    "ordered_generic_delayed_ring
       (current_delayed_ring
         (tick_role_entry_abs (canonicalize_scheduler_cursors a)))"
    using core_wf_due_tick_entry_ordered[OF shadow_core]
    by simp
  have shape_a: "ring_shape_wf a"
    using core by (simp add: cursor_general_core_wf_def)
  have shape_entry: "ring_shape_wf (tick_role_entry_abs a)"
    by (rule iffD2[OF tick_role_entry_abs_ring_shape_wf_iff shape_a])
  have wf_a: "xlist_wf (sa_delayed_a (tick_role_entry_abs a))"
    and wf_b: "xlist_wf (sa_delayed_b (tick_role_entry_abs a))"
    using shape_entry by (simp_all add: ring_shape_wf_def)
  have real_wf:
    "xlist_wf (current_delayed_ring (tick_role_entry_abs a))"
    using wf_a wf_b
    by (simp add: current_delayed_ring_def split: if_splits)
  have qeq:
    "current_delayed_ring
       (tick_role_entry_abs (canonicalize_scheduler_cursors a)) =
     clear_xlist_cursor
       (current_delayed_ring (tick_role_entry_abs a))"
    by (simp only: tick_role_entry_abs_canonicalize_scheduler_cursors
        current_delayed_ring_canonicalize_scheduler_cursors)
  have shadow_generic:
    "generic_ring
       (current_delayed_ring
         (tick_role_entry_abs (canonicalize_scheduler_cursors a)))"
    using shadow_ordered
    unfolding ordered_generic_delayed_ring_def by blast
  have real_generic:
    "generic_ring (current_delayed_ring (tick_role_entry_abs a))"
    using shadow_generic
    by (simp only: qeq generic_ring_def clear_xlist_cursor_fields)
  have shadow_sorted:
    "sorted
      (map
        (item_key
          (current_delayed_ring
            (tick_role_entry_abs (canonicalize_scheduler_cursors a))))
        (ring
          (current_delayed_ring
            (tick_role_entry_abs (canonicalize_scheduler_cursors a)))))"
    using shadow_ordered
    unfolding ordered_generic_delayed_ring_def by blast
  have real_sorted:
    "sorted
      (map (item_key (current_delayed_ring (tick_role_entry_abs a)))
        (ring (current_delayed_ring (tick_role_entry_abs a))))"
    using shadow_sorted
    by (simp only: qeq clear_xlist_cursor_fields)
  show ?thesis
    unfolding ordered_generic_delayed_ring_def
    using real_wf real_generic real_sorted by blast
qed

lemma cursor_general_core_wf_tick_role_entry_due_loop_core:
  assumes core: "cursor_general_core_wf a"
  shows "cursor_general_due_loop_core_wf (tick_role_entry_abs a)"
proof -
  have shadow_core: "core_wf (canonicalize_scheduler_cursors a)"
    and shape: "ring_shape_wf a"
    using core by (simp_all add: cursor_general_core_wf_def)
  have shadow_loop:
    "due_loop_core_wf
       (tick_role_entry_abs (canonicalize_scheduler_cursors a))"
    using core_wf_due_tick_entry_due_loop_core_wf[OF shadow_core]
    by simp
  have real_shape: "ring_shape_wf (tick_role_entry_abs a)"
    by (rule iffD2[OF tick_role_entry_abs_ring_shape_wf_iff shape])
  have canonical_loop:
    "due_loop_core_wf
       (canonicalize_scheduler_cursors (tick_role_entry_abs a))"
    using shadow_loop
    by (simp only: tick_role_entry_abs_canonicalize_scheduler_cursors)
  show ?thesis
    unfolding cursor_general_due_loop_core_wf_def
    by (rule conjI[OF canonical_loop real_shape])
qed

lemma cursor_general_core_wf_tick_role_entry_due_loop_time:
  assumes core: "cursor_general_core_wf a"
  shows
    "due_loop_time_wf
       (sa_tick (tick_role_entry_abs a))
       (tick_due_sequence_abs a)
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)))
       (tick_role_entry_abs a)"
proof -
  have shadow_core: "core_wf (canonicalize_scheduler_cursors a)"
    using core by (simp add: cursor_general_core_wf_def)
  have shadow_time:
    "due_loop_time_wf
       (sa_tick (tick_role_entry_abs
         (canonicalize_scheduler_cursors a)))
       (tick_due_sequence_abs (canonicalize_scheduler_cursors a))
       (due_future_nodes
         (sa_tick (tick_role_entry_abs
           (canonicalize_scheduler_cursors a)))
         (current_delayed_ring
           (tick_role_entry_abs (canonicalize_scheduler_cursors a))))
       (tick_role_entry_abs (canonicalize_scheduler_cursors a))"
    using core_wf_due_tick_entry_canonical_time_phase[OF shadow_core]
    by simp
  have state_eq:
    "tick_role_entry_abs (canonicalize_scheduler_cursors a) =
     canonicalize_scheduler_cursors (tick_role_entry_abs a)"
    by (rule tick_role_entry_abs_canonicalize_scheduler_cursors)
  have tick_eq:
    "sa_tick (tick_role_entry_abs (canonicalize_scheduler_cursors a)) =
     sa_tick (tick_role_entry_abs a)"
    using state_eq
    by (simp only: canonicalize_scheduler_cursors_frames)
  have sequence_eq:
    "tick_due_sequence_abs (canonicalize_scheduler_cursors a) =
     tick_due_sequence_abs a"
    by (rule tick_due_sequence_abs_canonicalize_scheduler_cursors)
  have future_eq:
    "due_future_nodes
       (sa_tick (tick_role_entry_abs (canonicalize_scheduler_cursors a)))
       (current_delayed_ring
         (tick_role_entry_abs (canonicalize_scheduler_cursors a))) =
     due_future_nodes
       (sa_tick (tick_role_entry_abs a))
       (current_delayed_ring (tick_role_entry_abs a))"
    by (rule tick_due_future_abs_canonicalize_scheduler_cursors)
  have canonical_tick_eq:
    "sa_tick (canonicalize_scheduler_cursors (tick_role_entry_abs a)) =
     sa_tick (tick_role_entry_abs a)"
    by (rule canonicalize_scheduler_cursors_frames(6))
  have canonical_future_eq:
    "due_future_nodes
       (sa_tick (canonicalize_scheduler_cursors (tick_role_entry_abs a)))
       (current_delayed_ring
         (canonicalize_scheduler_cursors (tick_role_entry_abs a))) =
     due_future_nodes
       (sa_tick (tick_role_entry_abs a))
       (current_delayed_ring (tick_role_entry_abs a))"
    by (simp only: canonicalize_scheduler_cursors_frames
        current_delayed_ring_canonicalize_scheduler_cursors
        due_future_nodes_def clear_xlist_cursor_fields)
  have canonical_ring_future_eq:
    "due_future_nodes
       (sa_tick (tick_role_entry_abs a))
       (current_delayed_ring
         (canonicalize_scheduler_cursors (tick_role_entry_abs a))) =
     due_future_nodes
       (sa_tick (tick_role_entry_abs a))
       (current_delayed_ring (tick_role_entry_abs a))"
    by (simp only: current_delayed_ring_canonicalize_scheduler_cursors
        due_future_nodes_def clear_xlist_cursor_fields)
  have canonical_time:
    "due_loop_time_wf
       (sa_tick (tick_role_entry_abs a))
       (tick_due_sequence_abs a)
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)))
       (canonicalize_scheduler_cursors (tick_role_entry_abs a))"
    using shadow_time
    by (simp only: state_eq sequence_eq canonical_tick_eq
        canonical_ring_future_eq)
  show ?thesis
    using canonical_time by simp
qed

theorem cursor_general_core_wf_tick_role_entry_canonical_phase:
  assumes core: "cursor_general_core_wf a"
  shows
    "cursor_general_due_loop_core_wf (tick_role_entry_abs a) \<and>
     ordered_generic_delayed_ring
       (current_delayed_ring (tick_role_entry_abs a)) \<and>
     due_loop_time_wf
       (sa_tick (tick_role_entry_abs a))
       (tick_due_sequence_abs a)
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)))
       (tick_role_entry_abs a)"
  using cursor_general_core_wf_tick_role_entry_due_loop_core[OF core]
    cursor_general_core_wf_tick_role_entry_ordered[OF core]
    cursor_general_core_wf_tick_role_entry_due_loop_time[OF core]
  by blast

corollary cursor_general_core_wf_tick_role_entry_loop_initial:
  assumes core: "cursor_general_core_wf a"
  shows
    "due_prefix_loop_inv (sa_tick (tick_role_entry_abs a))
       (tick_role_entry_abs a) [] (tick_due_sequence_abs a)
       (due_future_nodes (sa_tick (tick_role_entry_abs a))
         (current_delayed_ring (tick_role_entry_abs a)))
       (tick_role_entry_abs a)"
proof -
  have ordered_due:
    "ordered_generic_delayed_ring
       (current_delayed_ring (due_tick_entry_abs a))"
    using cursor_general_core_wf_tick_role_entry_ordered[OF core]
    by simp
  have initial:
    "due_prefix_loop_inv (sa_tick (due_tick_entry_abs a))
       (due_tick_entry_abs a) [] (due_tick_sequence_abs a)
       (due_future_nodes (sa_tick (due_tick_entry_abs a))
         (current_delayed_ring (due_tick_entry_abs a)))
       (due_tick_entry_abs a)"
    by (rule due_tick_loop_initial[OF ordered_due])
  show ?thesis using initial by simp
qed

end
