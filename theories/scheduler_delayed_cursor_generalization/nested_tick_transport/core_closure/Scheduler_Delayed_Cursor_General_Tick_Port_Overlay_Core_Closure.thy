theory Scheduler_Delayed_Cursor_General_Tick_Port_Overlay_Core_Closure
  imports
    "EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Tick_Rel_Spec_Probe.Scheduler_Delayed_Cursor_General_Tick_Rel_Spec_Probe"
begin

text \<open>
  The proof-port overlay writes only the interrupt mask and critical depth.
  These six generated scheduler selectors are therefore exact frames, and
  their record updaters commute with the overlay.  The heap frame is a
  semantic non-read fact used by generated list operations; it is not being
  replaced by a modifies theorem.
\<close>

lemma tick_port_overlay_core_selectors [simp]:
  "Scheduler_V611_Parse.globals.t_hrs_'
      (tick_port_overlay depth irq_mask c) =
    Scheduler_V611_Parse.globals.t_hrs_' c"
  "Scheduler_V611_Parse.globals.xTickCount_'
      (tick_port_overlay depth irq_mask c) =
    Scheduler_V611_Parse.globals.xTickCount_' c"
  "Scheduler_V611_Parse.globals.pxDelayedTaskList_'
      (tick_port_overlay depth irq_mask c) =
    Scheduler_V611_Parse.globals.pxDelayedTaskList_' c"
  "Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'
      (tick_port_overlay depth irq_mask c) =
    Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_' c"
  "Scheduler_V611_Parse.globals.xNumOfOverflows_'
      (tick_port_overlay depth irq_mask c) =
    Scheduler_V611_Parse.globals.xNumOfOverflows_' c"
  "Scheduler_V611_Parse.globals.uxTopReadyPriority_'
      (tick_port_overlay depth irq_mask c) =
    Scheduler_V611_Parse.globals.uxTopReadyPriority_' c"
  by (simp_all add: tick_port_overlay_def)

lemma tick_port_overlay_core_updates:
  "tick_port_overlay depth irq_mask
      (Scheduler_V611_Parse.globals.t_hrs_'_update f_hrs c) =
    Scheduler_V611_Parse.globals.t_hrs_'_update f_hrs
      (tick_port_overlay depth irq_mask c)"
  "tick_port_overlay depth irq_mask
      (Scheduler_V611_Parse.globals.xTickCount_'_update f_tick c) =
    Scheduler_V611_Parse.globals.xTickCount_'_update f_tick
      (tick_port_overlay depth irq_mask c)"
  "tick_port_overlay depth irq_mask
      (Scheduler_V611_Parse.globals.pxDelayedTaskList_'_update f_delayed c) =
    Scheduler_V611_Parse.globals.pxDelayedTaskList_'_update f_delayed
      (tick_port_overlay depth irq_mask c)"
  "tick_port_overlay depth irq_mask
      (Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'_update
        f_overflow_delayed c) =
    Scheduler_V611_Parse.globals.pxOverflowDelayedTaskList_'_update
      f_overflow_delayed
      (tick_port_overlay depth irq_mask c)"
  "tick_port_overlay depth irq_mask
      (Scheduler_V611_Parse.globals.xNumOfOverflows_'_update f_overflows c) =
    Scheduler_V611_Parse.globals.xNumOfOverflows_'_update f_overflows
      (tick_port_overlay depth irq_mask c)"
  "tick_port_overlay depth irq_mask
      (Scheduler_V611_Parse.globals.uxTopReadyPriority_'_update f_top c) =
    Scheduler_V611_Parse.globals.uxTopReadyPriority_'_update f_top
      (tick_port_overlay depth irq_mask c)"
  by (simp_all add: tick_port_overlay_def)

lemma tick_port_overlay_bisim_map_value:
  fixes p ::
    "('e::default, 'a, Scheduler_V611_Parse.globals) spec_monad"
    and f ::
    "('e, 'a) exception_or_result \<Rightarrow>
     ('f::default, 'b) exception_or_result"
  assumes p: "tick_port_overlay_bisim depth irq_mask p"
  shows "tick_port_overlay_bisim depth irq_mask (map_value f p)"
  using p
  by (simp add: tick_port_overlay_bisim_iff_run run_map_value
      map_post_state_comp fun_eq_iff comp_def split_beta')

lemma tick_port_overlay_bisim_liftE:
  fixes p :: "('a, Scheduler_V611_Parse.globals) res_monad"
  assumes p: "tick_port_overlay_bisim depth irq_mask p"
  shows
    "tick_port_overlay_bisim depth irq_mask
       (liftE p ::
         ('e, 'a, Scheduler_V611_Parse.globals) exn_monad)"
  unfolding liftE_def
  by (rule tick_port_overlay_bisim_map_value[OF p])

lemma tick_port_overlay_bisim_finally:
  fixes p ::
    "('a, 'a, Scheduler_V611_Parse.globals) exn_monad"
  assumes p: "tick_port_overlay_bisim depth irq_mask p"
  shows "tick_port_overlay_bisim depth irq_mask (finally p)"
  unfolding finally_def
  by (rule tick_port_overlay_bisim_map_value[OF p])

lemma tick_port_overlay_bisim_whileLoop:
  fixes C ::
      "'a \<Rightarrow> Scheduler_V611_Parse.globals \<Rightarrow> bool"
    and B ::
      "'a \<Rightarrow>
       ('e::default, 'a, Scheduler_V611_Parse.globals) spec_monad"
  assumes cond:
      "\<And>x c. C x (tick_port_overlay depth irq_mask c) = C x c"
    and body: "\<And>x. tick_port_overlay_bisim depth irq_mask (B x)"
  shows
    "tick_port_overlay_bisim depth irq_mask (whileLoop C B I)"
proof -
  let ?R = "tick_port_overlay_rel depth irq_mask"
  have loops:
    "rel_spec_monad ?R (rel_exception_or_result (=) (=))
       (whileLoop C B I) (whileLoop C B I)"
  proof (rule rel_spec_monad_whileLoop[
      where R = "(=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"])
    show "I = I"
      by simp
  next
    fix x y :: 'a
    assume xy: "x = y"
    show "rel_fun ?R (=) (C x) (C y)"
      using cond xy
      by (auto simp: rel_fun_def tick_port_overlay_rel_def)
  next
    fix x y :: 'a
    assume xy: "x = y"
    show
      "rel_spec_monad ?R (rel_exception_or_result (=) (=))
         (B x) (B y)"
      using body[of x] xy
      by (simp add: tick_port_overlay_bisim_def
          rel_exception_or_result_eq_conv)
  qed
  show ?thesis
    using loops
    by (simp add: tick_port_overlay_bisim_def
        rel_exception_or_result_eq_conv)
qed

end
