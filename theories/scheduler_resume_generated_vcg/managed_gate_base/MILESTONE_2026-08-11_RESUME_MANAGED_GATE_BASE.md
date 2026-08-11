# Resume managed gate base — 2026-08-11

Baseline: `892fc08e2a7430d150d543eb2677738af5dcef64` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child introduces the parallel cursor-general managed Resume
gate required before any new outer composition.

`CursorGeneralStrongProtectedSchedulerSnapshotRel` retains a full public
`CursorGeneralStrongSchedulerSnapshotRel` witness and overlays only the actual
proof-port critical depth and interrupt mask.  The public managed gate fixes
that protected cutpoint to 1/1, requires abstract suspension depth zero, and
requires a current task only when the pending ring is nonempty.  It does not
include `resume_pending_gate_entry_rel` and does not require
`tick_entry_pending_wf` while pending work remains.

The checked projections establish:

1. the full managed domain, including symbolic termination and external Event
   roots, survives behind the protected shadow;
2. the actual state has proof-port depth 1, interrupt mask 1, and
   `xSchedulerRunning = 1`;
3. nonempty pending work has a public-live current task;
4. every task represented in the pending Event ring belongs to `sa_live` even
   though the decoder/family domain remains the larger `managed` set;
5. combining this gate with any legacy Resume gate, even one using unrelated
   raw-family witnesses, forces `managed = sa_live`; consequently a nonempty
   termination ring forbids every such legacy-gate witness.

The last diagnostic is why the future phase adapter and body/drain proofs must
be parallel managed results rather than extensions of the old gate.

## Theorem-object audit

Every audited theorem has zero hidden hypotheses.

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongProtectedSchedulerSnapshotRelI` | 2 |
| `CursorGeneralStrongProtectedSchedulerSnapshotRelD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRelI` | 3 |
| `CursorGeneralStrongResumePendingManagedGateRelD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_managed_domainD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_port_runningD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_current_liveD` | 2 |
| `CursorGeneralStrongResumePendingManagedGateRel_pending_liveD` | 1 |
| `CursorGeneralStrongResumePendingManagedGateRel_old_gate_forces_no_retired` | 2 |
| `CursorGeneralStrongResumePendingManagedGateRel_retired_forbids_old_gate` | 2 |

The exact ledger is `2/1/3/1/1/1/2/1/2/2`.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Gate_Base` has sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Pending_Control_Frame` and the smallest
side dependency that supplies the protected cursor-general snapshot,
`EAL6_FreeRTOS_V611_Scheduler_Delayed_Cursor_General_Nested_Tick_Overlay`.
It has one theory and sets `document=false`, `quick_and_dirty=false`, and
`parallel_proofs=0`.  Its original session `timeout=60` admitted the initial
58-second green run but was too tight for later cold parent-heap promotion.
The bound is now 120 seconds; the measured promotion completed in 69 seconds.
The repository wrapper bound remains 300 seconds and the checker command uses
`-o quick_and_dirty=false -j 1`.

The first cold attempt still used the broader First_Unsafe side dependency and
hit the Isabelle session timeout before reporting a proof location.  The
second run narrowed the side dependency, changed elimination destructors to
one-premise existential results, quantified independent legacy-family
witnesses, and exported pending membership as a set-level fact.  It was green:

| run | exit | wrapper | leaf | result |
| --- | ---: | ---: | ---: | --- |
| `20260811Tresume-managed-gate-base-01-cold` | 142 | 221.605 s | timeout | session timeout |
| `20260811Tresume-managed-gate-base-02-minimal-side` | 0 | 189.602 s | 58 s | green |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `5F52EC97BE53655E917A67C4942403DEA6E0C9670F500406E3B55E690AD2E58A` |
| `command.txt` | `000AA1D45D2380629F797B923BDA6D865A3B325D83047190F557963003DABA91` |
| `status.txt` | `6AF819B843328DA7CD5595AA060719ACFE13B81B878C079252BF93462641B149` |
| `stdout.log` | `0FC21C98BECD8936CF46C0021B107D2FCFF7CC145430089197C7AAF2912AFE66` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next exclusive child is the proof-only managed pending phase adapter.  It
must construct/alignment-carry canonical pending tasks, the full managed root
universes, families, payload maps, priorities, owners, and top cache while
keeping `set (rpc_tasks C) \<subseteq> sa_live a` separate from
`rpc_live C = managed`.  It must not contain the legacy gate.  Once that
adapter and its re-entry preservation are green, prove the parallel managed
body/list drain, empty exit to protected tick entry, and only then the new
managed outer composition and safe/unsafe replay continuation.
