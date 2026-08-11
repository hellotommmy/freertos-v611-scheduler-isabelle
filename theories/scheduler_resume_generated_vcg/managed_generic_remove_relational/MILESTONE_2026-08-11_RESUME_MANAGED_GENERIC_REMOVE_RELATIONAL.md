# Resume managed Generic-remove relational cutpoint — 2026-08-11

Baseline: `5a6adc4619d4ab1cc66658548b8aa04d540a127d` on
`agent/universal-scheduler-refinement`.

## Checked scope

This exclusive child classifies the exact transient state after both pending
head list removals, without yet composing the two generated source calls.  From
the managed phase and `rpc_tasks C = t # rest`, it proves six facts on the
Generic-removed heap:

- complete Generic coverage for the updated raw and abstract Generic families;
- complete Event coverage framed across the Generic removal;
- preserved managed task observation;
- reconstructed Generic/Event cross-storage separation from the two post
  coverages;
- `raw_family_globally_unlinked` for the removed Generic item; and
- the generated `RP_GenericUnlinked` phase invariant.

The globally-unlinked fact is exported explicitly because coverage and
observation alone do not provide the freshness premise needed by the later
ready insertion.  It follows from
`scheduler_family_remove_pre_rel_and_unlinked` and is transported to the exact
generated post transformers.  No legacy Resume gate, managed/live collapse,
or full transient scheduler snapshot is used.

## Theorem-object audit

The capstone and all six projections have zero hidden hypotheses and exactly
two premises: the managed phase and nonempty task-list equation.

| theorem | premises |
| --- | ---: |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_relational` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_generic_coverageD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_event_coverageD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_observationD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_cross_storageD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generic_remove_globally_unlinkedD` | 2 |
| `CursorGeneralStrongResumePendingManagedPhaseRel_generic_unlinkedD` | 2 |

The exact ledger is `2/2/2/2/2/2/2`, with `0` hidden hypotheses throughout.

## Checker topology and evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Generic_Remove_Relational` has
sole parent
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Generic_Remove_After_Event`, one
theory, `document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.  Its sole-parent import already contains all generic frame,
coverage, observation, and phase-step support.  The repository wrapper
remained bounded at 300 seconds and used `-o quick_and_dirty=false -j 1`.

The first run was green:

| run | exit | wrapper | result |
| --- | ---: | ---: | --- |
| `20260811Tresume-managed-generic-remove-relational-01-six-relations` | 0 | 170.025 s | green; parent 9 s, leaf 3 s |

Final evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `CEFF02C57383F575CF0014C06A2AC1DA1506B1F3404748A50E473BB23C067075` |
| `command.txt` | `D53FE6C2FD6248BA94488C8C6C14AFADEF9AA02F7FDD7A4B6EB1059358068DAA` |
| `status.txt` | `4D4C735F36D369F61E09ED1BA442C5931DB873724EE066DEC437FB076761C5FA` |
| `stdout.log` | `1E5DA96A403ED505407CA82A2EFC37A1B04F39EEA4E53E9B41DF720B2CB541D7` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

## Exact remaining boundary

The next thin child may compose the already-green generated Event and Generic
remove source theorems into one exact two-unlink bind, while consuming this
relational cutpoint only as the semantic interface for later work.  Ready
insertion, top/scalar/yield effects, managed re-entry, and loop induction
remain later rungs.
