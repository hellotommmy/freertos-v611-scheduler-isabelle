# Resume managed outer-entry source factor — 2026-08-12

Baseline: `423e04e` on `agent/universal-scheduler-refinement`.

## Checked scope

This child closes the source-linkage boundary left intentionally open by the
managed outer-entry prefix theorem.  It defines the complete generated suffix
beginning immediately after the suspension decrement and proves the exact,
zero-premise program equality

`xTaskResumeAll' = bind resume_outer_generated_entry_prefix
  (lambda _. resume_outer_generated_entry_suffix)`.

The suffix retains the actual translated source order:

- the suspension-zero condition;
- the positive generated task-count condition;
- the pending-list guard and head read;
- the generated pending while loop with initial local yield word zero;
- the checked after-drain continuation;
- the final proof-port critical exit; and
- the returned `xAlreadyYielded` word.

The proof rewrites the already checked `xTaskResumeAll_program_eq`, unfolds the
three transparent program definitions, and uses only monadic bind
associativity.  It preserves Result, Exception, guard-failure, and no-success
paths and adds no scheduler-state premise.

This theorem is source factoring only.  It does not claim that all suffix
branches are yet composed into a whole-operation functional-correctness
theorem.

## Theorem-object audit

| theorem | premises | hidden hypotheses |
| --- | ---: | ---: |
| `xTaskResumeAll_generated_entry_prefix_factor` | 0 | 0 |

The embedded ML audit rejects any premise or hidden hypothesis.

## Checker evidence

The exclusive session
`EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Entry_Factor` has sole
parent `EAL6_FreeRTOS_V611_Scheduler_Resume_Managed_Outer_Entry`, one theory,
`document=false`, `quick_and_dirty=false`, `parallel_proofs=0`, and
`timeout=120`.

The first bounded run was green:

- run: `20260812Tresume-managed-outer-entry-factor-01-source-equality`
- `exit_code=0`
- `timed_out=false`
- `quick_and_dirty=false`
- `elapsed_seconds=279.288`
- parent replay: 11 s
- leaf: 3 s

Evidence hashes:

| object | SHA-256 |
| --- | --- |
| theory | `48133F761D72D95C61AC52E8ABAD6200F40575486567545EA089A93A9679E464` |
| `command.txt` | `E7E4F37C598638CB371B0613852D67CEDB050D92005E688E740FFA1AA178B275` |
| `status.txt` | `7FEAA14BDDC6C9B5556B150938AA5807DD70DA49B79E7996C21970BEFAA76AC0` |
| `stdout.log` | `1651B76D04546DA1BBAF7E3047D963A2C19DE3ECAEAE56ED382C94325DFDB808` |
| `stderr.log` | `7EB70257593DA06F682A3DDDA54A9D260D4FC514F645237F5CA74B08F8DA61A6` |

The frozen-layout ELF, frozen-layout ledger, and generated address
configuration hashes remained respectively
`DC830E50513384D712E0D1C68CB198EA656365F673D021C452D7D7EBD45C045A`,
`CA288A4CD2344BE979ADFA9DBF0298C6715F196D64AE472D173304289C4F2C02`,
and `27F74768E1DB1C3F8DBFCFC85371075192BB7D2544ED324DC81B65A9A2911712`.

## Exact remaining boundary

The actual generated function is now factored at the verified managed entry
cutpoint.  The remaining work is to compose the suffix: nested suspension,
outermost managed pending drain, safe/unsafe missed-tick replay, modular yield,
and the final public endpoint, followed by sequential and concurrent public
contracts.
