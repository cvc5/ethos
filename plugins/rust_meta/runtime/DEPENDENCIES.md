Copied from Pathos at `f77aff7a457a73fb1708b8867d76f21e50fef081`.
The generated crate uses the same pinned dependency graph through its copied
number runtime. References below to Pathos crates and measured platform
reachability describe the upstream audit; they are not new reachability
measurements of this generated checker.

# Dependencies and their unsafe code

pathos forbids `unsafe` code in its own crates. This file accounts for the
`unsafe` code in every dependency, direct and indirect, as listed in
`Cargo.lock`. See "Memory safety" in [brief.md](brief.md).

For each dependency: its version, whether it contains `unsafe` code, where,
whether pathos can reach that code, and why it is acceptable. Adding a
dependency that contains `unsafe` code or binds C code needs the user's
agreement.

**Status (2026-11-14, milestone 15): option 0 chosen, pinned; approved by
Daniel Larraz on 2026-11-14 (recorded at his request).** Milestone 15 added the trace on the other
five platforms ("[On the other platforms](#on-the-other-platforms)"): the
decision is the one of milestone 14, and the text under it now covers arm64,
where the `unsafe` lines in the binaries are different ones. The list matches `Cargo.lock`, which has
not changed since milestone 1: twelve crates from the registry, all brought
in by `malachite`. The brief agreed to `malachite` knowing of one `unsafe`
use, the AVX2 FFT in `malachite-nz`. `malachite` also brings nine crates of
its own, none of them optional, and all nine contain `unsafe` code. None of
the twelve binds C or C++ code, and none has a build script that compiles
any. The [decision](#decision) is to keep `malachite` as it is, at exactly
these versions; the [options](#options-considered) record what else was
looked at.

In short: of the nine, five (`hashbrown`, `foldhash`, `either`, `libm`,
`ryu`) contribute no code at all to the binaries. The `unsafe` code that is
in the binaries all lies behind one door, the FFT multiplication, which
`malachite-nz` uses for numbers of about 25,000 bits and more: 17 source
lines with instructions of their own (`malachite-nz` 4, `bytemuck` 4,
`wide` 3, `safe_arch` 6), and with them four `unsafe` items that emit no
instruction but on which soundness depends (a second call site of the AVX2
kernels, two marker-trait impls, and one zero-initialisation in `wide`).
An input can open that door (a decimal literal of 17,602 digits does); no
case of any gate but `bignum`, which is there for it, does. What can go
wrong in that code is a wrong product, not a memory error; the large-number
cases compare the products with Ethos. These counts are for x86-64 Linux
and Windows. On arm64 the door is the same and behind it are 10 or 11 lines
of `wide` alone; on x86-64 macOS there are 19.

## Direct dependencies

Only `pathos-term` has external dependencies, and only
`crates/pathos-term/src/num.rs` names them.

| Crate | Version | `unsafe` code | Where, and why acceptable |
| --- | --- | --- | --- |
| `malachite-base` | 0.14.0 | none | `#![forbid(unsafe_code)]`. Used for the arithmetic traits. |
| `malachite-nz` | 0.14.0 | 8 lines in 2 files | `#![deny(unsafe_code)]`, allowed only in `natural/arithmetic/mul/fft/avx2.rs` (the vector type the AVX2 kernels use: four operator impls that call an intrinsic each, and two marker-trait impls for `bytemuck`) and at the two places in `fft/mod.rs` that call the AVX2 kernels after a run-time check that the CPU has AVX2 and FMA. Its build script compiles nothing: it only sets the `cfg` flag that includes the AVX2 kernels. The `unsafe` in `conversion/pyo3.rs` is behind the `enable_pyo3` feature, which pathos does not enable. This is the case the brief accepted. |
| `malachite-q` | 0.14.0 | none | `#![forbid(unsafe_code)]`. |

## Indirect dependencies

All of these come from `malachite` and cannot be turned off with features.

| Crate | Version | Needed by | `unsafe` code | Where | Reached by pathos? |
| --- | --- | --- | --- | --- | --- |
| `hashbrown` | 0.16.1 | `malachite-base` | yes, throughout (325 lines in 18 files) | The hash table behind `std::collections::HashMap`; the standard library ships the same code. | **Not reached**: no code in the binaries. |
| `foldhash` | 0.2.0 | `hashbrown` | 10 lines in 3 files | The default hasher of `hashbrown`: unaligned reads of byte slices and a seed kept in a static. | **Not reached**: no code in the binaries. |
| `itertools` | 0.14.0 | all three `malachite` crates | 10 lines in 2 files | `next_array.rs` (filling a `MaybeUninit` array) and `either_or_both.rs` (`unreachable_unchecked` after a check). | **Not reached**: four lines of `itertools` are in the binaries (`repeat_n` and `collect_vec`, used by bit operations, digit conversion and polynomial evaluation); none is `unsafe`, and neither file above is among them. |
| `either` | 1.19.0 | `itertools` | 2 lines in 1 file | Pin projection for `Either`. | **Not reached**: no code in the binaries. |
| `libm` | 0.2.16 | all three `malachite` crates | 56 lines in 9 files | Pure-Rust floating-point functions. The `unsafe` is CPU feature detection and x86/aarch64 intrinsics for `sqrt`, `fma` and rounding. Its build script only sets `cfg` flags. | **Not reached**: no code in the binaries. (With the `std` feature, which pathos uses, `malachite` takes these functions from the standard library.) |
| `ryu` | 1.0.23 | `malachite-base` | 27 lines in 10 files | Float-to-string conversion, writing digits through raw pointers into a fixed buffer. | **Not reached**: no code in the binaries. pathos converts no floats. |
| `wide` | 1.7.1 | `malachite-nz` | yes (443 lines in 34 files) | SIMD vector types. Mostly transmutes between vectors and arrays of the same size, and calls into `safe_arch`. | **Reached only through the FFT, and only on a CPU without AVX2 and FMA.** 42 lines are in the binaries, 3 of them `unsafe` (`simd.rs`: making a vector from an array and back, and copying a slice into one), all inside the 52 functions of the FFT's baseline kernels. |
| `safe_arch` | 1.2.0 | `wide` | yes, throughout (1,157 lines in 30 files) | Wrappers that expose CPU intrinsics as safe functions, each compiled only when the target has the CPU feature. | **Reached only through the FFT, and only on a CPU without AVX2 and FMA.** 6 lines are in the binaries, all `unsafe`: the SSE2 add, subtract, multiply, compare and xor of two doubles (`sse2.rs`). SSE2 is part of every x86-64 CPU, so these intrinsics are always valid. |
| `bytemuck` | 1.25.2 | `malachite-nz`, `wide`, `safe_arch` | yes (323 lines in 13 files) | Checked casts between plain-data types; the `unsafe` is the implementation of those checks and the marker traits. | **Reached only through the FFT, and only on a CPU with AVX2 and FMA.** 5 lines are in the binaries, 4 of them `unsafe` (`cast` and `pod_read_unaligned`, between `[f64; 4]` and the 256-bit vector), all inside the AVX2 kernels. |

The line counts are of lines that contain the word `unsafe` outside
comments and lint attributes, in each crate's `src/`.

The standard library is not in the table. It contains `unsafe` code, as
every Rust program's does, and pathos uses it through its safe interface.

## What pathos reaches

pathos calls `malachite` for parsing and printing integers, addition,
multiplication, powers, floor division, bit operations and shifts, and the
same on rationals. All the calls are in `crates/pathos-term/src/num.rs`.

### Method

Three kinds of evidence, each rerunnable.

1. **What is in the binaries.** `scripts/unsafe-reach` builds `pathos` and
   `pathos-eoc` in release mode with debug information, disassembles them,
   and maps every instruction to its source lines, including the lines of
   the functions inlined there (`addr2line -i`). The linker drops every
   function nothing refers to. So a source line of a dependency that has no
   instruction in a binary cannot run, whatever the input. This is where
   "no code in the binaries" in the table comes from, and the counts of
   lines. The script prints, per crate, the lines with code and those of
   them inside an `unsafe` block, function or impl. Both binaries give the
   same list (454,853 and 566,294 instructions):

   ```
   bytemuck-1.25.2: 5 lines with code, 4 of them unsafe
       src/internal.rs: 112 123
       src/lib.rs: 343 378
   itertools-0.14.0: 4 lines with code, 0 of them unsafe
   malachite-base-0.14.0: 406 lines with code, 0 of them unsafe
   malachite-nz-0.14.0: 9117 lines with code, 4 of them unsafe
       src/natural/arithmetic/mul/fft/avx2.rs: 182 192 202
       src/natural/arithmetic/mul/fft/mod.rs: 2036
   malachite-q-0.14.0: 143 lines with code, 0 of them unsafe
   safe_arch-1.2.0: 6 lines with code, 6 of them unsafe
       src/x86_x64/sse2.rs: 77 584 703 1825 2808 3048
   wide-1.7.1: 42 lines with code, 3 of them unsafe
       src/simd.rs: 110 386 402
   ```

   `hashbrown`, `foldhash`, `either`, `libm` and `ryu` do not appear. (The
   `hashbrown` symbols a debugger shows in the binary are the standard
   library's own copy, behind `HashMap`.)

2. **Where the remaining `unsafe` lines sit.** For every instruction that
   comes from one of the lines above, the function of the binary that
   contains it: all are in `malachite_nz::natural::arithmetic::mul::fft`.
   The lines of `wide` and `safe_arch` are in `fft::baseline::body` (52
   functions), those of `bytemuck` and of `avx2.rs` in `fft::avx2::body`
   (56 functions), and `fft/mod.rs:2036` is the call into the AVX2 kernels.
   Those kernels have two entry points, `mpn_ctx_mpn_mul` and
   `fmpz_poly_mul_mid_mpn_ctx` in `fft/mod.rs`, and each picks the AVX2
   kernels when the CPU has AVX2 and FMA and the baseline kernels
   otherwise. `malachite-nz` multiplies with the FFT when both numbers have
   more than 389 64-bit words (`MUL_FFT_THRESHOLD` in `platform_64.rs`,
   and the same for squaring), which is about 25,000 bits or 7,500 decimal
   digits; its division, radix conversion and powers multiply too.

3. **Whether a run goes there.** A copy of pathos built against a copy of
   `malachite-nz` in which those two entry points append a line to a log
   file before they do anything else (a `[patch.crates-io]` entry in a
   scratch copy of the workspace; nothing else changed).
   - Inputs made for it do reach the FFT. The smallest found: a decimal
     literal of 17,602 digits (parsing it multiplies), `(eo::pow 10 21408)`,
     and `eo::mul` of two numbers of 26,000 and 27,000 bits. On the
     development machine, which has AVX2, the log shows the AVX2 kernels.
     Ethos accepts the same inputs.
   - The gates do not: with the instrumented binaries, `scripts/difftest`
     `tests`, `proofs`, `large`, `fuzz` and `eoc` passed and the log stayed
     empty. No regression, no cvc5 proof (the 43 large ones included), no
     saved fuzzing finding and no eoc case multiplies numbers that large.

### Result

| Crate | `unsafe` code reached? | Evidence |
| --- | --- | --- |
| `malachite-base`, `malachite-q` | has none | `forbid(unsafe_code)` |
| `malachite-nz` | **Reached** by inputs with numbers of about 25,000 bits or more, on a CPU with AVX2 and FMA; by no gate case | 1, 2, 3 |
| `bytemuck` | **Reached**, under the same condition (it is used by the AVX2 kernels only) | 1, 2, 3 |
| `wide`, `safe_arch` | **Reached** by the same inputs, on a CPU without AVX2 or FMA (the baseline kernels); not on the development machine, so read, not run | 1, 2 |
| `itertools` | **Not reached**: its `unsafe` lines have no code in the binaries | 1 |
| `hashbrown`, `foldhash`, `either`, `libm`, `ryu` | **Not reached**: no code of theirs is in the binaries | 1 |

Nothing is left as "not known". The limits of the method: it describes the
binaries of one build (release profile, rustc 1.99.1). The text above is
for x86-64 Linux; the next section has the other five platforms pathos is
built for.

What the reached `unsafe` code is: arithmetic on vectors of four doubles.
The AVX2 kernels call the AVX2 and FMA intrinsics, which are sound exactly
when the CPU has those features, and `fft/mod.rs` checks that before every
call. `bytemuck`'s casts are between `[f64; 4]` and a 256-bit vector, types
of the same size without invalid bit patterns. `safe_arch`'s six lines are
SSE2 arithmetic, sound on every x86-64 CPU. None of it handles pointers or
lengths that come from the input: the kernels index their buffers with
ordinary bounds-checked slices.

### On the other platforms

CI runs `scripts/unsafe-reach` on each of the six platforms Ethos is built
for (job `platforms`, step "List the dependency code in the binaries"),
on the statically linked release build of that platform. Evidence 1 is
therefore from each platform. Evidence 2 and 3 (which function, and the
instrumented run) were done on x86-64 Linux only; elsewhere, that the
lines sit behind the FFT follows from the source, and that the FFT runs
and multiplies correctly is what the `bignum` gate shows on each platform
(7 cases, all the same as Ethos, on all six). The numbers are from run
43634777751 (commit `3579f6b`); `pathos` and `pathos-eoc` give the same
lines everywhere.

`unsafe` lines with code, by platform:

| Platform (Rust target) | `malachite-nz` | `bytemuck` | `safe_arch` | `wide` | Total |
| --- | --- | --- | --- | --- | --- |
| Linux x86-64 (`x86_64-unknown-linux-gnu`) | 4 | 4 | 6 | 3 | 17 |
| Windows x86-64 (`x86_64-pc-windows-msvc`) | 4 | 4 | 6 | 3 | 17 |
| macOS x86-64 (`x86_64-apple-darwin`) | 4 | 4 | 7 | 4 | 19 |
| Linux arm64 (`aarch64-unknown-linux-gnu`) | 0 | none in the binary | not built | 10 | 10 |
| Windows arm64 (`aarch64-pc-windows-msvc`) | 0 | none in the binary | not built | 10 | 10 |
| macOS arm64 (`aarch64-apple-darwin`) | 0 | none in the binary | not built | 11 | 11 |

`hashbrown`, `foldhash`, `either`, `libm` and `ryu` contribute no code on
any of the six, and `itertools` no `unsafe` line.

**x86-64.** Windows has exactly the lines of Linux. macOS has two more,
because Apple's x86-64 target assumes SSE4.1 where the other two assume
only SSE2: `safe_arch` `sse4_1.rs:72` (`blend_varying_m128d`, the SSE4.1
select that `wide` uses in place of an and/or sequence) and `wide`
`simd.rs:393` (`splat`). Which kernels run is decided at run time as on
Linux: the AVX2 ones on a CPU with AVX2 and FMA, the baseline ones
otherwise. GitHub's x86-64 runners have AVX2, so there, as on the
development machine, `bignum` runs the AVX2 kernels and the baseline
kernels are read, not run.

**arm64.** `malachite-nz` compiles its AVX2 kernels only for x86
(`build.rs` sets `fft_avx2` for `x86` and `x86_64` alone), so on arm64
there is one set of kernels, the baseline ones, with no run-time choice,
and `malachite-nz` has no `unsafe` line in the binary. `bytemuck` is used
by the AVX2 kernels only and drops out with them. `safe_arch` is an x86
crate; `wide` depends on it for x86 targets only, so it is not compiled.
What is left is `wide`, which on arm64 calls the NEON intrinsics itself:
its vector of four doubles is two NEON vectors of two. So on arm64 the
baseline kernels are the ones that run, and `bignum` runs them on all
three arm64 platforms.

| Where (`wide` 1.7.1) | What it does | Why it is sound |
| --- | --- | --- |
| `f64x2_.rs:110`, `:146`, `:164`, `:182`, `:1007` | Negate, add, subtract, multiply and fused multiply-add of two doubles: `vnegq_f64`, `vaddq_f64`, `vsubq_f64`, `vmulq_f64`, `vfmaq_f64` | Each is one NEON intrinsic on values, with no pointer. An intrinsic is `unsafe` to call only because it needs the CPU feature; these lines are compiled under `cfg(all(target_feature = "neon", target_arch = "aarch64"))`, and NEON is part of every arm64 CPU and of the baseline of all three targets, so there is nothing to check at run time. |
| `f64x2_.rs:316`, `:336` | Compare less-than and greater-than: `vcltq_f64`, `vcgtq_f64`, the mask reinterpreted as doubles | As above; the reinterpretation is between two 128-bit vector types, every bit pattern valid in both. |
| `f64x2_.rs:433` | Select by mask: `vbslq_f64` | As above. |
| `simd.rs:386`, and `:393` on macOS | `new` and `splat`: transmute from `[f64; N]` to the vector | Same size, every bit pattern valid; `transmute` refuses to compile otherwise. The same code as on x86-64. |
| `simd.rs:101` (no code), `:110` | `From<&[f64]>`: a zeroed vector, then `copy_nonoverlapping` of the slice into it | As on x86-64: `assert!(value.len() <= N)` at `simd.rs:91` comes first. |

As on x86-64, none of it computes an index or a length from the input: the
kernels reach their buffers through bounds-checked slices, and what could
go wrong is a wrong product.

**The standard library when linked statically.** On Linux the release
binaries are linked with `-C target-feature=+crt-static`, as Ethos's are
with `-static`. The linker then warns that `getpwuid_r` and `getaddrinfo`,
which the standard library refers to (the home directory, host names),
need the shared C library at run time. pathos calls neither.

## Decision

**Option 0: keep `malachite` as it is**, with its default features, and pin
it. `crates/pathos-term/Cargo.toml` requires exactly `=0.14.0` of
`malachite-base`, `malachite-nz` and `malachite-q`, and `Cargo.lock` fixes
the nine indirect crates at the versions in the table above. Every build
that counts passes `--locked` (CI's clippy and test steps,
`scripts/difftest`, `scripts/full-check`, `scripts/unsafe-reach`), so a
build fails instead of quietly taking another version, and `cargo update`
cannot move the three `malachite` crates at all.

### Why the reachable `unsafe` code is sound

Every `unsafe` item that pathos can reach, in the order a multiplication
meets them. "Line with code" means `scripts/unsafe-reach` finds
instructions for it in the binaries.

| Where | What it does | Why it is sound |
| --- | --- | --- |
| `malachite-nz` `fft/mod.rs:2036` (line with code) and `:2064` (inlined into its caller; no line of its own) | The two calls into the AVX2 kernels, which are compiled with `#[target_feature(enable = "avx2,fma")]` | Calling such a function is sound exactly when the CPU has the features. Both calls are inside `if avx2::is_supported()`, which is `is_x86_feature_detected!("avx2") && is_x86_feature_detected!("fma")` (`avx2.rs:35-37`), the standard library's run-time check. Otherwise the baseline kernels run. |
| `malachite-nz` `fft/avx2.rs:182`, `:192`, `:202` (lines with code), `:213` | `Add`, `Sub`, `Mul` and `Neg` for the kernels' vector of four doubles: one AVX intrinsic each | A trait method cannot carry `#[target_feature]`, hence the `unsafe` block. A value of the type can only be made by constructors that do carry it (`avx2.rs:53-80`), so one exists only in code already running behind the check above. The intrinsics take and return values, not pointers. |
| `malachite-nz` `fft/avx2.rs:48`, `:49` (no code) | `unsafe impl Zeroable` and `Pod` for that vector type, which let `bytemuck` cast it | The type is `#[repr(transparent)]` over `__m256d`: 32 bytes of four `f64`, no padding, every bit pattern valid. That is what the two traits promise. |
| `bytemuck` `lib.rs:378` (line with code) | `cast`: `[f64; 4]` to the vector and back, by value | `cast` compares the two sizes (`internal.rs:196`) and panics if they differ; here both are 32 bytes of plain data, for which every bit pattern is valid. |
| `bytemuck` `lib.rs:343`, `internal.rs:112`, `:123` (lines with code) | `pod_read_unaligned`: reads a vector from a slice of 4 doubles | It compares the slice's length in bytes with the size of the vector before it reads (`internal.rs:109`) and panics on a mismatch; the read is unaligned, so alignment does not matter. The slice comes from ordinary bounds-checked indexing (`&xs[i..i + 4]`). |
| `wide` `simd.rs:386`, `:402` (lines with code) | `new` and `to_array`: transmute between `[f64; N]` and the vector | Same size, every bit pattern valid; `transmute` refuses to compile otherwise. |
| `wide` `simd.rs:101` (no code), `:110` (line with code) | `From<&[f64]>`: a zeroed vector, then `copy_nonoverlapping` of the slice into it | `assert!(value.len() <= N)` at `simd.rs:91` comes first, so the copy fits; source and destination are a shared and a fresh local value, so they do not overlap; all zeros is a valid vector. |
| `safe_arch` `sse2.rs:77`, `:584`, `:703`, `:1825`, `:2808`, `:3048` (lines with code) | Add, compare (two), multiply, subtract and xor of two doubles: one SSE2 intrinsic each | SSE2 is part of every x86-64 CPU, and the crate compiles these wrappers only for targets that have it. Values in, values out. |
| `safe_arch` `sse4_1.rs:72` (line with code on macOS only) | Select by mask: `_mm_blendv_pd` | The wrapper exists only when the target has SSE4.1, which Apple's x86-64 target does: every Intel Mac has it. Values in, values out. |
| `wide` `simd.rs:393` (line with code on macOS only) | `splat`: transmute from `[f64; N]` to the vector | As `new`. |

This table is for x86-64. The `unsafe` lines of `wide` that are in the
arm64 binaries, where it uses NEON, are in the table under
"[On the other platforms](#on-the-other-platforms)".

None of this code computes an index or a length from the input and uses it
unchecked: the kernels reach their buffers through ordinary slices, which
Rust bounds-checks. So the failure that remains possible here is an
arithmetic one (a wrong product, if the FFT had a bug), not memory
corruption. The check for that is the large-number cases: `eo::add`,
`eo::mul`, `eo::pow`, division, conversions and the bit-vector operations
on operands from 64 bits to a million bits, far past the FFT threshold,
compared with Ethos (which uses GMP) and with values computed
independently. They are the `bignum` row of the gate table in
[evidence.md](evidence.md).

On a CPU with AVX2 and FMA the items of `malachite-nz` and `bytemuck` run
and those of `wide` and `safe_arch` do not; on a CPU without, the reverse.
The development machine and CI have AVX2, so the baseline kernels have been
read but not run here.

### Changing the pin

Any change to the version of one of the twelve crates, to the features
pathos enables, or to the build settings that select the kernels
(`target-feature`, `target-cpu`, a non-x86 target) is a change to this
file:

1. Rerun `scripts/unsafe-reach` and compare its output with the list under
   [Method](#method). Read every `unsafe` line that is new.
2. Update the tables above: versions, counts, what is reached, and the
   soundness argument for each reachable item.
3. Rerun the large-number cases and `scripts/full-check`.
4. Get Daniel's sign-off on the changed file before the change is merged.

A build with `--locked` fails until `Cargo.lock` is updated on purpose, so
none of this can happen by accident.

## Options considered

None of the options other than 0 has been applied.

No feature or setting takes `wide`, `safe_arch` and `bytemuck` out of the
build: `malachite-nz` depends on them unconditionally, and its FFT
threshold is a constant. What can be chosen is which kernels are compiled.

| | Option | `unsafe` lines with code in the binary | Cost |
| --- | --- | --- | --- |
| 0 | **As now** (chosen): `malachite` with its default `std` feature | `malachite-nz` 4, `bytemuck` 4, `wide` 3, `safe_arch` 6 (SSE2) | none |
| 1 | **`default-features = false`** on the three `malachite` crates. Without `std`, `malachite-nz` cannot ask the CPU for its features and leaves the AVX2 kernels out. | `malachite-nz` **0**, `bytemuck` **0**, `wide` 3, `safe_arch` 6 (SSE2). `libm` then has code in the binary (its portable `fma` and rounding, 111 lines, none `unsafe`), because without `std` the baseline kernels take those from `libm`. | Gates: none measurable (below). Large multiplications: **45 times slower** (0.37 s to 16.9 s on the input below), since every fused multiply-add becomes a library call. |
| 2 | **Compile for AVX2**: `-C target-feature=+avx2,+fma`. `malachite-nz`'s build script then leaves out the separate AVX2 kernels, because the baseline kernels are already compiled with those features. | `malachite-nz` **0**, `bytemuck` **0**, `wide` 3, `safe_arch` 6 (AVX and FMA intrinsics instead of SSE2) | Gates: **32% slower** (below). Large multiplications: the same speed. The binary dies with an illegal instruction on a CPU without AVX2, and the `safe_arch` wrappers are sound only on a CPU that has it, with no check left. |
| 3 | **Replace `malachite`** with a big-number crate that has fewer dependencies. `num.rs` is the only code that names `malachite`, so the swap is local. | depends on the crate | No candidate has been evaluated. `num-bigint` has no FFT and no SIMD; its speed on the large proofs is unknown. |

With options 1 and 2 nine `unsafe` lines stay reachable (`wide`'s three
and six of `safe_arch`), still only behind the FFT. No option removes those
short of replacing `malachite`.

How the numbers were measured, on 2026-11-14: `scripts/unsafe-reach` on a
scratch copy of the workspace with the one change, for the lines. For the
gates, the cases of the `perf` gate (regressions, proofs and large proofs,
673 cases, one job at a time: `scripts/difftest all --jobs 1`) on such a
copy and on an unchanged copy, one after the other, all agreeing with Ethos
in each run. A fuzzing campaign was running at low priority on the same
machine, so the times are comparable with each other, not with other days.

| Build | pathos's time over the 629 accepted cases | Large proofs (41) | Proofs (400) |
| --- | --- | --- | --- |
| Option 0, first run | 528.3 s | 508.8 s | 19.1 s |
| Option 1 | 522.7 s | 503.3 s | 19.0 s |
| Option 2 | 697.7 s | 676.6 s | 20.6 s |
| Option 0, second run | 526.0 s | 506.4 s | 19.1 s |

For large multiplications: `(eo::pow 3 6000000)`, `(eo::pow 7 3000000)`,
their product, its square and a division of the square, three runs each:
0.37 s with options 0 and 2, 16.9 s with option 1; Ethos takes 0.55 s.

Why option 0: option 1 would remove 8 of the 17 lines at no cost on the
gates, but it makes arithmetic on large numbers 45 times slower, where
Ethos with GMP is fast, and that is behaviour a user of `eo::pow` would
see. Option 2 ties the binary to newer CPUs, removes the run-time check,
and is slower on the proofs. The code kept by option 0 is small, guarded
by a check that is easy to read, and cannot corrupt memory by its
construction.
