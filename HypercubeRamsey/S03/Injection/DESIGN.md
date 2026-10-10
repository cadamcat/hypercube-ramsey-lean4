# Lemma 3.9 decomposition

The price-witness theorem is plausible as stated: it is Step 4 of the paper,
using Steps 1–3. No counterexample to `price_directed_label_sampler` was found.
This redesign is a collection of proof obligations, not a completed proof.
The export `near_product_injection` and the price-witness type are unchanged.

## Why the former split failed

The raw baseline is commit `25c5764`, `Injection/Nodes.lean:50–219`.
The paper source is
`sections/03-general-conventions-and-probabilistic-tools.tex`.

| Old node | Old assertion | Paper assertion / replacement |
|---|---|---|
| L3.9a, `balanced_completion_good_order` | Real atoms ≤ d^(-.95), but every completed atom ≤ 10/d; d ≥ 100 | TeX 627–647: only dummy atoms are O(1/d). New eventual statement accepts real atoms ≤ 2d^(-.95), gives the exact dummy formula, a row order and `OrderedInput`. |
| L3.9b, `tracking_label_sampler` | Some injection law has additive singleton error ≤ d^(-.1), with t ≤ d | TeX 649–693: the specific sequential process tracks used mass, with overwhelming probability. New statement is `Pr(G) ≥ 1-exp(-d^.1)` for `sequentialLaw`, with t ≤ 3d/4. |
| L3.9c, `price_directed_label_sampler` | Some injection law has final near-product bounds and price ≥ target | TeX 695–734 contains only the forcing comparison; price perturbation is TeX 736–758. Same final type, now assembled from completion, conditioned comparison, restriction, perturbation, gain and bound transfer. |
| L3.9d / L3.9e | Compact-convex calibration and side-data lifting | TeX 760–768 / 618–625. Existing proofs and statements are retained. |

The old completion is false. Take one row, d=11^20, q(0)=11/d,
and q(y)=(1-11/d)/(d-1) otherwise. Its atoms are at most d^(-.95)=11/d,
its column loads are at most 1/2, and its row mass is one. Preservation of
q(0) contradicts 10/d. The new completion incorporates the dummy-only fix
from lane fix-inj-a and also permits the atom inflation needed by prices.
Its signature supersedes that lane's narrower correction.

The old tracking estimate does not control joint probabilities of its witness. For uniform
rows, uniform cyclic shifts have exact marginals 1/d, but two consecutive
prescribed labels occur with probability 1/d, not about 1/d². Choose
d=2^40 so that two queried rows satisfy the query-size bound. The shift law
violates the final bound because exp(2d^(-.04)) < d. For a zero target atom,
an additive error still permits positive output mass; relative error does not.
The old L3.9c never invoked the completion or tracking nodes.

## Concrete process and proof order

`Sampler.lean` defines option-valued paths and the product of explicit
triangular kernels. At a stop or zero allowed mass, the next output is
`none`; all later kernels then emit `none`. The kernel depends only on
previous coordinates, including its stop decision. `trackingError` is the
finite maximum of the errors for all rows and times up to b, with zero
inserted for an empty row set. `Good` checks valid injection paths, the
constant stop threshold and d^(-.1) tracking through time t.

`forcingStepWeight` forces queried steps and reserves all strictly pending
target labels at ordinary steps. Its drift is computed under that kernel.
The singleton forcing martingale event has half the ordinary tolerance,
leaving room for the O(d^(-.95)) cumulative drift change. No lower-bound
claim for multiple targets is needed.

| Stage | Nodes | TeX lines |
|---|---|---|
| Finite laws | `sequential_weights_probability`, `forcing_weights_probability` | 650, 657, 697–699 |
| Free mass and drift | `free_mass_before_stop`, `sequential_drift_increment` | 662–668 |
| Stopped fluctuations | `sequential_martingale_concentration` | 668–671 |
| Two summations by parts | `drift_denominator_replacement`, `drift_column_replacement` | 673–685 |
| Recursion, iteration, stop exclusion | `tracking_drift_recurrence`, `discrete_tracking_gronwall`, `tracking_bootstrap`, `tracking_probability_transfer` | 687–693 |
| Atom-extracted identity | `forcing_likelihood_identity` | 699–705 |
| Log comparison | `prefix_log_comparison`, `linear_likelihood_cancellation`, `quadratic_likelihood_remainder`, `likelihood_log_transfer` | 707–720 |
| Single-target stability | `singleton_forcing_drift_stability`, `forced_martingale_concentration`, `singleton_forcing_tracking_transfer` | 725–734 |
| Conditional integration | `conditioned_comparison_transfer` | 722–734 |
| Price construction | `price_perturbation_estimates`, `price_gain_dominates_relative_error`, `perturbed_joint_bound_transfer` | 739–758 |
| Real rows | `restrict_ordered_sampler` | 627–636, 737–758 |

The assembled theorems are `tracking_label_sampler`,
`ordered_conditioned_sampler_estimates` and `price_directed_label_sampler`.
The main export still calls the last one, then the existing calibration and
side-data proofs. Helpers for the two summations, scalar Gronwall and prefix
log comparison are available for the corresponding node proofs; those
proofs have intentionally not been written.

About 800 lines per old node was not a credible allocation: L3.9b omitted
its process and event, while L3.9c contained both samplers and price
perturbation. The new nodes isolate a formula or estimate apiece; most are
plausibly below that budget, but proof lengths have not been measured.
The concentration and stopping proofs remain the main uncertainty.
The repository's finite `xAzuma` is itself unfinished at
`Tools/Concentration.lean:291–306`; Mathlib has scalar discrete Gronwall in
`Mathlib/Analysis/ODE/DiscreteGronwall.lean`. There is no missing import in
this redesign. Proving concentrations still requires a kernel-prefix
centering argument and a verified concentration tool.

## One degenerate attack per new theorem statement

These are mathematical boundary inspections, not Lean proofs or exhaustive
counterexample searches. Every theorem below still needs its full proof,
except the three assemblies. The explicit definitions were also inspected
at zero horizon, failed prefixes, empty reservations and zero atom values.

| Statement | Attack and result |
|---|---|
| `balanced_completion_good_order` | No real rows: t dummy laws are uniform and the formula is 1/d. At column load 1/2 the dummy numerator stays positive. The 11/d real atom is now permitted. Small d is excluded by eventuality. |
| `sequential_weights_probability` | t=0, including d=0: unique empty path, product 1. At zero free mass the failure atom has mass 1. |
| `forcing_weights_probability` | Empty query: identical kernels to sequential sampling. Repeated forced labels cause absorbing failure, not loss of normalization. |
| `free_mass_before_stop` | j=0 gives D=0 and free mass 1. At horizon 3d/4 and stop error 1/20 the lower bound is 1/5; permitting t=d would destroy it. |
| `sequential_drift_increment` | A zero q_a(y) contributes zero. Valid-prefix and error hypotheses exclude failed paths from the drift formula. |
| `sequential_martingale_concentration` | No rows: event is vacuous and has probability 1. Stopped paths have zero subsequent centered increments under their actual kernels. |
| `drift_denominator_replacement` | b=0: both drift sums vanish. First bad index is allowed, since only previous times must be below the stop threshold. |
| `drift_column_replacement` | Uniform q: the column replacement is exact on an injective prefix. b=0 again gives zero sums. |
| `tracking_drift_recurrence` | b=0: maximum is 0. Terminal b=t is present; no claim is made beyond t. |
| `discrete_tracking_gronwall` | n=0 or B=0 gives e≤A. A=0 and nonnegative e force e=0 by induction. |
| `tracking_bootstrap` | A path that first becomes none cannot satisfy positive weight and the martingale bound at a large d before the constant-error stop. t=0 gives Good automatically. |
| `tracking_probability_transfer` | Null paths can be invalid: implication is required only on nonzero weights. |
| `tracking_label_sampler` | Empty horizon gives probability 1; uses the concrete event rather than any output marginal. |
| `forcing_likelihood_identity` | Empty query gives factor 1 and identical laws. An ordinary zero-atom choice gives zero on both sides. Repeated/zero target atoms are excluded only from this identity's logarithmic domain. |
| `prefix_log_comparison` | First row: empty sum and log(1)=0. Last row has 1-s≥1/4. |
| `linear_likelihood_cancellation` | Empty query: both sums are zero. Queried-step omission is paid for by the l² atom term, including consecutive queried rows. |
| `quadratic_likelihood_remainder` | Empty query: all excluded fractions and remainders are zero. Eventuality ensures fractions ≤1/2 for maximal allowed l. |
| `likelihood_log_transfer` | Empty query gives likelihood factor 1 and log 0. Positivity comes from the denominator bounds and fractions ≤1/2. |
| `singleton_forcing_drift_stability` | First target has no earlier reservation; only its forced step contributes. A target already used on an arbitrary valid prefix makes the forced step fail and still costs at most one tracked atom. |
| `forced_martingale_concentration` | Forced draws have zero centered increment. Tiny positive target mass never enters a denominator or the tail exponent. |
| `singleton_forcing_tracking_transfer` | Last-row target reserves its label longest; the completed column prefix bound still bounds its cumulative cost. Half-tolerance leaves room for that cost. |
| `conditioned_comparison_transfer` | Empty query has probability and product 1 and must be treated directly when conditioning. Zero atoms force zero event mass; repeated labels have zero probability by injective support. No tiny atom divides an absolute exception probability. |
| `ordered_conditioned_sampler_estimates` | Zero atoms get zero marginal; empty horizon gets the unique empty assignment. |
| `restrict_ordered_sampler` | Empty real row set maps every assignment to the unique empty function. A non-surjective embedding merely discards dummies; query cardinality is preserved. |
| `price_perturbation_estimates` | Constant prices give sign 0, unchanged q and zero gain. Zero atoms remain zero. Eventual delta<1 prevents a zero normalizer. |
| `price_gain_dominates_relative_error` | Arbitrary negative constant prices have zero centered loss; row probability sums cancel their baselines exactly. Empty rows give price 0. |
| `perturbed_joint_bound_transfer` | Empty query gives bound 1. If an original atom is zero, pointwise nonnegative domination forces the perturbed atom zero. |
| `price_directed_label_sampler` | Empty rows give the unique empty law and equal zero prices. All-constant row prices cause zero centered gain without a strict-price requirement. |

## Freeze and verification

`FREEZE.txt` lists all new declarations and changed existing declarations by
module and fully qualified name. It distinguishes statement changes from
body-only changes; no named declaration was deleted. The obsolete cyclic
shift proof body was removed. The main export's complete source file remains
identical to baseline. All analytic nodes contain intentional `sorry`
placeholders under this lane's instruction to write no node proofs.
