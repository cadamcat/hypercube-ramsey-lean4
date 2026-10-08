import HypercubeRamsey.S06.OddLoads_sol_s06_loadB
import HypercubeRamsey.S06.OddLoads_opus_hjoint_sol_s06_hjoint
import HypercubeRamsey.S06.OddLoads_opus_hjoint_tuples_sol_s06_hjoint
import HypercubeRamsey.S06.OddLoads_opus_hjoint_hid_sol_s06_hjoint

/-!
# The target-only route for the odd hidden joint step (lane opus-diag-hjoint)

TeX 06:684–688: for separated signs, remove the hidden-stage constraints touching each target scalar; with the
other keys fixed, integrate the distinct targets under their original independent priors; the proxy calculation
bounds each mean by `2Nπ_{ℓ(b)}(y)`, and no other retained function reads that target.  The last clause is the
proxy locality of 06:641–643: the proxy computation consults hidden keys at signs within `O(√m)` of the role's
sign, because eligibility is determined by incident stars and the short tube contains only that many sign
changes.  The sign count of the short tube uses the one-hot fine count fields of the code (06:231–235), recorded
as `StateCode6.sign_dist`.

The generic part (resampling a block of coordinates of a product law, the conditional avoidance comparison with
a fiber bound, and the fiber product over distinct targets) is proved here.  The proxy locality
`proxyMean_signScope_local` is assembled from two lemmas, `proxyRow_congr_hid` and
`proxyRow_dependsOn_tuples`, both proved.
-/

namespace HypercubeRamsey.S06.Lane_opus_hjoint

open OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section

/-! ### Resampling a block of coordinates under a product law -/

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)]

/-- Replace the coordinates of `ω` in `B` by those of `ω'`. -/
def merge (B : Finset V) (ω' ω : ∀ v, α v) : ∀ v, α v := fun v => if v ∈ B then ω' v else ω v

theorem merge_swap_fst (B : Finset V) (ω ω' : ∀ v, α v) :
    merge B (merge B ω ω') (merge B ω' ω) = ω := by
  funext v
  by_cases h : v ∈ B <;> simp [merge, h]

theorem merge_swap_snd (B : Finset V) (ω ω' : ∀ v, α v) :
    merge B (merge B ω' ω) (merge B ω ω') = ω' := by
  funext v
  by_cases h : v ∈ B <;> simp [merge, h]

/-- Exchanging the `B`-coordinates of two samples. -/
def swapEquiv (B : Finset V) : ((∀ v, α v) × (∀ v, α v)) ≃ ((∀ v, α v) × (∀ v, α v)) where
  toFun p := (merge B p.2 p.1, merge B p.1 p.2)
  invFun p := (merge B p.2 p.1, merge B p.1 p.2)
  left_inv p := Prod.ext (merge_swap_fst B p.1 p.2) (merge_swap_snd B p.1 p.2)
  right_inv p := Prod.ext (merge_swap_fst B p.1 p.2) (merge_swap_snd B p.1 p.2)

theorem prod_weight_swap (q : ∀ v, α v → ℝ) (B : Finset V) (ω ω' : ∀ v, α v) :
    (∏ v, q v (merge B ω' ω v)) * (∏ v, q v (merge B ω ω' v)) =
      (∏ v, q v (ω v)) * ∏ v, q v (ω' v) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  by_cases h : v ∈ B
  · simp only [merge, h, if_true]
    ring
  · simp only [merge, h, if_false]

/-- Resampling the `B`-coordinates from an independent copy does not change a product-law expectation. -/
theorem sum_resample (q : ∀ v, α v → ℝ) (hq1 : ∀ v, ∑ a, q v a = 1) (B : Finset V)
    (F : (∀ v, α v) → ℝ) :
    (∑ ω, ∑ ω', ((∏ v, q v (ω v)) * ∏ v, q v (ω' v)) * F (merge B ω' ω)) =
      ∑ ω, (∏ v, q v (ω v)) * F ω := by
  classical
  let w : (∀ v, α v) → ℝ := fun ω => ∏ v, q v (ω v)
  have hw1 : ∑ ω, w ω = 1 := by
    simp only [w]
    rw [← Fintype.prod_sum]
    simp [hq1]
  calc
    (∑ ω, ∑ ω', (w ω * w ω') * F (merge B ω' ω)) =
        ∑ p : (∀ v, α v) × (∀ v, α v), (w p.1 * w p.2) * F (merge B p.2 p.1) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ p : (∀ v, α v) × (∀ v, α v),
          (w (swapEquiv B p).1 * w (swapEquiv B p).2) * F (swapEquiv B p).1 := by
          apply Fintype.sum_congr
          intro p
          have hsw : w (swapEquiv B p).1 * w (swapEquiv B p).2 = w p.1 * w p.2 :=
            prod_weight_swap q B p.1 p.2
          rw [hsw]
          rfl
    _ = ∑ p : (∀ v, α v) × (∀ v, α v), (w p.1 * w p.2) * F p.1 :=
          Equiv.sum_comp (swapEquiv B) (fun p => (w p.1 * w p.2) * F p.1)
    _ = ∑ ω, w ω * F ω := by
          rw [Fintype.sum_prod_type]
          apply Fintype.sum_congr
          intro ω
          have h : ∑ ω', (w ω * w ω') * F ω = (w ω * F ω) * ∑ ω', w ω' := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω' _
            ring
          rw [h, hw1, mul_one]

/-- Avoidance of events that do not read the block `B`, with a uniform bound on the `B`-fibers. -/
theorem avoid_sum_le_of_resample {I : Type*} [Fintype I] [DecidableEq I]
    (q : ∀ v, α v → ℝ) (hq0 : ∀ v a, 0 ≤ q v a) (hq1 : ∀ v, ∑ a, q v a = 1)
    (E : I → Finset (∀ v, α v)) (scope : I → Finset V)
    (hscope : ∀ i (ω ω' : ∀ v, α v), (∀ v ∈ scope i, ω v = ω' v) → (ω ∈ E i ↔ ω' ∈ E i))
    (B : Finset V) (S : Finset I) (hS : ∀ i ∈ S, Disjoint B (scope i))
    (W : (∀ v, α v) → ℝ) (C : ℝ)
    (hfib : ∀ ω, ∑ ω', (∏ v, q v (ω' v)) * W (merge B ω' ω) ≤ C) :
    (∑ ω ∈ LocalLemma.avoid E S, (∏ v, q v (ω v)) * W ω) ≤
      C * LocalLemma.mass (fun ω => ∏ v, q v (ω v)) (LocalLemma.avoid E S) := by
  classical
  let w : (∀ v, α v) → ℝ := fun ω => ∏ v, q v (ω v)
  let P : (∀ v, α v) → Prop := fun ω => ∀ j ∈ S, ω ∉ E j
  have hw0 : ∀ ω, 0 ≤ w ω := fun ω => Finset.prod_nonneg fun v _ => hq0 v (ω v)
  have hP : ∀ ω ω', P (merge B ω' ω) ↔ P ω := by
    intro ω ω'
    apply forall₂_congr
    intro i hi
    rw [hscope i (merge B ω' ω) ω ?_]
    intro v hv
    have hvB : v ∉ B := fun hvB => Finset.disjoint_left.mp (hS i hi) hvB hv
    simp [merge, hvB]
  let F : (∀ v, α v) → ℝ := fun ω => if P ω then W ω else 0
  have hlhs : (∑ ω ∈ LocalLemma.avoid E S, w ω * W ω) = ∑ ω, w ω * F ω := by
    rw [show LocalLemma.avoid E S = Finset.univ.filter P from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : P ω
    · have hF : F ω = W ω := if_pos h
      rw [if_pos h, hF]
    · have hF : F ω = 0 := if_neg h
      rw [if_neg h, hF, mul_zero]
  have hmass : LocalLemma.mass w (LocalLemma.avoid E S) = ∑ ω, if P ω then w ω else 0 := by
    rw [LocalLemma.mass, show LocalLemma.avoid E S = Finset.univ.filter P from rfl, Finset.sum_filter]
  change (∑ ω ∈ LocalLemma.avoid E S, w ω * W ω) ≤ C * LocalLemma.mass w (LocalLemma.avoid E S)
  rw [hlhs, hmass, ← sum_resample q hq1 B F, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : P ω
  · have hF : ∀ ω', F (merge B ω' ω) = W (merge B ω' ω) := by
      intro ω'
      simp [F, (hP ω ω').mpr h]
    simp only [hF, h, if_true]
    calc
      (∑ ω', (w ω * w ω') * W (merge B ω' ω)) = w ω * ∑ ω', w ω' * W (merge B ω' ω) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω' _
          ring
      _ ≤ w ω * C := mul_le_mul_of_nonneg_left (hfib ω) (hw0 ω)
      _ = C * w ω := mul_comm _ _
  · have hF : ∀ ω', F (merge B ω' ω) = 0 := by
      intro ω'
      have hn : ¬ P (merge B ω' ω) := fun h' => h ((hP ω ω').mp h')
      simp [F, hn]
    simp [hF, h]

/-- A function of one coordinate has its marginal expectation under a product law. -/
theorem pi_expect_coord {A : Type*} [Fintype A] (q : V → FinProb A) (i : V) (F : A → ℝ) :
    (FinProb.pi q).expect (fun Z => F (Z i)) = (q i).expect F := by
  classical
  unfold FinProb.expect FinProb.pi
  simp only []
  have h : ∀ Z : V → A, (∏ v, (q v).w (Z v)) * F (Z i) =
      ∏ v, ((q v).w (Z v) * (if v = i then F (Z v) else 1)) := by
    intro Z
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  simp_rw [h]
  rw [← Fintype.prod_sum (fun v (a : A) => (q v).w a * (if v = i then F a else 1))]
  rw [Fintype.prod_eq_single i]
  · simp
  · intro v hv
    simp [hv, (q v).sum_eq_one]

/-- The fiber product over distinct targets: with the other coordinates fixed, a product of functions each reading
only its own target among the targets integrates to the product of the one-target integrals (06:686–688). -/
theorem resample_prod_le {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]
    (q : V → FinProb A) (U : Finset ι) (t : ι → V)
    (ht : ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' → t u ≠ t u')
    (f : ι → (V → A) → ℝ) (hf0 : ∀ u Z, 0 ≤ f u Z)
    (hloc : ∀ u ∈ U, ∀ Z Z' : V → A,
      (∀ v, (∀ u' ∈ U, u' ≠ u → v ≠ t u') → Z v = Z' v) → f u Z = f u Z')
    (c : ι → ℝ)
    (hc : ∀ u ∈ U, ∀ Z : V → A, ∑ ξ, (q (t u)).w ξ * f u (Function.update Z (t u) ξ) ≤ c u)
    (Z : V → A) :
    ∑ Z' : V → A, (∏ v, (q v).w (Z' v)) * (∏ u ∈ U, f u (merge (U.image t) Z' Z)) ≤
      ∏ u ∈ U, c u := by
  classical
  let g : ι → (V → A) → ℝ := fun u Z' => f u (Function.update Z (t u) (Z' (t u)))
  have hmerge : ∀ u ∈ U, ∀ Z' : V → A, f u (merge (U.image t) Z' Z) = g u Z' := by
    intro u hu Z'
    apply hloc u hu
    intro v hv
    by_cases hvt : v = t u
    · subst hvt
      simp [merge, Finset.mem_image_of_mem t hu]
    · by_cases hvB : v ∈ U.image t
      · obtain ⟨u', hu', hvu'⟩ := Finset.mem_image.mp hvB
        have hne : u' ≠ u := by
          intro h
          apply hvt
          rw [← hvu', h]
        exact absurd hvu'.symm (hv u' hu' hne)
      · simp [merge, hvB, Function.update_of_ne hvt]
  have hLHS : (∑ Z' : V → A, (∏ v, (q v).w (Z' v)) * (∏ u ∈ U, f u (merge (U.image t) Z' Z))) =
      (FinProb.pi q).expect (fun Z' => ∏ u ∈ U, g u Z') := by
    unfold FinProb.expect FinProb.pi
    apply Fintype.sum_congr
    intro Z'
    simp only []
    rw [Finset.prod_congr rfl (fun u hu => hmerge u hu Z')]
  rw [hLHS]
  have hdep : ∀ u, FinProb.DependsOn (g u) ({t u} : Finset V) := by
    intro u Z₁ Z₂ h
    simp only [g, h (t u) (Finset.mem_singleton_self _)]
  have hdis : ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' → Disjoint ({t u} : Finset V) {t u'} := by
    intro u hu u' hu' hne
    exact Finset.disjoint_singleton.mpr (ht u hu u' hu' hne)
  rw [_root_.Lane_q_s06_loads.pi_expect_prod_pairwise_disjoint (Ω := fun _ => A) q U
    (fun u => ({t u} : Finset V)) g hdep hdis]
  apply Finset.prod_le_prod₀
  · intro u _
    unfold FinProb.expect
    exact Finset.sum_nonneg fun Z' _ => mul_nonneg ((FinProb.pi q).nonneg Z') (hf0 _ _)
  · intro u hu
    have hcoord := pi_expect_coord q (t u) (fun ξ => f u (Function.update Z (t u) ξ))
    have hg : g u = fun Z' => (fun ξ => f u (Function.update Z (t u) ξ)) (Z' (t u)) := rfl
    rw [hg, hcoord]
    unfold FinProb.expect
    exact hc u hu Z

end Generic

/-! ### The stage 3 comparison with the targets only -/

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}

/-- Remove the stage 3 constraints in `T` (those touching the block `B`) and bound the rest by a uniform
`B`-fiber bound (06:684–688). -/
theorem stage3_compare_targets (X : Ctx6 γ p₀ K n N E G M) (b : X.Base)
    (xmax : ℝ) (cert : AvoidCert6 (X.hidLaw b).w (X.bad3Set b) xmax)
    (hx : xmax < 1) (B : Finset X.HKey) (W : X.Hid → ℝ) (hW0 : ∀ Z, 0 ≤ W Z) (Cb : ℝ)
    (hfib : ∀ Z : X.Hid, ∑ Z' : X.Hid, (∏ ℓ, (X.hidPost b ℓ.1).w (Z' ℓ)) * W (merge B Z' Z) ≤ Cb)
    (S T : Finset (X.Bin × CubeVertex X.m)) (hST : Disjoint S T)
    (hUnion : S ∪ T = Finset.univ)
    (hS : ∀ gr ∈ S, Disjoint B (Lane_q_s06_loads.bad3HidScope6 X gr)) :
    (X.stage3Law b).expect W ≤ (∏ gr ∈ T, (1 - cert.x gr)⁻¹) * Cb := by
  classical
  have hscope : ∀ gr (Z Z' : X.Hid),
      (∀ ℓ ∈ Lane_q_s06_loads.bad3HidScope6 X gr, Z ℓ = Z' ℓ) →
      (Z ∈ X.bad3Set b gr ↔ Z' ∈ X.bad3Set b gr) := by
    intro gr Z Z' heq
    simpa [Ctx6.bad3Set] using
      _root_.Lane_q_s06_loads.bad3_congr_hidScope X b gr Z Z' heq
  have hpos := Lane_q_s06_loads.S06.AvoidCert6.mass_avoid_pos cert
    (X.hidLaw b).nonneg (X.hidLaw b).sum_eq_one hx
  have hmass : LocalLemma.mass (X.hidLaw b).w
      (LocalLemma.avoid (X.bad3Set b) Finset.univ) =
      (X.hidLaw b).pr (fun Z => ∀ gr, ¬ X.Bad3 b gr Z) := by
    unfold LocalLemma.mass FinProb.pr
    rw [← Finset.sum_ite_mem_eq]
    apply Finset.sum_congr rfl
    intro Z _
    by_cases hg : ∀ gr, ¬ X.Bad3 b gr Z
    · simp [Lane_sol_s06_loadB.mem_avoid_bad3, hg]
    · simp [Lane_sol_s06_loadB.mem_avoid_bad3, hg]
  have hnum : (∑ Z ∈ LocalLemma.avoid (X.bad3Set b) Finset.univ,
        (X.hidLaw b).w Z * W Z) =
      ∑ Z, if (∀ gr, ¬ X.Bad3 b gr Z) then (X.hidLaw b).w Z * W Z else 0 := by
    rw [← Finset.sum_ite_mem_eq]
    apply Finset.sum_congr rfl
    intro Z _
    by_cases hg : ∀ gr, ¬ X.Bad3 b gr Z
    · simp [Lane_sol_s06_loadB.mem_avoid_bad3, hg]
    · simp [Lane_sol_s06_loadB.mem_avoid_bad3, hg]
  have hbound : (∑ Z ∈ LocalLemma.avoid (X.bad3Set b) S, (X.hidLaw b).w Z * W Z) ≤
      Cb * LocalLemma.mass (X.hidLaw b).w (LocalLemma.avoid (X.bad3Set b) S) :=
    avoid_sum_le_of_resample (fun ℓ : X.HKey => (X.hidPost b ℓ.1).w)
      (fun ℓ a => (X.hidPost b ℓ.1).nonneg a) (fun ℓ => (X.hidPost b ℓ.1).sum_eq_one)
      (X.bad3Set b) (Lane_q_s06_loads.bad3HidScope6 X) hscope B S hS W Cb hfib
  have hposS := _root_.Lane_q_s06_loads.avoid_mass_positive_subset cert
    (X.hidLaw b).nonneg (X.hidLaw b).sum_eq_one hx S
  have hratio : (∑ Z ∈ LocalLemma.avoid (X.bad3Set b) S, (X.hidLaw b).w Z * W Z) /
      LocalLemma.mass (X.hidLaw b).w (LocalLemma.avoid (X.bad3Set b) S) ≤ Cb := by
    rw [div_le_iff₀ hposS]
    exact hbound
  let p : (X.Bin × CubeVertex X.m) → ℝ := fun gr => cert.x gr *
    ∏ gr' ∈ Finset.univ.filter (cert.adj gr), (1 - cert.x gr')
  have havoid := LocalLemma.conditional_avoidance (X.hidLaw b).w
    (X.hidLaw b).nonneg (X.hidLaw b).sum_eq_one (X.bad3Set b) cert.adj
    cert.adj_symm cert.adj_irrefl p cert.x cert.local_bound cert.x_nonneg
    (fun gr => (cert.x_le gr).trans_lt hx) (fun _ => le_rfl)
  have hcompare := havoid.2.2.1 S T hST W hW0
  rw [hUnion, ← Finset.prod_inv_distrib] at hcompare
  have hT0 : 0 ≤ ∏ gr ∈ T, (1 - cert.x gr)⁻¹ :=
    Finset.prod_nonneg fun gr _ => inv_nonneg.mpr (by linarith [cert.x_le gr])
  rw [Lane_q_s06_loads.stage3Law_expect_formula X b (by rwa [← hmass]) W]
  rw [← hnum, ← hmass]
  exact hcompare.trans (mul_le_mul_of_nonneg_left hratio hT0)

/-! ### Proxy locality (06:641–643) -/

/-- Hidden keys at signs within `Rshort + 6` of the role's sign. -/
def proxySignScope (X : Ctx6 γ p₀ K n N E G M) (u : CubeVertex n) : Finset X.HKey :=
  Finset.univ.filter fun ℓ => _root_.hammingDist ℓ.2 (X.g.L.sign u) ≤ X.Rshort + 6

/-- Tuple coordinates whose types observe only keys in the proxy sign scope. -/
def proxyTupleScope (X : Ctx6 γ p₀ K n N E G M) (u : CubeVertex n) : Finset (X.Loc × X.Ty) :=
  Finset.univ.filter fun e => e.2.obs ⊆ proxySignScope X u

/-- At fixed history, positions, activations and ties, the short proxy row reads tuple data only at types whose
observation lists lie in the sign scope: the consulted tuples belong to descriptors of `b = q_st(u)` and of the odd
states marking sites within `Rshort` of its neighbours' sites (06:641–643, 06:560–566).  Uses `StateCode6.sign_dist`. -/
theorem proxyRow_dependsOn_tuples (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (P : X.Loc → Bool)
    (a : X.Loc → Bool) (τ : X.hp.Ties) (u : CubeVertex n) (hu : ¬ IsEvenRole u) (y : Fin N) :
    FinProb.DependsOn (fun d : X.Data X.Loc => X.proxyRow H (((P, d), a), τ) u y)
      (proxyTupleScope X u) := by
  intro d d' hdd
  apply Lane_sol_s06_hjoint.proxyRow_congr_data X H (((P, d), a), τ)
    (((P, d'), a), τ) u rfl rfl rfl ?_ y
  intro e he
  exact hdd e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)

/-- At fixed centre data, the short proxy row reads hidden keys only in the sign scope: marks through
`S3Fail_congr_hid`, validity and the Step 3 tests at `b`, and the adjustment table through `presProb` (whose tuple law
is handled by `dataLaw_expect_congr_hid` and `proxyRow_dependsOn_tuples`'s geometry).  Uses `StateCode6.sign_dist`. -/
theorem proxyRow_congr_hid (X : Ctx6 γ p₀ K n N E G M) (b₀ : X.Base) (C : X.Centre) (u : CubeVertex n)
    (hu : ¬ IsEvenRole u) (y : Fin N) (Z Z' : X.Hid) (hZ : ∀ ℓ ∈ proxySignScope X u, Z ℓ = Z' ℓ) :
    X.proxyRow (b₀, Z) C u y = X.proxyRow (b₀, Z') C u y := by
  exact Lane_sol_s06_hjoint.proxyRow_hid_local X b₀ C u y Z Z' hZ

/-- Proxy locality (06:641–643): the centre-averaged short proxy row of an odd role reads hidden keys only at signs
within `Rshort + 6` of its sign.  The short choice at a neighbour `a` of `b = q_st(u)` consults eligibility at sites
within `Rshort` of `site a` (`HDParams.Reach`); a mark at such a site `site a₂` reads the Step 3 failures of the odd
states `b₂` adjacent to `a₂`; `StateCode6.sign_dist` gives `d(sign a₂, sign a) ≤ Rshort`, and each of the steps
`u → a`, `a₂ → b₂ → a₃` and an observation list moves the sign by at most one.  Assembled from
`proxyRow_congr_hid` and `proxyRow_dependsOn_tuples` with `dataLaw_expect_congr_hid`. -/
theorem proxyMean_signScope_local (X : Ctx6 γ p₀ K n N E G M) (b₀ : X.Base) (u : CubeVertex n)
    (hu : ¬ IsEvenRole u) (y : Fin N) (Z Z' : X.Hid) (hZ : ∀ ℓ ∈ proxySignScope X u, Z ℓ = Z' ℓ) :
    (X.centreLaw (b₀, Z)).expect (fun C => (N : ℝ) * X.proxyRow (b₀, Z) C u y) =
      (X.centreLaw (b₀, Z')).expect (fun C => (N : ℝ) * X.proxyRow (b₀, Z') C u y) := by
  classical
  have hrow : ∀ C, X.proxyRow (b₀, Z) C u y = X.proxyRow (b₀, Z') C u y :=
    fun C => proxyRow_congr_hid X b₀ C u hu y Z Z' hZ
  simp_rw [hrow]
  unfold Ctx6.centreLaw
  simp only [_root_.Lane_q_s06_loads.finProb_prod_expect]
  apply congrArg (fun g : (X.Loc → Bool) → ℝ => X.hp.posLaw.expect g)
  funext P
  apply _root_.Lane_q_s06_loads.dataLaw_expect_congr_hid X b₀ Z Z' (proxyTupleScope X u)
  · intro d d' hdd
    have hpt : ∀ a τ, X.proxyRow (b₀, Z') (((P, d), a), τ) u y =
        X.proxyRow (b₀, Z') (((P, d'), a), τ) u y :=
      fun a τ => proxyRow_dependsOn_tuples X (b₀, Z') P a τ u hu y d d' hdd
    simp only [hpt]
  · intro e he ℓ hℓ
    exact hZ ℓ ((Finset.mem_filter.mp he).2 hℓ)

/-- The target of a sign-separated role is outside the proxy sign scope. -/
theorem signFar_target_not_mem (X : Ctx6 γ p₀ K n N E G M) (u u' : CubeVertex n)
    (hFar : 100 * (Nat.sqrt X.m + 1) < _root_.hammingDist (X.g.L.sign u) (X.g.L.sign u')) :
    X.tgt (X.g.L.stateOf u') ∉ proxySignScope X u := by
  intro hmem
  have hd := (Finset.mem_filter.mp hmem).2
  have hsign : (X.tgt (X.g.L.stateOf u')).2 = X.g.L.sign u' := by
    simp [Ctx6.tgt, ChunkLayout6.stTarget, X.facts.sign_eq]
  rw [hsign, hammingDist_comm] at hd
  have hR : X.Rshort = 10 * Nat.sqrt X.m := rfl
  rw [hR] at hd
  omega

end

end HypercubeRamsey.S06.Lane_opus_hjoint
