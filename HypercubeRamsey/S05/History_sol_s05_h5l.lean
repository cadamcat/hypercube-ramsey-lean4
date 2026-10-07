import HypercubeRamsey.S05.History_q_s05_h5l
import HypercubeRamsey.S05.History_sol_s05_h1
import HypercubeRamsey.S05.Bounds_sol_s05_h1

namespace HypercubeRamsey.Lane_sol_s05_h5l

open Classical Filter Real OAI.HypercubeRamsey
open scoped Topology

noncomputable section
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 800000

/-- Integrating a posterior based on any subset of independent observations recovers its prior. -/
theorem product_posterior_mean {A I O : Type*} [Fintype A] [DecidableEq A] [Fintype I]
    [DecidableEq I] [Fintype O] (P : FinProb A) (Q : A → I → FinProb O)
    (S : Finset I) (o₀ : O) (fallback y : A) :
    P.expect (fun a => (FinProb.pi (Q a)).expect (fun z =>
      (normalize5 (fun b => P.w b * ∏ i ∈ S, (Q b i).w (z i)) fallback).w y)) = P.w y := by
  let post : (I → O) → ℝ := fun z =>
    (normalize5 (fun b => P.w b * ∏ i ∈ S, (Q b i).w (z i)) fallback).w y
  have hdep : FinProb.DependsOn post S := by
    intro z z' h
    apply congrArg (fun f => (normalize5 f fallback).w y)
    funext b
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [h i hi]
  have hrestrict (a : A) :
      (FinProb.pi (Q a)).expect post =
        (FinProb.pi (fun i : S => Q a i.1)).expect (fun z =>
          (normalize5 (fun b => P.w b * ∏ i : S, (Q b i.1).w (z i)) fallback).w y) := by
    rw [FinProb.pi_expect_depends (Q a) S post (fun _ => o₀) hdep]
    congr 1
    funext z
    dsimp [post]
    apply congrArg (fun f => (normalize5 f fallback).w y)
    funext b
    congr 1
    rw [← Finset.prod_attach S (fun i => (Q b i).w
      ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => O)).symm
        (z, fun _ => o₀) i))]
    apply Finset.prod_congr rfl
    intro i hi
    simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
  change P.expect (fun a => (FinProb.pi (Q a)).expect post) = _
  simp_rw [hrestrict]
  simp only [FinProb.expect]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hBayes := Lane_q_s05_h5l.bayes_posterior_mean5 P
    (fun b => FinProb.pi (fun i : S => Q b i.1)) y fallback
  convert hBayes using 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [FinProb.pi]
  ring

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

/-- The marginal raw law at one bin, including its candidate parent. -/
def binLaw (v : Fin N) (w : BinVector5 n) : FinProb (Fin N × X.Stream) :=
  FinProb.bind (X.P.prior.partner v w) fun a => FinProb.pi fun _ => X.segLaw v a

/-- Repackage coarse data as the independent bin variables. -/
def coarseBinEquiv : X.Coarse ≃ (BinVector5 n → Fin N × X.Stream) where
  toFun c w := (c.1 w, c.2 w)
  invFun z := (fun w => (z w).1, fun w => (z w).2)
  left_inv c := by cases c; rfl
  right_inv z := by funext w; exact Prod.eta _

theorem coarseLaw_weight (v : Fin N) (c : X.Coarse) :
    (FinProb.pi (binLaw X v)).w (coarseBinEquiv X c) = (X.coarseLaw v).w c := by
  change (∏ w, (X.P.prior.partner v w).w (c.1 w) *
    ∏ s, (X.segLaw v (c.1 w)).w (c.2 w s)) =
      (∏ w, (X.P.prior.partner v w).w (c.1 w)) *
        ∏ w, ∏ s, (X.segLaw v (c.1 w)).w (c.2 w s)
  exact Finset.prod_mul_distrib

/-- The raw coarse law is a product of its per-bin laws. -/
theorem coarseLaw_expect (v : Fin N) (f : X.Coarse → ℝ) :
    (X.coarseLaw v).expect f =
      (FinProb.pi (binLaw X v)).expect (fun z => f ((coarseBinEquiv X).symm z)) := by
  symm
  simpa using Lane_sol_s05_h1.expect_equiv (X.coarseLaw v)
    (FinProb.pi (binLaw X v)) (coarseBinEquiv X) (coarseLaw_weight X v)
    (fun z => f ((coarseBinEquiv X).symm z))

/-- An interior posterior ignores the candidate draw and all other bins. -/
theorem interior_prior (v : Fin N) (c : X.Coarse) (w : BinVector5 n)
    (t : CubeVertex (X.p.m n)) (j : Fin (X.p.J n + 1)) :
    (X.prior (v, c) (.inl ((w, false), t, j))) =
      normalize5 (fun y => (X.P.prior.partner v w).w y *
        ∏ s ∈ Finset.univ.filter (fun s : Fin (X.p.streamSegs n) =>
          (s : ℕ) < X.p.uSeg n (j.val + 1)), (X.segLaw v y).w (c.2 w s)) X.y₀ := by
  unfold Setup5.prior Setup5.colWeight
  simp [HiddenKey5.coarse, HiddenKey5.level, Finset.prod_filter]

/-- The raw mean of an interior posterior equals the partner prior. -/
theorem interior_prior_mean (v : Fin N) (w : BinVector5 n)
    (t : CubeVertex (X.p.m n)) (j : Fin (X.p.J n + 1)) (y : Fin N) :
    (binLaw X v w).expect (fun z =>
      (normalize5 (fun a => (X.P.prior.partner v w).w a *
        ∏ s ∈ Finset.univ.filter (fun s : Fin (X.p.streamSegs n) =>
          (s : ℕ) < X.p.uSeg n (j.val + 1)), (X.segLaw v a).w (z.2 s)) X.y₀).w y) =
          (X.P.prior.partner v w).w y := by
  let post : X.Stream → ℝ := fun z =>
    (normalize5 (fun a => (X.P.prior.partner v w).w a *
      ∏ s ∈ Finset.univ.filter (fun s : Fin (X.p.streamSegs n) =>
        (s : ℕ) < X.p.uSeg n (j.val + 1)), (X.segLaw v a).w (z s)) X.y₀).w y
  change (FinProb.bind (X.P.prior.partner v w)
    (fun a => FinProb.pi fun _ : Fin (X.p.streamSegs n) => X.segLaw v a)).expect (fun z => post z.2) = _
  rw [FinProb.bind_expect (X.P.prior.partner v w)
    (fun a => FinProb.pi fun _ : Fin (X.p.streamSegs n) => X.segLaw v a) (fun _ z => post z)]
  simpa only [FinProb.expect, post] using product_posterior_mean (X.P.prior.partner v w) (fun a (_ : Fin (X.p.streamSegs n)) => X.segLaw v a)
    (Finset.univ.filter (fun s : Fin (X.p.streamSegs n) =>
      (s : ℕ) < X.p.uSeg n (j.val + 1))) (fun _ => X.y₀) X.y₀ y


/-- Products of functions with disjoint coordinate scopes integrate independently. -/
theorem pi_expect_prod_disjoint {I V : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq I] {A : V → Type*} [∀ v, Fintype (A v)]
    (P : ∀ v, FinProb (A v)) (S : Finset I) (scope : I → Finset V)
    (f : I → (∀ v, A v) → ℝ)
    (hdep : ∀ i ∈ S, FinProb.DependsOn (f i) (scope i))
    (hdis : (S : Set I).Pairwise (fun i j => Disjoint (scope i) (scope j))) :
    (FinProb.pi P).expect (fun z => ∏ i ∈ S, f i z) =
      ∏ i ∈ S, (FinProb.pi P).expect (f i) := by
  revert hdep hdis
  induction S using Finset.induction_on with
  | empty => intro hdep hdis; simp [FinProb.expect, FinProb.sum_eq_one]
  | @insert i S hi ih =>
    intro hdep hdis
    simp only [Finset.prod_insert hi]
    have hdepS : FinProb.DependsOn (fun z => ∏ j ∈ S, f j z) (S.biUnion scope) := by
      intro z z' hz
      apply Finset.prod_congr rfl
      intro j hj
      apply hdep j (Finset.mem_insert_of_mem hj) z z'
      intro v hv
      exact hz v (Finset.mem_biUnion.mpr ⟨j, hj, hv⟩)
    have hd : Disjoint (scope i) (S.biUnion scope) := by
      apply Finset.disjoint_left.mpr
      intro v hvi hvS
      obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hvS
      exact Finset.disjoint_left.mp
        (hdis (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
          (by intro h; subst j; exact hi hj)) hvi hvj
    rw [FinProb.pi_expect_mul_of_disjoint P (f i) (fun z => ∏ j ∈ S, f j z)
      (scope i) (S.biUnion scope) (hdep i (Finset.mem_insert_self _ _)) hdepS hd]
    rw [ih (fun j hj => hdep j (Finset.mem_insert_of_mem hj))
      (hdis.mono (Finset.subset_insert _ _))]

/-- The exact raw product identity for distinct interior bins. -/
theorem coarse_expect_prod {I : Type*} [Fintype I] [DecidableEq I]
    (v : Fin N) (w : I → BinVector5 n) (hw : Function.Injective w)
    (f : I → (Fin N × X.Stream) → ℝ) :
    (X.coarseLaw v).expect (fun c => ∏ i, f i (c.1 (w i), c.2 (w i))) =
      ∏ i, (binLaw X v (w i)).expect (f i) := by
  rw [coarseLaw_expect]
  let scope : I → Finset (BinVector5 n) := fun i => {w i}
  have hdep : ∀ i ∈ (Finset.univ : Finset I),
      FinProb.DependsOn (fun z : BinVector5 n → Fin N × X.Stream => f i (z (w i))) (scope i) := by
    intro i hi z z' hz
    exact congrArg (f i) (hz (w i) (Finset.mem_singleton_self _))
  have hdis : ((Finset.univ : Finset I) : Set I).Pairwise (fun i j => Disjoint (scope i) (scope j)) := by
    intro i hi j hj hij
    simp only [scope, Finset.disjoint_singleton]
    exact fun h => hij (hw h)
  change (FinProb.pi (binLaw X v)).expect (fun z => ∏ i, f i (z (w i))) = _
  rw [pi_expect_prod_disjoint (binLaw X v) Finset.univ scope
    (fun i z => f i (z (w i))) hdep hdis]
  apply Finset.prod_congr rfl
  intro i hi
  exact Lane_q_s05_h5l.pi_expect_singleton5 (binLaw X v) (w i) (f i)
    (X.y₀, fun _ _ => X.y₀)

private def halfBool : FinProb Bool where
  w _ := 1 / 2
  nonneg _ := by norm_num
  sum_eq_one := by norm_num [Fintype.sum_bool]

private def boolWeight {I : Type*} [Fintype I] (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

private def boolSupportEquiv (I : Type*) [Fintype I] [DecidableEq I] :
    (I → Bool) ≃ Finset I where
  toFun x := Finset.univ.filter fun i => x i = true
  invFun S i := decide (i ∈ S)
  left_inv x := by funext i; cases h : x i <;> simp [h]
  right_inv S := by ext i; simp

private theorem boolWeight_card (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) :
    (Finset.univ.filter fun x : I → Bool => boolWeight x = q).card =
      Nat.choose (Fintype.card I) q := by
  let e : {x : I → Bool // boolWeight x = q} ≃ {S : Finset I // S.card = q} :=
    (boolSupportEquiv I).subtypeEquiv (fun x => Iff.rfl)
  have h : Fintype.card {S : Finset I // S.card = q} = Nat.choose (Fintype.card I) q := by
    let f : {S : Finset I // S.card = q} ≃
        {S : Finset I // S ∈ Finset.univ.powersetCard q} := {
      toFun S := ⟨S.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.2⟩⟩
      invFun S := ⟨S.1, (Finset.mem_powersetCard.mp S.2).2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    rw [Fintype.card_congr f]
    simp [Finset.card_powersetCard]
  calc
    _ = Fintype.card {x : I → Bool // boolWeight x = q} := by
      simpa using (Fintype.card_subtype (fun x : I → Bool => boolWeight x = q)).symm
    _ = Fintype.card {S : Finset I // S.card = q} := Fintype.card_congr e
    _ = _ := h

private theorem bin_indicator_mean {I : Type*} [Fintype I] [DecidableEq I]
    {k : ℕ} (bin : ℕ → Fin k) (j : Fin k) :
    (FinProb.pi (fun _ : I => halfBool)).expect
      (fun x => if bin (boolWeight x) = j then 1 else 0) =
      (∑ q ∈ Finset.range (Fintype.card I + 1),
        if bin q = j then (Nat.choose (Fintype.card I) q : ℝ) else 0) /
          (2 : ℝ) ^ Fintype.card I := by
  have hcard : (Finset.univ.filter fun x : I → Bool => bin (boolWeight x) = j).card =
      ∑ q ∈ Finset.range (Fintype.card I + 1),
        if bin q = j then Nat.choose (Fintype.card I) q else 0 := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := boolWeight) (t := Finset.range (Fintype.card I + 1))]
    · apply Finset.sum_congr rfl
      intro q hq
      by_cases hj : bin q = j
      · rw [if_pos hj]
        have hf : (Finset.univ.filter (fun x : I → Bool => bin (boolWeight x) = j)).filter
            (fun x => boolWeight x = q) = Finset.univ.filter (fun x => boolWeight x = q) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact And.right
          · intro hx; exact ⟨by rw [hx]; exact hj, hx⟩
        rw [hf, boolWeight_card]
      · rw [if_neg hj]
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxq := (Finset.mem_filter.mp hx).2
        have hxj := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
        exact hj (by rwa [hxq] at hxj)
    · intro x hx
      apply Finset.mem_range.mpr
      have hle : boolWeight x ≤ Fintype.card I := Finset.card_le_univ _
      omega
  have hc : ((Finset.univ.filter fun x : I → Bool => bin (boolWeight x) = j).card : ℝ) =
      ∑ q ∈ Finset.range (Fintype.card I + 1),
        if bin q = j then (Nat.choose (Fintype.card I) q : ℝ) else 0 := by
    exact_mod_cast hcard
  simp only [FinProb.expect, FinProb.pi, halfBool, Finset.prod_const,
    Finset.card_univ, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hc, one_div, inv_pow, div_eq_mul_inv]

/-- Each coarse chunk's bin has its declared small probability under the uniform cube law. -/
theorem coarse_chunk_bin_mean {m : ℕ} (g : ChunkGeometry5 n m)
    (i : Fin coarseChunkCount5) (j : Fin (n + 1)) :
    (FinProb.pi (fun _ : Fin n => halfBool)).expect
      (fun x => if g.bin i (g.coarseCount x i) = j then 1 else 0) ≤
        2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) := by
  let C := g.coarseChunks i
  have hcount (x : CubeVertex n) : g.coarseCount x i = boolWeight (fun a : C => x a.1) := by
    dsimp [ChunkGeometry5.coarseCount, boolWeight, C]
    rw [Finset.filter_attach (fun a : Fin n => x a = true) (g.coarseChunks i)]
    simp
  simp_rw [hcount]
  rw [FinProb.pi_marginal_expect (fun _ : Fin n => halfBool) C
    (fun x => if g.bin i (boolWeight x) = j then 1 else 0)]
  rw [bin_indicator_mean]
  have hp := g.bin_probability_bound i j
  have hc : Fintype.card C = (g.coarseChunks i).card := Fintype.card_coe _
  rw [hc]
  exact (div_le_iff₀ (by positivity)).mpr hp


/-- The full coarse-bin fiber has the product small-bin bound. -/
theorem coarse_bin_fraction {m : ℕ} (g : ChunkGeometry5 n m) (w : BinVector5 n) :
    ((Finset.univ.filter fun x : CubeVertex n => g.coarseBin x = w).card : ℝ) /
        (2 : ℝ) ^ n ≤ (2 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ coarseChunkCount5 := by
  let f : Fin coarseChunkCount5 → CubeVertex n → ℝ := fun i x =>
    if g.bin i (g.coarseCount x i) = w i then 1 else 0
  have hdep : ∀ i ∈ (Finset.univ : Finset (Fin coarseChunkCount5)),
      FinProb.DependsOn (f i) (g.coarseChunks i) := by
    intro i hi x x' hx
    have hc : g.coarseCount x i = g.coarseCount x' i := by
      unfold ChunkGeometry5.coarseCount
      congr 1
      apply Finset.filter_congr
      intro a ha
      rw [hx a ha]
    simp [f, hc]
  have hdis : ((Finset.univ : Finset (Fin coarseChunkCount5)) : Set (Fin coarseChunkCount5)).Pairwise
      (fun i j => Disjoint (g.coarseChunks i) (g.coarseChunks j)) := by
    intro i hi j hj hij
    exact g.chunks_disjoint.1 i j hij
  have hpoint (x : CubeVertex n) :
      (∏ i, f i x) = if g.coarseBin x = w then 1 else 0 := by
    by_cases hw : g.coarseBin x = w
    · have he (i : Fin coarseChunkCount5) : g.bin i (g.coarseCount x i) = w i :=
        congrFun hw i
      simp [f, hw, he]
    · have hex : ∃ i, g.bin i (g.coarseCount x i) ≠ w i := by
        by_contra hh
        apply hw
        funext i
        by_contra hi
        exact hh ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hex
      simp only [if_neg hw]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [f, hi])
  have hfactor := pi_expect_prod_disjoint (fun _ : Fin n => halfBool) Finset.univ
    g.coarseChunks f hdep hdis
  have hmean :
      (FinProb.pi (fun _ : Fin n => halfBool)).expect
        (fun x => if g.coarseBin x = w then 1 else 0) =
      ((Finset.univ.filter fun x : CubeVertex n => g.coarseBin x = w).card : ℝ) /
        (2 : ℝ) ^ n := by
    simp only [FinProb.expect, FinProb.pi, halfBool, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul, one_div, inv_pow, div_eq_mul_inv]
  rw [← hmean, ← funext hpoint, hfactor]
  calc
    _ ≤ ∏ _i : Fin coarseChunkCount5, 2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg fun x hx => mul_nonneg
          ((FinProb.pi (fun _ : Fin n => halfBool)).nonneg x)
          (by dsimp [f]; split_ifs <;> norm_num)
      · intro i hi
        exact coarse_chunk_bin_mean g i (w i)
    _ = _ := by simp

/-- Passing from the whole cube to odd roles loses at most a factor of two. -/
theorem odd_bin_fraction {m : ℕ} (g : ChunkGeometry5 n m) (hn : 0 < n)
    (w : BinVector5 n) :
    ((Finset.univ.filter fun x : OddRole5 n => g.coarseBin x.1 = w).card : ℝ) ≤
      (2 * (2 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ coarseChunkCount5) *
        Fintype.card (OddRole5 n) := by
  have hinj : Function.Injective (fun x : OddRole5 n => x.1) := Subtype.val_injective
  have hsub :
      (Finset.univ.filter fun x : OddRole5 n => g.coarseBin x.1 = w).image Subtype.val ⊆
        Finset.univ.filter fun x : CubeVertex n => g.coarseBin x = w := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  have hc :
      ((Finset.univ.filter fun x : OddRole5 n => g.coarseBin x.1 = w).card : ℝ) ≤
        (Finset.univ.filter fun x : CubeVertex n => g.coarseBin x = w).card := by
    exact_mod_cast (by
      rw [← Finset.card_image_of_injective _ hinj]
      exact Finset.card_le_card hsub)
  have hprob := coarse_bin_fraction g w
  have hpar : (2 : ℝ) ^ n = 2 * Fintype.card (OddRole5 n) := by
    have hOdd : Fintype.card (OddRole5 n) = 2 ^ (n - 1) := by
      rw [Fintype.card_subtype]
      have he : (Finset.univ \ evenRoleSet n) =
          Finset.univ.filter (fun x : CubeVertex n => ¬ IsEvenRole x) := by
        ext x; simp [evenRoleSet]
      rw [← he]
      exact (parity_class_card hn).2
    rw [hOdd]
    have he : n = (n - 1) + 1 := by omega
    nth_rw 1 [he]
    rw [pow_succ]
    push_cast
    ring
  have hwhole := (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).mp hprob
  rw [hpar] at hwhole
  calc
    _ ≤ (2 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ coarseChunkCount5 *
        (2 * Fintype.card (OddRole5 n)) := hc.trans hwhole
    _ = _ := by ring

/-- Shrink the last parameter to keep every posterior cap below a small power of `n`. -/
def loadRequest : ParamReq5 where
  Kcap _ := 0
  Kpp _ := 0
  Kh _ := 0
  K1 _ := 0
  K2 _ := 0
  KD _ := 0
  Ks _ := 0
  KB _ := 0
  alpha x := 1 / (10000 * (|x.1.1.1.1.1.2.1| + 1) * (|x.1.1.1.1.2| + 1))
  alpha_pos x := by positivity

/-- The Step 1 cap is eventually `n^((j+5)/500)`, uniformly in the severity. -/
theorem eventually_prior_caps (p : Params5 γ K' χ) (hp : loadRequest.Holds p) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      Real.exp (p.Kcap * (p.q0 * p.uSeg n (j + 1))) ≤
        (n : ℝ) ^ (((j : ℝ) + 5) / 500) := by
  have ha : p.alpha ≤ 1 / (10000 * (p.Kcap + 1) * (p.K1 + 1)) := by
    simpa [loadRequest, Params5.pre6, Params5.pre5, Params5.pre4, Params5.pre3,
      Params5.pre2, Params5.pre1, abs_of_pos p.hKcap, abs_of_pos p.hK1] using hp.2.2.2.2.2.2.2.2
  have hbudget : p.Kcap * p.K1 * p.alpha ≤ 1 / 10000 := by
    have hden : 0 < 10000 * (p.Kcap + 1) * (p.K1 + 1) :=
      mul_pos (mul_pos (by norm_num) (by linarith [p.hKcap])) (by linarith [p.hK1])
    have hmul := (le_div_iff₀ hden).mp ha
    have hα := p.halpha.1
    have hk := p.hK1
    have hc := p.hKcap
    nlinarith [mul_pos hc hk]
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog : ∀ᶠ n : ℕ in atTop,
      max (Real.log 2 / p.alpha) (1000 * p.Kcap * p.q0) ≤ Real.log (n : ℝ) :=
    hlogTop.eventually_ge_atTop _
  filter_upwards [hlog, Filter.eventually_ge_atTop (1 : ℕ)] with n hlog hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hpow : 1 ≤ (n : ℝ) ^ p.alpha := Real.one_le_rpow hnR p.halpha.1.le
  have hmupper : (p.m n : ℝ) ≤ 2 * (n : ℝ) ^ p.alpha := by
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ p.alpha from Real.rpow_nonneg hnpos.le p.alpha))
    change (⌈(n : ℝ) ^ p.alpha⌉₊ : ℝ) ≤ _
    linarith
  have hmpos : (0 : ℝ) < p.m n := by
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (n : ℝ) ^ p.alpha) (Nat.le_ceil _)
  have hlogm : Real.log (p.m n : ℝ) ≤ 2 * p.alpha * Real.log (n : ℝ) := by
    have hh := Real.log_le_log hmpos hmupper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
      Real.log_rpow hnpos] at hh
    have hsmall := (div_le_iff₀ p.halpha.1).mp ((le_max_left _ _).trans hlog)
    linarith
  have hlogm0 : 0 ≤ Real.log (p.m n : ℝ) := by
    apply Real.log_nonneg
    exact hpow.trans (Nat.le_ceil _)
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  intro j
  have hceil : (p.uSeg n (j + 1) : ℝ) ≤
      p.K1 * (((j : ℝ) + 1) + 4) * Real.log (p.m n : ℝ) / p.q0 + 1 := by
    dsimp [Params5.uSeg]
    have hh := Nat.ceil_lt_add_one (show 0 ≤
      p.K1 * (((j : ℝ) + 1) + 4) * Real.log (p.m n : ℝ) / p.q0 from
      div_nonneg (mul_nonneg (mul_nonneg p.hK1.le (by positivity)) hlogm0) hq.le)
    push_cast
    exact hh.le
  have hbound : p.Kcap * ((p.q0 : ℝ) * p.uSeg n (j + 1)) ≤
      ((j : ℝ) + 5) / 500 * Real.log (n : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hceil (mul_nonneg p.hKcap.le hq.le)
    have h1' : p.Kcap * (p.q0 : ℝ) * p.uSeg n (j + 1) ≤
        p.Kcap * p.K1 * ((j : ℝ) + 5) * Real.log (p.m n : ℝ) + p.Kcap * p.q0 := by
      calc
        _ ≤ p.Kcap * p.q0 * (p.K1 * (((j : ℝ) + 1) + 4) *
          Real.log (p.m n : ℝ) / p.q0 + 1) := h1
        _ = _ := by field_simp [hq.ne']; ring
    have h2 := mul_le_mul_of_nonneg_left hlogm
      (mul_nonneg p.hKcap.le (mul_nonneg p.hK1.le (by positivity : 0 ≤ (j : ℝ) + 5)))
    have h3 := mul_le_mul_of_nonneg_right hbudget
      (mul_nonneg (by positivity : 0 ≤ (j : ℝ) + 5) (Real.log_nonneg hnR))
    have hconst := (le_max_right _ _).trans hlog
    have hmain : p.Kcap * p.K1 * ((j : ℝ) + 5) * Real.log (p.m n : ℝ) ≤
        1 / 5000 * ((j : ℝ) + 5) * Real.log (n : ℝ) := by
      nlinarith only [h2, h3]
    have hlog0 := Real.log_nonneg hnR
    have hjlog := mul_nonneg (show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j) hlog0
    nlinarith only [h1', hmain, hconst, hjlog, hlog0]
  rw [Real.rpow_def_of_pos hnpos]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith [hbound]

/-- The repeated-bin term tends to zero even after multiplying by the posterior cap. -/
theorem repeated_bin_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (4 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ coarseChunkCount5 *
        (n : ℝ) ^ (1 / 100 : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1099 / 100)).comp
    tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => (4 : ℝ) ^ coarseChunkCount5 *
      (n : ℝ) ^ (-(1099 / 100 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using h.const_mul ((4 : ℝ) ^ coarseChunkCount5)
  apply hh.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he : (n : ℝ) * (4 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ coarseChunkCount5 *
      (n : ℝ) ^ (1 / 100 : ℝ) = (4 : ℝ) ^ coarseChunkCount5 *
        (n : ℝ) ^ (-(1099 / 100 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hnpos.le (-(4 / 100 : ℝ)) coarseChunkCount5]
    calc
      _ = (4 : ℝ) ^ coarseChunkCount5 * ((n : ℝ) ^ (1 : ℝ) *
          (n : ℝ) ^ (-(4 / 100 : ℝ) * coarseChunkCount5) * (n : ℝ) ^ (1 / 100 : ℝ)) := by
        rw [Real.rpow_one]
        ring
      _ = (4 : ℝ) ^ coarseChunkCount5 *
          (n : ℝ) ^ (1 + (-(4 / 100 : ℝ) * coarseChunkCount5) + 1 / 100) := by
        rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
      _ = _ := by congr 1; norm_num [coarseChunkCount5]
  exact he.symm

/-- Interior severity-zero odd roles, the class requiring a moment estimate. -/
def interiorZero (r : OddRole5 n) : Prop := ¬ X.g.boundary r.1 ∧ X.g.severity r.1 = 0

def coreWeight (v : Fin N) (c : X.Coarse) (y : Fin N) (r : OddRole5 n) : ℝ :=
  if interiorZero X r then (N : ℝ) * (X.prior (v, c) (X.g.roleKey (X.p.J n) r.1)).w y else 0

def lowWeight (v : Fin N) (c : X.Coarse) (y : Fin N) (r : OddRole5 n) : ℝ :=
  if X.g.low (X.p.J n) r.1 then (N : ℝ) * (X.prior (v, c) (X.g.roleKey (X.p.J n) r.1)).w y else 0

theorem coreWeight_nonneg (v : Fin N) (c : X.Coarse) (y : Fin N) (r : OddRole5 n) :
    0 ≤ coreWeight X v c y r := by
  unfold coreWeight
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg N) ((X.prior _ _).nonneg y)
  · exact le_rfl

/-- Each core row reads precisely its own coarse bin. -/
theorem coreWeight_eq (v : Fin N) (c : X.Coarse) (y : Fin N) (r : OddRole5 n) :
    coreWeight X v c y r = if interiorZero X r then
      (N : ℝ) * (normalize5 (fun a =>
        (X.P.prior.partner v (X.g.coarseBin r.1)).w a *
          ∏ s ∈ Finset.univ.filter (fun s : Fin (X.p.streamSegs n) =>
            (s : ℕ) < X.p.uSeg n 1),
            (X.segLaw v a).w (c.2 (X.g.coarseBin r.1) s)) X.y₀).w y else 0 := by
  by_cases hr : interiorZero X r
  · have hlow : X.g.severity r.1 ≤ X.p.J n := by rw [hr.2]; exact Nat.zero_le _
    have hkey : X.g.key r.1 = (X.g.coarseBin r.1, false) := by
      simp [ChunkGeometry5.key, hr.1]
    have he : X.g.roleKey (X.p.J n) r.1 =
        .inl ((X.g.coarseBin r.1, false), X.g.sign r.1, ⟨0, Nat.zero_lt_succ _⟩) := by
      simp [ChunkGeometry5.roleKey, hlow, hkey, hr.2]
    rw [coreWeight, if_pos hr, if_pos hr, he, interior_prior]
  · simp [coreWeight, hr]

/-- The raw product of core rows on distinct bins is bounded by the partner atom cap. -/
theorem core_product_raw {I : Type*} [Fintype I] [DecidableEq I]
    (v : Fin N) (y : Fin N) (r : I → OddRole5 n)
    (hinj : Function.Injective (fun i => X.g.coarseBin (r i).1)) :
    (X.coarseLaw v).expect (fun c => ∏ i, coreWeight X v c y (r i)) ≤
      ∏ _i : I, (4 / χ ^ 2 : ℝ) := by
  let f : I → (Fin N × X.Stream) → ℝ := fun i z =>
    if interiorZero X (r i) then
      (N : ℝ) * (normalize5 (fun a =>
        (X.P.prior.partner v (X.g.coarseBin (r i).1)).w a *
          ∏ s ∈ Finset.univ.filter (fun s : Fin (X.p.streamSegs n) =>
            (s : ℕ) < X.p.uSeg n 1), (X.segLaw v a).w (z.2 s)) X.y₀).w y else 0
  have hf (c : X.Coarse) :
      (∏ i, coreWeight X v c y (r i)) =
        ∏ i, f i (c.1 (X.g.coarseBin (r i).1), c.2 (X.g.coarseBin (r i).1)) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact coreWeight_eq X v c y (r i)
  simp_rw [hf]
  rw [coarse_expect_prod X v _ hinj f]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg fun z hz => mul_nonneg ((binLaw X v _).nonneg z)
      (by
        dsimp [f]
        split_ifs
        · exact mul_nonneg (Nat.cast_nonneg N) ((normalize5 _ X.y₀).nonneg y)
        · exact le_rfl)
  · intro i hi
    by_cases hr : interiorZero X (r i)
    · have he := interior_prior_mean X v (X.g.coarseBin (r i).1)
        (X.g.sign (r i).1) ⟨0, Nat.zero_lt_succ _⟩ y
      have hm : (binLaw X v (X.g.coarseBin (r i).1)).expect (f i) =
          (N : ℝ) * (X.P.prior.partner v (X.g.coarseBin (r i).1)).w y := by
        simp only [f, if_pos hr, FinProb.expect]
        calc
          _ = (N : ℝ) * (binLaw X v (X.g.coarseBin (r i).1)).expect
              (fun z => (normalize5 (fun a =>
                (X.P.prior.partner v (X.g.coarseBin (r i).1)).w a *
                ∏ s ∈ Finset.univ.filter (fun s : Fin (X.p.streamSegs n) =>
                  (s : ℕ) < X.p.uSeg n 1), (X.segLaw v a).w (z.2 s)) X.y₀).w y) := by
                    simp [FinProb.expect, Finset.mul_sum, mul_comm, mul_left_comm]
          _ = _ := by rw [he]
      rw [hm]
      have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos X.y₀
      have hatom := X.P.prior.partner_atom v (X.g.coarseBin (r i).1) y
      rw [X.P.prior_atom_constant] at hatom
      have hh := (le_div_iff₀ hN).mp hatom
      nlinarith
    · simp [f, hr, FinProb.expect]
      positivity

/-- The core product reads no bins beyond those used by the selected rows. -/
theorem core_product_depends {I : Type*} [Fintype I]
    (v : Fin N) (y : Fin N) (r : I → OddRole5 n) :
    ∀ c c' : X.Coarse,
      (∀ w ∈ Finset.univ.image (fun i => X.g.coarseBin (r i).1),
        c.1 w = c'.1 w ∧ c.2 w = c'.2 w) →
      (∏ i, coreWeight X v c y (r i)) = ∏ i, coreWeight X v c' y (r i) := by
  intro c c' h
  apply Finset.prod_congr rfl
  intro i hi
  rw [coreWeight_eq, coreWeight_eq]
  have hh := (h _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).2
  rw [hh]


private theorem odd_total (hn : 0 < n) :
    (2 : ℝ) ^ n = 2 * Fintype.card (OddRole5 n) := by
  have hOdd : Fintype.card (OddRole5 n) = 2 ^ (n - 1) := by
    rw [Fintype.card_subtype]
    have he : (Finset.univ \ evenRoleSet n) =
        Finset.univ.filter (fun x : CubeVertex n => ¬ IsEvenRole x) := by
      ext x; simp [evenRoleSet]
    rw [← he]
    exact (parity_class_card hn).2
  rw [hOdd]
  have he : n = (n - 1) + 1 := by omega
  nth_rw 1 [he]
  rw [pow_succ]
  push_cast
  ring

private theorem odd_event_card (hn : 0 < n) (P : CubeVertex n → Prop) [DecidablePred P] (a : ℝ)
    (ha : ((Finset.univ.filter P).card : ℝ) / (2 : ℝ) ^ n ≤ a) :
    ((Finset.univ.filter fun r : OddRole5 n => P r.1).card : ℝ) ≤
      2 * a * Fintype.card (OddRole5 n) := by
  have hi : (Finset.univ.filter fun r : OddRole5 n => P r.1).image Subtype.val ⊆
      Finset.univ.filter P := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩
  have hc : ((Finset.univ.filter fun r : OddRole5 n => P r.1).card : ℝ) ≤
      (Finset.univ.filter P).card := by
    exact_mod_cast (by
      rw [← Finset.card_image_of_injective _ Subtype.val_injective]
      exact Finset.card_le_card hi)
  have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).mp ha
  rw [odd_total hn] at hh
  nlinarith

/-- The exceptional roles have a deterministic small average on every Step 1 support point. -/
theorem exception_average (hn : 1 ≤ n) (hGeom : ChunkEstimates5 X.g)
    (hcaps : ∀ j : ℕ, Real.exp (X.p.Kcap * (X.p.q0 * X.p.uSeg n (j + 1))) ≤
      (n : ℝ) ^ (((j : ℝ) + 5) / 500))
    (v : Fin N) (c : X.Coarse) (y : Fin N) (hpass : X.Step1Pass (v, c)) :
    (Fintype.card (OddRole5 n) : ℝ)⁻¹ *
      ∑ r, (lowWeight X v c y r - coreWeight X v c y r) ≤
        2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) +
          2 * (X.p.J n + 1 : ℕ) * (n : ℝ) ^ (-(1 / 10 : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by positivity
  have hm : 1 ≤ X.p.m n := by
    apply Nat.one_le_ceil_iff.mpr
    positivity
  have hJ : X.p.J n ≤ X.p.m n := Lane_sol_s05_h1.J_le_m X.p n hm
  have hMpos : (0 : ℝ) < Fintype.card (OddRole5 n) := by
    have hh := odd_total (n := n) hnpos
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ n by positivity]
  let boundary : OddRole5 n → ℝ := fun r =>
    if X.g.boundary r.1 ∧ X.g.severity r.1 = 0 then (n : ℝ) ^ (1 / 100 : ℝ) else 0
  let severe : Fin (X.p.J n + 1) → OddRole5 n → ℝ := fun j r =>
    if X.g.severity r.1 = j.val ∧ 1 ≤ j.val then
      (n : ℝ) ^ (((j.val : ℝ) + 5) / 500) else 0
  have hcap (r : OddRole5 n) (hlo : X.g.low (X.p.J n) r.1) :
      (N : ℝ) * (X.prior (v, c) (X.g.roleKey (X.p.J n) r.1)).w y ≤
        (n : ℝ) ^ (((X.g.severity r.1 : ℝ) + 5) / 500) := by
    have hocc : X.KeyOccurs (X.g.roleKey (X.p.J n) r.1) := Or.inl ⟨r.1, r.2, rfl⟩
    have hh := Lane_q_s05_h5l.step1_prior_cap5 X (v, c) hpass _ hocc y
    have hlevel : (X.g.roleKey (X.p.J n) r.1).level = X.g.severity r.1 := by
      unfold ChunkGeometry5.low at hlo
      simp [ChunkGeometry5.roleKey, hlo, HiddenKey5.level]
    rw [hlevel] at hh
    exact hh.trans (hcaps _)
  have hrow (r : OddRole5 n) : lowWeight X v c y r - coreWeight X v c y r ≤
      boundary r + ∑ j, severe j r := by
    have hs : 0 ≤ ∑ j, severe j r := by
      apply Finset.sum_nonneg
      intro j hj
      dsimp [severe]
      split_ifs <;> positivity
    have hb : 0 ≤ boundary r := by dsimp [boundary]; split_ifs <;> positivity
    by_cases hlo : X.g.low (X.p.J n) r.1
    · have hh := hcap r hlo
      by_cases hzero : X.g.severity r.1 = 0
      · by_cases hbound : X.g.boundary r.1
        · have hh0 : (N : ℝ) * (X.prior (v, c) (X.g.roleKey (X.p.J n) r.1)).w y ≤
              (n : ℝ) ^ (1 / 100 : ℝ) := by norm_num [hzero] at hh; exact hh
          simpa [lowWeight, coreWeight, interiorZero, hlo, boundary, hzero, hbound] using
            hh0.trans (le_add_of_nonneg_right hs)
        · simp [lowWeight, coreWeight, interiorZero, hlo, hzero, hbound, add_nonneg hb hs]
      · have hj : X.g.severity r.1 < X.p.J n + 1 := Nat.lt_succ_of_le hlo
        let j : Fin (X.p.J n + 1) := ⟨X.g.severity r.1, hj⟩
        have hsevere : severe j r = (n : ℝ) ^ (((X.g.severity r.1 : ℝ) + 5) / 500) := by
          simp [severe, j, show 1 ≤ X.g.severity r.1 by omega]
        have hsum := Finset.single_le_sum
          (fun j _ => show 0 ≤ severe j r by dsimp [severe]; split_ifs <;> positivity)
          (Finset.mem_univ j)
        rw [hsevere] at hsum
        simp only [lowWeight, if_pos hlo, coreWeight, interiorZero, hzero, and_false, if_false,
          sub_zero]
        linarith
    · have hno : ¬ interiorZero X r := by
        intro h
        apply hlo
        unfold ChunkGeometry5.low
        rw [h.2]
        exact Nat.zero_le _
      simp [lowWeight, coreWeight, hlo, hno, add_nonneg hb hs]
  have hboundary : (∑ r, boundary r) ≤
      2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) * Fintype.card (OddRole5 n) := by
    have hcard := odd_event_card (n := n) hnpos X.g.boundary _ hGeom.boundary_fraction
    have hsub : (Finset.univ.filter fun r : OddRole5 n =>
        X.g.boundary r.1 ∧ X.g.severity r.1 = 0) ⊆
      Finset.univ.filter (fun r : OddRole5 n => X.g.boundary r.1) := by
      intro r hr; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.1⟩
    have hh : ((Finset.univ.filter fun r : OddRole5 n =>
        X.g.boundary r.1 ∧ X.g.severity r.1 = 0).card : ℝ) ≤
      2 * (n : ℝ) ^ (-(5 / 100 : ℝ)) * Fintype.card (OddRole5 n) := by
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcard
    have hrpow : (n : ℝ) ^ (-(5 / 100 : ℝ)) * (n : ℝ) ^ (1 / 100 : ℝ) =
        (n : ℝ) ^ (-(4 / 100 : ℝ)) := by
      rw [← Real.rpow_add hnRpos]
      congr 1 <;> norm_num
    dsimp [boundary]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hh' := mul_le_mul_of_nonneg_right hh
      (Real.rpow_nonneg hnRpos.le (1 / 100))
    nlinarith [hrpow]
  have hsevere (j : Fin (X.p.J n + 1)) :
      (∑ r, severe j r) ≤ 2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) *
        Fintype.card (OddRole5 n) := by
    by_cases hj : 1 ≤ j.val
    · have hjm : j.val ≤ X.p.m n := (Nat.le_of_lt_succ j.isLt).trans hJ
      have hcard := odd_event_card (n := n) hnpos (fun x => j.val ≤ X.g.severity x)
        ((n : ℝ) ^ (-(13 / 100 : ℝ) * (j.val : ℝ)))
        (by simpa only using hGeom.severity_tail j.val hj hjm)
      have hsub : (Finset.univ.filter fun r : OddRole5 n =>
          X.g.severity r.1 = j.val ∧ 1 ≤ j.val) ⊆
        Finset.univ.filter (fun r : OddRole5 n => j.val ≤ X.g.severity r.1) := by
        intro r hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [(Finset.mem_filter.mp hr).2.1]⟩
      have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcard
      have hexp : -(13 / 100 : ℝ) * j.val + ((j.val : ℝ) + 5) / 500 ≤ -(1 / 10 : ℝ) := by
        have hh : (1 : ℝ) ≤ j.val := by exact_mod_cast hj
        linarith
      have hpow : (n : ℝ) ^ (-(13 / 100 : ℝ) * j.val) *
          (n : ℝ) ^ (((j.val : ℝ) + 5) / 500) ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) := by
        rw [← Real.rpow_add hnRpos]
        exact Real.rpow_le_rpow_of_exponent_le hnR hexp
      dsimp [severe]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hh := mul_le_mul_of_nonneg_right hc
        (Real.rpow_nonneg hnRpos.le (((j.val : ℝ) + 5) / 500))
      nlinarith
    · simp [severe, hj]
      positivity
  apply (inv_mul_le_iff₀ hMpos).mpr
  calc
    (∑ r, (lowWeight X v c y r - coreWeight X v c y r)) ≤
        ∑ r, (boundary r + ∑ j, severe j r) := Finset.sum_le_sum fun r _ => hrow r
    _ = (∑ r, boundary r) + ∑ j, ∑ r, severe j r := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ 2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) * Fintype.card (OddRole5 n) +
        ∑ _j : Fin (X.p.J n + 1), 2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) *
          Fintype.card (OddRole5 n) := add_le_add hboundary
            (Finset.sum_le_sum fun j _ => hsevere j)
    _ = _ := by simp; push_cast; ring


/-- The explicit exceptional-role upper bound is eventually at most one. -/
theorem exception_numerical_small (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) +
        2 * (p.J n + 1 : ℕ) * (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 := by
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 100)).comp
    tendsto_natCast_atTop_atTop
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 8 / 100)).comp
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) +
      8 * (n : ℝ) ^ (-(8 / 100 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, add_zero] using (h1.const_mul 2).add (h2.const_mul 8)
  have hsmall := hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, Filter.eventually_ge_atTop (1 : ℕ)] with n hsmall hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hpow : 1 ≤ (n : ℝ) ^ p.alpha := Real.one_le_rpow hnR p.halpha.1.le
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le p.alpha)
  have hm : (p.m n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 50 : ℝ) := by
    have hraw : (p.m n : ℝ) ≤ 2 * (n : ℝ) ^ p.alpha := by
      change (⌈(n : ℝ) ^ p.alpha⌉₊ : ℝ) ≤ _
      linarith
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hnR p.halpha.2.le) (by norm_num))
  have hm1 : 1 ≤ p.m n := by
    exact_mod_cast (hpow.trans (Nat.le_ceil _))
  have hJ : (p.J n + 1 : ℕ) ≤ 2 * p.m n := by
    have hh := Lane_sol_s05_h1.J_le_m p n hm1
    omega
  have hJreal : ((p.J n + 1 : ℕ) : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 50 : ℝ) := by
    have hh : ((p.J n + 1 : ℕ) : ℝ) ≤ 2 * (p.m n : ℝ) := by exact_mod_cast hJ
    linarith
  have hprod : (n : ℝ) ^ (1 / 50 : ℝ) * (n : ℝ) ^ (-(1 / 10 : ℝ)) =
      (n : ℝ) ^ (-(8 / 100 : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    congr 1 <;> norm_num
  have hh := mul_le_mul_of_nonneg_right hJreal
    (Real.rpow_nonneg hnpos.le (-(1 / 10 : ℝ)))
  nlinarith

/-- Scattered moments bound the severity-zero interior average after coarse avoidance. -/
theorem core_average_tail (hn : 1 ≤ n) (v : Fin N) (ν : FinProb X.Coarse)
    (hpass : ∀ c, ν.w c ≠ 0 → X.Step1Pass (v, c))
    (hcompare : ∀ (B : Finset (BinVector5 n)) (f : X.Coarse → ℝ),
      (∀ c, 0 ≤ f c) →
      (∀ c c', (∀ w ∈ B, c.1 w = c'.1 w ∧ c.2 w = c'.2 w) → f c = f c') →
      ν.expect f ≤ 2 ^ B.card * (X.coarseLaw v).expect f)
    (hcap0 : Real.exp (X.p.Kcap * (X.p.q0 * X.p.uSeg n 1)) ≤
      (n : ℝ) ^ (1 / 100 : ℝ))
    (hrepeat : (n : ℝ) * (4 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ coarseChunkCount5 *
      (n : ℝ) ^ (1 / 100 : ℝ) ≤ 1)
    (hN : N ≤ n * 2 ^ n)
    (htail : (n : ℝ) * (1 / 2 : ℝ) ^ n ≤ 1 / 100) :
    ν.pr (fun c => ∃ y, 8 * (4 / χ ^ 2 + 1) <
      (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, coreWeight X v c y r) ≤ 1 / 100 := by
  have hnpos : 0 < n := by omega
  letI : Nonempty (OddRole5 n) := by
    let even : CubeVertex n := fun _ => false
    have heven : IsEvenRole even := by simp [IsEvenRole, even]
    let i : Fin n := ⟨0, by omega⟩
    have hodd : ¬ IsEvenRole (cubeFlip even i) := by
      intro h
      exact (cubeFlip_parity even i).mp h heven
    exact ⟨⟨cubeFlip even i, hodd⟩⟩
  have hMne : (Fintype.card (OddRole5 n) : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card (OddRole5 n))).ne'
  let A : ℝ := 4 / χ ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C : ℝ := 8 * (A + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  let L : ℝ := (n : ℝ) ^ (1 / 100 : ℝ)
  let f : ℝ := (4 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ coarseChunkCount5
  let near : OddRole5 n → Finset (OddRole5 n) := fun r =>
    Finset.univ.filter fun s => X.g.coarseBin s.1 = X.g.coarseBin r.1
  let succ := Finset.univ.filter fun c : X.Coarse => ν.w c ≠ 0
  have hnear (r : OddRole5 n) : ((near r).card : ℝ) ≤ f * Fintype.card (OddRole5 n) := by
    have hh := odd_bin_fraction X.g hnpos (X.g.coarseBin r.1)
    have hm : 2 * (2 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ coarseChunkCount5 ≤ f := by
      dsimp [f]
      rw [show (4 * (n : ℝ) ^ (-(4 / 100 : ℝ))) =
        2 * (2 * (n : ℝ) ^ (-(4 / 100 : ℝ))) by ring,
        mul_pow (2 : ℝ) (2 * (n : ℝ) ^ (-(4 / 100 : ℝ))) coarseChunkCount5]
      apply mul_le_mul_of_nonneg_right
        (by
          have hh : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ 300 :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          simpa [coarseChunkCount5] using hh) (by positivity)
    exact hh.trans (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _))
  have hlabel (y : Fin N) :
      ν.pr (fun c => C < (Fintype.card (OddRole5 n) : ℝ)⁻¹ *
        ∑ r, coreWeight X v c y r) ≤ (1 / 4 : ℝ) ^ n := by
    let avg : X.Coarse → ℝ := fun c =>
      (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, coreWeight X v c y r
    have havg (c : X.Coarse) : 0 ≤ avg c := by
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun r _ => coreWeight_nonneg X v c y r)
    have hcap (r : OddRole5 n) (c : X.Coarse) (hc : c ∈ succ) :
        coreWeight X v c y r ≤ L := by
      have hpassc := hpass c (Finset.mem_filter.mp hc).2
      by_cases hr : interiorZero X r
      · have hocc : X.KeyOccurs (X.g.roleKey (X.p.J n) r.1) := Or.inl ⟨r.1, r.2, rfl⟩
        have hh := Lane_q_s05_h5l.step1_prior_cap5 X (v, c) hpassc _ hocc y
        have hlevel : (X.g.roleKey (X.p.J n) r.1).level = 0 := by
          simp [ChunkGeometry5.roleKey, hr.2, HiddenKey5.level]
        rw [hlevel] at hh
        exact (by simpa [coreWeight, hr, L] using hh.trans hcap0)
      · simp [coreWeight, hr, L]
        positivity
    have hjoint (q : ℕ) (hq : q ≤ n) (r : Fin q → OddRole5 n)
        (hsep : ∀ i j : Fin q, j < i → r i ∉ near (r j)) :
        ∑ c ∈ succ, ν.w c * ∏ i, coreWeight X v c y (r i) ≤
          (2 : ℝ) ^ q * ∏ _i : Fin q, A := by
      have hinj : Function.Injective (fun i => X.g.coarseBin (r i).1) := by
        intro i j hij
        by_contra hne
        rcases lt_or_gt_of_ne hne with hij' | hji'
        · exact hsep j i hij' (by simp [near, hij])
        · exact hsep i j hji' (by simp [near, hij])
      let B := Finset.univ.image (fun i => X.g.coarseBin (r i).1)
      have hB : B.card = q := by
        simp [B, Finset.card_image_of_injective _ hinj]
      have hraw := core_product_raw X v y r hinj
      have hc := hcompare B (fun c => ∏ i, coreWeight X v c y (r i))
        (fun c => Finset.prod_nonneg fun i _ => coreWeight_nonneg X v c y (r i))
        (core_product_depends X v y r)
      rw [hB] at hc
      have hsum : (∑ c ∈ succ, ν.w c * ∏ i, coreWeight X v c y (r i)) =
          ν.expect (fun c => ∏ i, coreWeight X v c y (r i)) := by
        simp only [succ, Finset.sum_filter, FinProb.expect]
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hz : ν.w c = 0 <;> simp [hz]
      rw [hsum]
      exact hc.trans (mul_le_mul_of_nonneg_left hraw (by positivity))
    have hmoment := scattered_moments ν.w ν.nonneg succ
      (fun r c => coreWeight X v c y r)
      (fun r c => coreWeight_nonneg X v c y r) L (by dsimp [L]; positivity) hcap near
      (by intro r; simp [near]) f hnear n 2 (by norm_num)
      (fun _ => A) (fun _ => hA) hjoint
    have hmoment' : ν.expect (fun c => avg c ^ n) ≤
        (2 : ℝ) ^ n * (A + (n : ℝ) * f * L) ^ n := by
      have hmean : (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ _r : OddRole5 n, A = A := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ hMne, one_mul]
      rw [hmean] at hmoment
      have hsum : (∑ c ∈ succ, ν.w c * avg c ^ n) = ν.expect (fun c => avg c ^ n) := by
        simp only [succ, Finset.sum_filter, FinProb.expect]
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hz : ν.w c = 0 <;> simp [hz]
      change (∑ c ∈ succ, ν.w c * avg c ^ n) ≤ _ at hmoment
      rw [hsum] at hmoment
      exact hmoment
    have hrepeat' : (n : ℝ) * f * L ≤ 1 := hrepeat
    have hbound : ν.expect (fun c => avg c ^ n) ≤ (2 * (A + 1)) ^ n := by
      calc
        _ ≤ (2 : ℝ) ^ n * (A + (n : ℝ) * f * L) ^ n := hmoment'
        _ ≤ (2 : ℝ) ^ n * (A + 1) ^ n := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by dsimp [f, L]; positivity) (by linarith) n) (by positivity)
        _ = _ := (mul_pow _ _ _).symm
    have hmarkov := FinProb.markov ν (fun c => avg c ^ n) (C ^ n)
      (fun c => pow_nonneg (havg c) n) (pow_pos hC n)
    have hmono := FinProb.pr_mono ν (fun c => C < avg c) (fun c => C ^ n ≤ avg c ^ n)
      (fun c hc => pow_le_pow_left₀ hC.le hc.le n)
    have hratio : (2 * (A + 1)) ^ n / C ^ n = (1 / 4 : ℝ) ^ n := by
      rw [← div_pow]
      congr 1
      dsimp [C]
      field_simp [show A + 1 ≠ 0 by positivity]
      ring
    exact (hmono.trans hmarkov).trans ((div_le_div_of_nonneg_right hbound (by positivity)).trans hratio.le)
  have hunion := FinProb.pr_exists_le_sum5 ν (fun y c => C <
    (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, coreWeight X v c y r)
  calc
    _ ≤ ∑ y : Fin N, ν.pr (fun c => C < (Fintype.card (OddRole5 n) : ℝ)⁻¹ *
        ∑ r, coreWeight X v c y r) := hunion
    _ ≤ ∑ _y : Fin N, (1 / 4 : ℝ) ^ n := Finset.sum_le_sum fun y _ => hlabel y
    _ = (N : ℝ) * (1 / 4 : ℝ) ^ n := by simp
    _ ≤ ((n * 2 ^ n : ℕ) : ℝ) * (1 / 4 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hN) (by positivity)
    _ = (n : ℝ) * (1 / 2 : ℝ) ^ n := by
      push_cast
      rw [mul_assoc, ← mul_pow]
      norm_num
    _ ≤ _ := htail


/-- Combine the moment estimate and the deterministic exceptional-role bound. -/
theorem low_average_tail (hn : 1 ≤ n) (v : Fin N) (ν : FinProb X.Coarse)
    (hGeom : ChunkEstimates5 X.g) (hN : N ≤ n * 2 ^ n)
    (hpass : ∀ c, ν.w c ≠ 0 → X.Step1Pass (v, c))
    (hcompare : ∀ (B : Finset (BinVector5 n)) (f : X.Coarse → ℝ),
      (∀ c, 0 ≤ f c) →
      (∀ c c', (∀ w ∈ B, c.1 w = c'.1 w ∧ c.2 w = c'.2 w) → f c = f c') →
      ν.expect f ≤ 2 ^ B.card * (X.coarseLaw v).expect f)
    (hcaps : ∀ j : ℕ, Real.exp (X.p.Kcap * (X.p.q0 * X.p.uSeg n (j + 1))) ≤
      (n : ℝ) ^ (((j : ℝ) + 5) / 500))
    (hexception : 2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) +
      2 * (X.p.J n + 1 : ℕ) * (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1)
    (hrepeat : (n : ℝ) * (4 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ coarseChunkCount5 *
      (n : ℝ) ^ (1 / 100 : ℝ) ≤ 1)
    (htail : (n : ℝ) * (1 / 2 : ℝ) ^ n ≤ 1 / 100) :
    ν.pr (fun c => ∃ y, 8 * (4 / χ ^ 2 + 1) + 1 <
      (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, lowWeight X v c y r) ≤ 1 / 100 := by
  have hcore := core_average_tail X hn v ν hpass hcompare (by convert hcaps 0 using 1 <;> norm_num)
    hrepeat hN htail
  apply le_trans _ hcore
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro c hc
  by_cases hw : ν.w c = 0
  · simp [hw]
  · by_cases hbad : ∃ y, 8 * (4 / χ ^ 2 + 1) + 1 <
        (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, lowWeight X v c y r
    · obtain ⟨y, hy⟩ := hbad
      have hbad : ∃ y, 8 * (4 / χ ^ 2 + 1) + 1 <
          (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, lowWeight X v c y r := ⟨y, hy⟩
      have he := (exception_average X hn hGeom hcaps v c y (hpass c hw)).trans hexception
      rw [Finset.sum_sub_distrib, mul_sub] at he
      have hc : ∃ y, 8 * (4 / χ ^ 2 + 1) <
          (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ r, coreWeight X v c y r := by
        refine ⟨y, ?_⟩
        linarith
      simp only [if_pos hbad, if_pos hc, le_refl]
    · simp only [if_neg hbad]
      split_ifs
      · exact ν.nonneg c
      · exact le_rfl

/-- The numerical bounds used in the L1 proof hold simultaneously from one dimension onward. -/
theorem eventually_load_bounds (p : Params5 γ K' χ) (hp : loadRequest.Holds p) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
      (∀ j : ℕ, Real.exp (p.Kcap * (p.q0 * p.uSeg n (j + 1))) ≤
        (n : ℝ) ^ (((j : ℝ) + 5) / 500)) ∧
      (2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) +
        2 * (p.J n + 1 : ℕ) * (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1) ∧
      ((n : ℝ) * (4 * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ coarseChunkCount5 *
        (n : ℝ) ^ (1 / 100 : ℝ) ≤ 1) ∧
      ((n : ℝ) * (1 / 2 : ℝ) ^ n ≤ 1 / 100) := by
  have hrepeat := repeated_bin_tendsto.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have htail := Lane_q_s05_h5l.halfPowerTail_tendsto.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), eventually_prior_caps p hp,
    exception_numerical_small p, hrepeat, htail] with n hn hc he hr ht
  exact ⟨hn, hc, he, hr.le, ht.le⟩

end
end HypercubeRamsey.Lane_sol_s05_h5l
