import HypercubeRamsey.S05.Centres_sol_s05_k1_scales
import HypercubeRamsey.S05.Centres_sol_s05_centres_counts

namespace HypercubeRamsey.Lane_sol_s05_k1

open Classical OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def starTypes (y : OddRole5 n) : Finset X.Ty :=
  (Setup5.evenNbrs y).image (fun a => X.g.evenType (X.p.J n) a.1)

/-- Colouring each distinct neighbouring type with one of two abstract IDs
injects a Boolean cube into the occurring records. The frozen record count
therefore also bounds the number of arrays in a star. -/
theorem starTypes_record_count (y : OddRole5 n) (C : ℝ) (hc : X.RecordCount C)
    (hT : 2 ≤ X.p.T n) :
    (2 : ℝ) ^ (starTypes X y).card ≤ abstractRecordBudget X C y := by
  let i0 : Fin (X.p.T n) := ⟨0, by omega⟩
  let i1 : Fin (X.p.T n) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by intro h; have h' := congrArg Fin.val h; simp [i0, i1] at h'
  let β := fun (f : starTypes X y → Bool) (K : X.Ty) =>
    if hK : K ∈ starTypes X y then f ⟨K, hK⟩ else false
  let μ := fun (f : starTypes X y → Bool) (s : X.St.Site) =>
    if β f (Lane_sol_s05_centres.siteType X s) = true then i1 else i0
  let emit := fun f : starTypes X y → Bool => Lane_sol_s05_centres.shapeRecord X y (μ f)
  have haK (a : EvenRole5 n) (ha : a ∈ Setup5.evenNbrs y) :
      X.g.evenType (X.p.J n) a.1 ∈ starTypes X y := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hmu (f : starTypes X y → Bool) (a : EvenRole5 n) (ha : a ∈ Setup5.evenNbrs y) :
      μ f (X.St.stateOf a.1) = if f ⟨X.g.evenType (X.p.J n) a.1, haK a ha⟩ = true then i1 else i0 := by
    simp only [μ, Lane_sol_s05_centres.siteType_even, β, dif_pos (haK a ha)]
  have hobs (f : starTypes X y → Bool) (K : starTypes X y) :
      (i1, K.1) ∈ (emit f).2.1 ↔ f K = true := by
    have ho : (emit f).2.1 = (Setup5.evenNbrs y).image
        (fun a => (μ f (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)) := by
      ext c
      simp only [emit, Lane_sol_s05_centres.shapeRecord, Finset.mem_image]
    rw [ho]
    constructor
    · intro h
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
      have hk : X.g.evenType (X.p.J n) a.1 = K.1 := congrArg Prod.snd he
      have hi : μ f (X.St.stateOf a.1) = i1 := congrArg Prod.fst he
      rw [hmu f a ha] at hi
      have hs : (⟨X.g.evenType (X.p.J n) a.1, haK a ha⟩ : starTypes X y) = K := Subtype.ext hk
      rw [hs] at hi
      by_cases hf : f K = true
      · exact hf
      · simp only [hf, ite_false] at hi
        exact (h01 hi).elim
    · intro hf
      obtain ⟨a, ha, hk⟩ := Finset.mem_image.mp K.2
      have hs : (⟨X.g.evenType (X.p.J n) a.1, haK a ha⟩ : starTypes X y) = K := Subtype.ext hk
      apply Finset.mem_image.mpr
      refine ⟨a, ha, Prod.ext ?_ hk⟩
      rw [hmu f a ha, hs, if_pos hf]
  have hemit : Function.Injective emit := by
    intro f g he
    funext K
    have hmem : (i1, K.1) ∈ (emit f).2.1 ↔ (i1, K.1) ∈ (emit g).2.1 := by rw [he]
    rw [hobs f K, hobs g K] at hmem
    cases hf : f K <;> cases hg : g K <;> simp_all
  let A := Finset.univ.filter (fun r : X.AbsRecord =>
    X.RecOccursAt r (X.g.sign y.1) (X.g.severity y.1) ∧ r.1 = X.g.roleKey (X.p.J n) y.1)
  have hsub : (Finset.univ.image emit) ⊆ A := by
    intro r hr
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hr
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨y, μ f, Lane_sol_s05_centres.shapeRecord_from X y (μ f), rfl, rfl⟩, rfl⟩
  calc
    _ = ((Finset.univ.image emit).card : ℝ) := by
      rw [Finset.card_image_of_injective _ hemit]
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (A.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ _ := hc (X.g.roleKey (X.p.J n) y.1) (X.g.sign y.1) (X.g.severity y.1)

theorem starTypes_log_bound (y : OddRole5 n) (C : ℝ) (hc : X.RecordCount C)
    (hT : 2 ≤ X.p.T n) :
    ((starTypes X y).card : ℝ) * Real.log 2 ≤
      C * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
        (((X.g.roleKey (X.p.J n) y.1).level : ℝ) + 1) * Real.log (X.p.m n) +
        (if (X.g.roleKey (X.p.J n) y.1).isLeft ∧
            (X.g.roleKey (X.p.J n) y.1).level = X.p.J n then
          (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0)) := by
  have h := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (starTypes X y).card)
    (starTypes_record_count X y C hc hT)
  simpa only [abstractRecordBudget, Real.log_exp, Real.log_pow] using h

theorem observationLength_star_bound {Id : Type} [DecidableEq Id]
    (r : X.RecordOn Id) (y : OddRole5 n) (μ : X.St.Site → Id) (hr : X.RecordFrom r y μ)
    (hids : (recordIds X r).card ≤ X.p.T n) (B : ℝ) (hB : 0 ≤ B)
    (hlen : ∀ c ∈ r.2.1, r.1 ∈ c.2.2.1 →
      (X.p.typeBlocks n c.2 * (X.p.q0 * X.p.typeSegs n c.2) : ℕ) ≤ B) :
    observationLength X r ≤ (X.p.T n : ℝ) * (starTypes X y).card * B := by
  letI : DecidableEq (Id × X.Ty) := Classical.decEq _
  have hsub : r.2.1 ⊆ (recordIds X r).product (starTypes X y) := by
    intro c hc
    refine Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨c, hc, rfl⟩, ?_⟩
    have hc' := (Finset.ext_iff.mp hr.2.1 c).mp hc
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hc'
    exact Finset.mem_image.mpr ⟨a, ha, congrArg Prod.snd he⟩
  have hcard : (r.2.1.card : ℝ) ≤ (X.p.T n : ℝ) * (starTypes X y).card := by
    have hh := Finset.card_le_card hsub
    rw [Finset.product_eq_sprod, Finset.card_product] at hh
    exact (Nat.cast_le.mpr hh).trans (by exact_mod_cast Nat.mul_le_mul_right _ hids)
  unfold observationLength
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _c ∈ r.2.1.filter (fun c => r.1 ∈ c.2.2.1), B := by
      apply Finset.sum_le_sum
      intro c hc
      exact hlen c (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hc).2
    _ = ((r.2.1.filter (fun c => r.1 ∈ c.2.2.1)).card : ℝ) * B := by simp
    _ ≤ (r.2.1.card : ℝ) * B := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_filter_le _ _)) hB
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB

theorem low_type_of_listed (x : CubeVertex n) (ℓ : X.Key) (hl : ℓ.isLeft)
    (hm : ℓ ∈ X.g.typeKeys (X.p.J n) x) : X.g.low (X.p.J n) x := by
  by_contra hx
  change ¬ X.g.severity x ≤ X.p.J n at hx
  simp only [ChunkGeometry5.typeKeys, if_neg hx, Finset.mem_image] at hm
  obtain ⟨i, _, he⟩ := hm
  rw [← he] at hl
  simp at hl

theorem observationLength_low_bound {Id : Type} [DecidableEq Id]
    (r : X.RecordOn Id) (y : OddRole5 n) (μ : X.St.Site → Id) (hr : X.RecordFrom r y μ)
    (hl : r.1.isLeft) (hids : (recordIds X r).card ≤ X.p.T n) (B : ℝ) (hB : 0 ≤ B)
    (hnum : ∀ j : ℕ, j ≤ X.p.J n → (X.p.q0 * X.p.uSeg n j * X.p.lowBlocks n j : ℕ) ≤ B) :
    observationLength X r ≤ (X.p.T n : ℝ) * (starTypes X y).card * B := by
  letI : DecidableEq (Id × X.Ty) := Classical.decEq _
  apply observationLength_star_bound X r y μ hr hids B hB
  intro c hc hk
  have hc' := (Finset.ext_iff.mp hr.2.1 c).mp hc
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hc'
  have hK : c.2 = X.g.evenType (X.p.J n) a.1 := (congrArg Prod.snd he).symm
  have hmem : r.1 ∈ X.g.typeKeys (X.p.J n) a.1 := by simpa only [hK, ChunkGeometry5.evenType] using hk
  have haLow := low_type_of_listed X a.1 r.1 hl hmem
  change X.g.severity a.1 ≤ X.p.J n at haLow
  let j : Fin (X.p.J n + 1) := ⟨X.g.severity a.1, Nat.lt_succ_of_le haLow⟩
  have htag : c.2.2.2 = some j := by
    rw [hK]
    simp only [ChunkGeometry5.evenType, dite_eq_left haLow, j]
  simpa only [Params5.typeBlocks, Params5.typeSegs, htag, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    hnum j.val (Nat.le_of_lt_succ j.isLt)

theorem starTypes_card_bound (y : OddRole5 n) (hy : X.g.low (X.p.J n) y.1)
    (C : ℝ) (hC : 0 ≤ C) (hc : X.RecordCount C) (hT : 2 ≤ X.p.T n)
    (hm : 1 ≤ (X.p.m n : ℝ))
    (hpat : (X.p.T n : ℝ) * Real.log (X.p.T n) +
      (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) ≤ (X.p.m n : ℝ) ^ (1 / 50 : ℝ))
    (hmargin : (2001 * C / Real.log 2) * (X.p.m n : ℝ) ^ (51 / 1000 : ℝ) ≤ (X.p.m n : ℝ) ^ (3 / 50 : ℝ)) :
    ((starTypes X y).card : ℝ) ≤ (X.p.m n : ℝ) ^ (3 / 50 : ℝ) := by
  have hmpos : (0 : ℝ) < X.p.m n := by linarith
  have hlog : 0 ≤ Real.log (X.p.m n : ℝ) := Real.log_nonneg hm
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlev : (X.g.roleKey (X.p.J n) y.1).level ≤ X.p.J n := by
    change X.g.severity y.1 ≤ X.p.J n at hy
    simpa only [ChunkGeometry5.roleKey, dite_eq_left hy, HiddenKey5.level] using hy
  have hJ : (X.p.J n : ℝ) ≤ (X.p.m n : ℝ) ^ (1 / 20 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpow1 : 1 ≤ (X.p.m n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow hm (by norm_num)
  have hlevR : ((X.g.roleKey (X.p.J n) y.1).level : ℝ) + 1 ≤ 2 * (X.p.m n : ℝ) ^ (1 / 20 : ℝ) := by
    have hh : ((X.g.roleKey (X.p.J n) y.1).level : ℝ) ≤ X.p.J n := by exact_mod_cast hlev
    linarith
  have hl : Real.log (X.p.m n : ℝ) ≤ 1000 * (X.p.m n : ℝ) ^ (1 / 1000 : ℝ) := by
    have hh := Real.log_le_rpow_div (Nat.cast_nonneg (X.p.m n)) (by norm_num : (0 : ℝ) < 1 / 1000)
    convert hh using 1 <;> ring
  have hprod : (((X.g.roleKey (X.p.J n) y.1).level : ℝ) + 1) * Real.log (X.p.m n : ℝ) ≤
      2000 * (X.p.m n : ℝ) ^ (51 / 1000 : ℝ) := by
    calc
      _ ≤ (2 * (X.p.m n : ℝ) ^ (1 / 20 : ℝ)) * (1000 * (X.p.m n : ℝ) ^ (1 / 1000 : ℝ)) :=
        mul_le_mul hlevR hl hlog (by positivity)
      _ = _ := by
        rw [show (2 * (X.p.m n : ℝ) ^ (1 / 20 : ℝ)) * (1000 * (X.p.m n : ℝ) ^ (1 / 1000 : ℝ)) =
          2000 * ((X.p.m n : ℝ) ^ (1 / 20 : ℝ) * (X.p.m n : ℝ) ^ (1 / 1000 : ℝ)) by ring,
          ← Real.rpow_add hmpos]
        norm_num
  have hit : (if (X.g.roleKey (X.p.J n) y.1).isLeft ∧
      (X.g.roleKey (X.p.J n) y.1).level = X.p.J n then
      (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0) ≤
      (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) := by
    split_ifs <;> first | exact le_rfl | positivity
  have hpw : (X.p.m n : ℝ) ^ (1 / 50 : ℝ) ≤ (X.p.m n : ℝ) ^ (51 / 1000 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have hcount := starTypes_log_bound X y C hc hT
  have htotal : ((starTypes X y).card : ℝ) * Real.log 2 ≤ 2001 * C * (X.p.m n : ℝ) ^ (51 / 1000 : ℝ) := by
    have hs : (X.p.T n : ℝ) * Real.log (X.p.T n) +
      (((X.g.roleKey (X.p.J n) y.1).level : ℝ) + 1) * Real.log (X.p.m n) +
      (if (X.g.roleKey (X.p.J n) y.1).isLeft ∧
          (X.g.roleKey (X.p.J n) y.1).level = X.p.J n then
          (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0) ≤
        2001 * (X.p.m n : ℝ) ^ (51 / 1000 : ℝ) := by linarith
    have hh := mul_le_mul_of_nonneg_left hs hC
    nlinarith
  have hd : ((starTypes X y).card : ℝ) ≤ (2001 * C / Real.log 2) * (X.p.m n : ℝ) ^ (51 / 1000 : ℝ) := by
    have hdiv := (le_div_iff₀ hlog2).mpr htotal
    convert hdiv using 1 <;> ring
  exact hd.trans hmargin

end
end HypercubeRamsey.Lane_sol_s05_k1
