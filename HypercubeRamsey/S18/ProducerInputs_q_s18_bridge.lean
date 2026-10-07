import HypercubeRamsey.S16.Geometry
import HypercubeRamsey.Tools.Ramsey

namespace HypercubeRamsey.S18.Lane_q_s18_bridge

open Classical
open Filter
open scoped BigOperators

private theorem fv_sq_one {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (x y : Fin N) : (fv E c x y) ^ 2 = 1 := by
  by_cases h : Hits E c x y <;> simp [fv, hit, h]
  <;> norm_num

private theorem corr_symmetric {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin N → ℝ) (x y : Fin N) : corr E c π x y = corr E c π y x := by
  unfold corr
  apply Finset.sum_congr rfl
  intro z hz
  ring

private theorem corr_diagonal_le_one {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (π : Law N) (x : Fin N) : corr E c π.w x x ≤ 1 := by
  unfold corr
  calc
    (∑ y, π.w y * fv E c x y * fv E c x y) = ∑ y, π.w y := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        π.w y * fv E c x y * fv E c x y = π.w y * (fv E c x y) ^ 2 := by ring
        _ = π.w y := by rw [fv_sq_one, mul_one]
    _ = 1 := π.sum_eq_one
    _ ≤ 1 := le_rfl

private theorem correlation_pair_in_large_aligned_set
    {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour) (π : Law N)
    (ξ θ σ : ℝ) (hξ : 0 < ξ) (hθ : 3 * θ < ξ ^ 2 / 4)
    (hθpos : 0 < θ) (hξlt : ξ < 1)
    (hσ : σ ^ 2 = 1) (x : Fin N) (S : Finset (Fin N))
    (hcard : (4 / ξ ^ 2 : ℝ) ≤ (S.card : ℝ))
    (halign : ∀ z ∈ S, ξ < σ * corr E c π.w x z) :
    ∃ z ∈ S, ∃ z' ∈ S, z ≠ z' ∧ 3 * θ < corr E c π.w z z' := by
  classical
  let F : Fin N → ℝ := fun y => σ * Real.sqrt (π.w y) * fv E c x y
  let G : Fin N → ℝ := fun y => Real.sqrt (π.w y) * ∑ z ∈ S, fv E c z y
  have hF2 : ∑ y, F y ^ 2 = 1 := by
    calc
      (∑ y, F y ^ 2) = ∑ y, π.w y := by
        apply Finset.sum_congr rfl
        intro y hy
        have hsqrt := Real.sq_sqrt (π.nonneg y)
        calc
          F y ^ 2 = (σ * Real.sqrt (π.w y) * fv E c x y) ^ 2 := by rfl
          _ = σ ^ 2 * (Real.sqrt (π.w y)) ^ 2 * (fv E c x y) ^ 2 := by ring
          _ = π.w y := by rw [hσ, hsqrt, fv_sq_one]; ring
      _ = 1 := π.sum_eq_one
  have hG2 : ∑ y, G y ^ 2 = ∑ z ∈ S, ∑ z' ∈ S, corr E c π.w z z' := by
    calc
      (∑ y, G y ^ 2) = ∑ y, π.w y * (∑ z ∈ S, fv E c z y) ^ 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hsqrt := Real.sq_sqrt (π.nonneg y)
        calc
          G y ^ 2 = (Real.sqrt (π.w y) * ∑ z ∈ S, fv E c z y) ^ 2 := by rfl
          _ = π.w y * (∑ z ∈ S, fv E c z y) ^ 2 := by rw [mul_pow, hsqrt]
      _ = ∑ y, ∑ z ∈ S, ∑ z' ∈ S,
            π.w y * fv E c z y * fv E c z' y := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z' hz'
        ring
      _ = ∑ z ∈ S, ∑ z' ∈ S, corr E c π.w z z' := by
        simp_rw [corr]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z hz
        rw [Finset.sum_comm]
  have hinner : ∑ y, F y * G y = ∑ z ∈ S, σ * corr E c π.w x z := by
    calc
      (∑ y, F y * G y) =
          ∑ y, ∑ z ∈ S, σ * (π.w y * fv E c x y * fv E c z y) := by
        apply Finset.sum_congr rfl
        intro y hy
        have hsqrt := Real.sq_sqrt (π.nonneg y)
        calc
          F y * G y =
              (σ * Real.sqrt (π.w y) * fv E c x y) *
                (Real.sqrt (π.w y) * ∑ z ∈ S, fv E c z y) := by rfl
          _ = ∑ z ∈ S, σ * (π.w y * fv E c x y * fv E c z y) := by
            have hmul :
                (σ * Real.sqrt (π.w y) * fv E c x y) *
                  (Real.sqrt (π.w y) * ∑ z ∈ S, fv E c z y) =
                (σ * π.w y * fv E c x y) * ∑ z ∈ S, fv E c z y := by
              calc
                _ = σ * (Real.sqrt (π.w y) * Real.sqrt (π.w y)) *
                    fv E c x y * ∑ z ∈ S, fv E c z y := by ring
                _ = (σ * π.w y * fv E c x y) * ∑ z ∈ S, fv E c z y := by
                  rw [← sq, hsqrt]
            rw [hmul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z hz
            ring
      _ = ∑ z ∈ S, σ * corr E c π.w x z := by
        rw [Finset.sum_comm]
        simp [corr, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  have hinner_strict : (S.card : ℝ) * ξ < ∑ y, F y * G y := by
    rw [hinner]
    have hSposR : (0 : ℝ) < (S.card : ℝ) := by
      have hpos : 0 < (4 / ξ ^ 2 : ℝ) := by positivity
      exact hpos.trans_le hcard
    have hScard : 0 < S.card := by exact_mod_cast hSposR
    have hSpos : S.Nonempty := Finset.card_pos.mp hScard
    calc
      (S.card : ℝ) * ξ = ∑ z ∈ S, ξ := by simp
      _ < ∑ z ∈ S, σ * corr E c π.w x z := by
        apply Finset.sum_lt_sum
        · intro z hz
          exact (halign z hz).le
        · obtain ⟨z, hz⟩ := hSpos
          exact ⟨z, hz, halign z hz⟩
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N)) F G
  rw [hF2, hG2, one_mul] at hcs
  have hpair : ((S.card : ℝ) * ξ) ^ 2 <
      ∑ z ∈ S, ∑ z' ∈ S, corr E c π.w z z' := by
    have hpos : 0 ≤ (S.card : ℝ) * ξ := by positivity
    have hinnerPos : 0 < ∑ y, F y * G y := by linarith [hinner_strict]
    have hsquare : ((S.card : ℝ) * ξ) ^ 2 < (∑ y, F y * G y) ^ 2 :=
      (sq_lt_sq₀ hpos hinnerPos.le).2 hinner_strict
    exact hsquare.trans_le hcs
  have hm : 4 ≤ (S.card : ℝ) * ξ ^ 2 := by
    have hξ : ξ ^ 2 ≠ 0 := pow_ne_zero 2 hξ.ne'
    have hmul' : 4 ≤ (S.card : ℝ) * ξ ^ 2 := by
      calc
        4 = (4 / ξ ^ 2) * ξ ^ 2 := by field_simp [hξ]
        _ ≤ (S.card : ℝ) * ξ ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg ξ)
    exact hmul'
  by_contra hNoPair
  have hnoedge : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → corr E c π.w z z' ≤ 3 * θ := by
    intro z hz z' hz' hne
    exact le_of_not_gt (fun h => hNoPair ⟨z, hz, z', hz', hne, h⟩)
  have hsumUpper : (∑ z ∈ S, ∑ z' ∈ S, corr E c π.w z z') ≤
      (S.card : ℝ) + 3 * θ * (S.card : ℝ) ^ 2 := by
    calc
      (∑ z ∈ S, ∑ z' ∈ S, corr E c π.w z z') ≤
          ∑ z ∈ S, ∑ z' ∈ S, (if z = z' then 1 else 3 * θ) := by
            apply Finset.sum_le_sum
            intro z hz
            apply Finset.sum_le_sum
            intro z' hz'
            by_cases heq : z = z'
            · subst z'
              simpa using corr_diagonal_le_one E c π z
            · simpa [heq] using hnoedge z hz z' hz' heq
      _ ≤ (S.card : ℝ) + 3 * θ * (S.card : ℝ) ^ 2 := by
        have hinnerSum (z : Fin N) :
            (∑ z' ∈ S, if z = z' then 1 else 3 * θ) ≤
              1 + 3 * θ * (S.card : ℝ) := by
          have hdiag : (∑ z' ∈ S, if z = z' then (1 : ℝ) else 0) ≤ 1 := by
            by_cases hz : z ∈ S <;> simp [Finset.sum_ite_eq', eq_comm, hz]
          have hcoeff : 0 ≤ 1 - 3 * θ := by
            have hx2 : ξ ^ 2 < 1 := by nlinarith [hξlt]
            linarith [hθ]
          have hsplit :
              (∑ z' ∈ S, if z = z' then 1 else 3 * θ) =
                3 * θ * (S.card : ℝ) +
                  (1 - 3 * θ) * (∑ z' ∈ S, if z = z' then 1 else 0) := by
            calc
              (∑ z' ∈ S, if z = z' then 1 else 3 * θ) =
                  ∑ z' ∈ S, (3 * θ + (1 - 3 * θ) *
                    (if z = z' then 1 else 0)) := by
                      apply Finset.sum_congr rfl
                      intro z' hz'
                      by_cases heq : z = z' <;> simp [heq] <;> ring
              _ = 3 * θ * (S.card : ℝ) +
                    (1 - 3 * θ) * (∑ z' ∈ S, if z = z' then 1 else 0) := by
                      simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
                        nsmul_eq_mul, mul_comm]
          rw [hsplit]
          calc
            3 * θ * (S.card : ℝ) +
                (1 - 3 * θ) * (∑ z' ∈ S, if z = z' then 1 else 0) ≤
              3 * θ * (S.card : ℝ) + (1 - 3 * θ) * 1 := by
                exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiag hcoeff)
            _ ≤ 1 + 3 * θ * (S.card : ℝ) := by nlinarith
        calc
          (∑ z ∈ S, ∑ z' ∈ S, (if z = z' then 1 else 3 * θ)) ≤
              ∑ z ∈ S, (1 + 3 * θ * (S.card : ℝ)) :=
            Finset.sum_le_sum fun z hz => hinnerSum z
          _ = (S.card : ℝ) + 3 * θ * (S.card : ℝ) ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
  have hbad : (S.card : ℝ) + 3 * θ * (S.card : ℝ) ^ 2 <
      ((S.card : ℝ) * ξ) ^ 2 := by
    have hSpos : 0 < (S.card : ℝ) := by
      have hpos : 0 < (4 / ξ ^ 2 : ℝ) := by positivity
      exact hpos.trans_le hcard
    have hm2 : 4 * (S.card : ℝ) ≤ (S.card : ℝ) ^ 2 * ξ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hm hSpos.le
      nlinarith [hmul]
    have hθscaled := mul_lt_mul_of_pos_right hθ (sq_pos_of_pos hSpos)
    nlinarith [hθscaled, hm2]
  linarith [hpair, hsumUpper, hbad]

private theorem aligned_side_card_lt {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Law N) (C A : Finset (Fin N)) (x : Fin N) (ξ θ Q σ : ℝ)
    (hξ : 0 < ξ) (hθ : 3 * θ < ξ ^ 2 / 4) (hθpos : 0 < θ) (hξlt : ξ < 1)
    (hQ : 0 ≤ Q) (hσ : σ ^ 2 = 1)
    (hA : A ⊆ C) (halign : ∀ z ∈ A, ξ < σ * corr E c π.w x z)
    (hNo : NoClique E c C π.w θ Q) :
    A.card < Nat.choose
      (Nat.ceil (Real.exp Q) + Nat.ceil (4 / ξ ^ 2) - 2)
      (Nat.ceil (Real.exp Q) - 1) := by
  classical
  let q := Nat.ceil (Real.exp Q)
  let t := Nat.ceil (4 / ξ ^ 2)
  let B := Nat.choose (q + t - 2) (q - 1)
  by_contra hlt
  have hltB : ¬ A.card < B := by simpa [B, q, t] using hlt
  have hB : B ≤ A.card := Nat.le_of_not_gt hltB
  let V := {z : Fin N // z ∈ A}
  let G : SimpleGraph V := {
    Adj := fun (a b : V) => a.1 ≠ b.1 ∧ 3 * θ < corr E c π.w a.1 b.1
    symm := ⟨fun a b hab => by
      rcases hab with ⟨hne, hcorr⟩
      refine ⟨hne.symm, ?_⟩
      simpa [corr_symmetric E c π.w] using hcorr⟩
    loopless := ⟨fun a ha => ha.1 rfl⟩ }
  have hqpos : 1 ≤ q := by
    have hq : (1 : ℝ) ≤ (q : ℝ) := by
      calc
        1 ≤ Real.exp Q := Real.one_le_exp hQ
        _ ≤ q := Nat.le_ceil _
    exact_mod_cast hq
  have htpos : 1 ≤ t := by
    have hval : 0 < 4 / ξ ^ 2 := by positivity
    have ht : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (Nat.ceil_pos.mpr hval)
    exact_mod_cast (show (1 : ℝ) ≤ (t : ℝ) by exact_mod_cast ht)
  have hRamCard : B ≤ Fintype.card V := by
    simpa [B, V] using hB
  have hRam := HypercubeRamsey.xRamseyBinom G q t hqpos htpos hRamCard
  rcases hRam with hclique | hindep
  · rcases hclique with ⟨D, hDcard, hDadj⟩
    let Dval := D.image Subtype.val
    have hDval_card : Dval.card = q := by
      dsimp [Dval]
      rw [Finset.card_image_of_injective _ Subtype.val_injective, hDcard]
    have hDval_sub : Dval ⊆ C := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
      exact hA a.2
    have hDval_clique : ∀ u ∈ Dval, ∀ v ∈ Dval, u ≠ v →
        3 * θ < corr E c π.w u v := by
      intro u hu v hv huv
      rcases Finset.mem_image.mp hu with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
      have hab : a ≠ b := by
        intro he
        exact huv (congrArg Subtype.val he)
      exact (hDadj a ha b hb hab).2
    exact hNo ⟨Dval, hDval_sub, hDval_card, hDval_clique⟩
  · rcases hindep with ⟨I, hIcard, hIindep⟩
    let Ival := I.image Subtype.val
    have hIval_card : Ival.card = t := by
      dsimp [Ival]
      rw [Finset.card_image_of_injective _ Subtype.val_injective, hIcard]
    have hIval_sub : Ival ⊆ A := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
      exact a.2
    have hIval_size : (4 / ξ ^ 2 : ℝ) ≤ (Ival.card : ℝ) := by
      rw [hIval_card]
      exact Nat.le_ceil _
    have hpair := correlation_pair_in_large_aligned_set E c π ξ θ σ hξ hθ
      hθpos hξlt hσ x Ival hIval_size (fun z hz => halign z (hIval_sub hz))
    rcases hpair with ⟨u, hu, v, hv, huv, hcorr⟩
    rcases Finset.mem_image.mp hu with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
    have hab : a ≠ b := by
      intro he
      exact huv (congrArg Subtype.val he)
    have hadj : G.Adj a b := ⟨huv, hcorr⟩
    exact (hIindep a ha b hb hab) hadj

theorem correlation_conflict_card_bound {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (π : Law N) (C : Finset (Fin N)) (x : Fin N) (ξ θ Q : ℝ)
    (hξ : 0 < ξ) (hθ : 3 * θ < ξ ^ 2 / 4) (hθpos : 0 < θ) (hξlt : ξ < 1)
    (hQ : 0 ≤ Q) (hNo : NoClique E c C π.w θ Q) :
    (C.filter fun z => ξ < |corr E c π.w x z|).card ≤
      2 * Nat.choose (Nat.ceil (Real.exp Q) + Nat.ceil (4 / ξ ^ 2) - 2)
        (Nat.ceil (Real.exp Q) - 1) := by
  classical
  let q := Nat.ceil (Real.exp Q)
  let t := Nat.ceil (4 / ξ ^ 2)
  let B := Nat.choose (q + t - 2) (q - 1)
  let H := C.filter fun z => ξ < |corr E c π.w x z|
  let Pos := H.filter fun z => ξ < corr E c π.w x z
  let Neg := H.filter fun z => corr E c π.w x z < -ξ
  have hpartition : H = Pos ∪ Neg := by
    ext z
    simp only [H, Pos, Neg, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hz, habs⟩
      by_cases hpos : ξ < corr E c π.w x z
      · exact Or.inl ⟨⟨hz, habs⟩, hpos⟩
      · have hnonpos : corr E c π.w x z ≤ ξ := le_of_not_gt hpos
        have hneg0 : corr E c π.w x z < 0 := by
          by_contra hn
          have habs' := habs
          rw [abs_of_nonneg (le_of_not_gt hn)] at habs'
          linarith
        have hneg : corr E c π.w x z < -ξ := by
          rw [abs_of_neg hneg0] at habs
          linarith
        exact Or.inr ⟨⟨hz, habs⟩, hneg⟩
    · rintro (⟨⟨hz, habs⟩, hpos⟩ | ⟨⟨hz, habs⟩, hneg⟩)
      · exact ⟨hz, habs⟩
      · have hneg0 : corr E c π.w x z < 0 := lt_trans hneg (by linarith)
        rw [abs_of_neg hneg0]
        exact ⟨hz, by linarith⟩
  have hdisjoint : Disjoint Pos Neg := by
    apply Finset.disjoint_left.mpr
    intro z hzP hzN
    have hpos := (Finset.mem_filter.mp hzP).2
    have hneg := (Finset.mem_filter.mp hzN).2
    linarith
  have hcard : H.card = Pos.card + Neg.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisjoint]
  have hPosSub : Pos ⊆ C := by
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  have hPosAlign : ∀ z ∈ Pos, ξ < (1 : ℝ) * corr E c π.w x z := by
    intro z hz
    simpa only [one_mul] using (Finset.mem_filter.mp hz).2
  have hNegSub : Neg ⊆ C := by
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  have hNegAlign : ∀ z ∈ Neg, ξ < (-1 : ℝ) * corr E c π.w x z := by
    intro z hz
    have h := (Finset.mem_filter.mp hz).2
    nlinarith [h]
  have hPos := aligned_side_card_lt E c π C Pos x ξ θ Q 1 hξ hθ hθpos hξlt hQ
    (by ring) hPosSub hPosAlign hNo
  have hNeg := aligned_side_card_lt E c π C Neg x ξ θ Q (-1) hξ hθ hθpos hξlt hQ
    (by ring) hNegSub hNegAlign hNo
  change H.card ≤ 2 * B
  change Pos.card < B at hPos
  change Neg.card < B at hNeg
  omega

private theorem Cstar_ge_four_ceil {u : ℕ} {ξ : ℝ} (hξ : 0 < ξ) (hξlt : ξ < 1) :
    4 * (Nat.ceil (4 / ξ ^ 2) : ℝ) ≤ Cstar u ξ := by
  let A := ⌊(4 : ℝ) ^ (u + 3) / ξ ^ 2⌋₊
  have hpow : (64 : ℝ) ≤ (4 : ℝ) ^ (u + 3) := by
    have hu : 3 ≤ u + 3 := by omega
    have hbase : (1 : ℝ) ≤ 4 := by norm_num
    calc
      (64 : ℝ) = 4 ^ (3 : ℕ) := by norm_num
      _ ≤ 4 ^ (u + 3) := by gcongr
  have hfrac : 64 / ξ ^ 2 ≤ (4 : ℝ) ^ (u + 3) / ξ ^ 2 :=
    div_le_div_of_nonneg_right hpow (by positivity)
  have hfloor : 64 / ξ ^ 2 - 1 < (A : ℝ) := by
    exact lt_of_le_of_lt (sub_le_sub_right hfrac 1) (Nat.sub_one_lt_floor _)
  have hceil : (Nat.ceil (4 / ξ ^ 2) : ℝ) < 4 / ξ ^ 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hxi2 : ξ ^ 2 < 1 := by nlinarith
  have hinv : 1 < 1 / ξ ^ 2 := by
    simpa using (one_div_lt_one_div (by norm_num : (0 : ℝ) < 1)
      (sq_pos_of_pos hξ)).2 hxi2
  let r := 1 / ξ ^ 2
  have hfloor' : 64 * r - 1 < (A : ℝ) := by
    dsimp [r]
    have hh := hfloor
    rw [div_eq_mul_inv] at hh
    simpa only [one_div] using hh
  have hceil' : (Nat.ceil (4 / ξ ^ 2) : ℝ) < 4 * r + 1 := by
    simpa [r, div_eq_mul_inv] using hceil
  have hbase : 4 * (Nat.ceil (4 / ξ ^ 2) : ℝ) < 2 * (A : ℝ) := by
    nlinarith [hfloor', hceil', hinv]
  have hCstar : 2 * (A : ℝ) ≤ Cstar u ξ := by
    have hA0 : 0 ≤ (A : ℝ) := Nat.cast_nonneg _
    have hu0 : 0 ≤ (u : ℝ) := Nat.cast_nonneg _
    dsimp [Cstar, A]
    nlinarith [hA0, hu0]
  exact hbase.le.trans hCstar

private theorem choose_ramsey_le_exp {u : ℕ} {ξ Q : ℝ}
    (hξ : 0 < ξ) (hξlt : ξ < 1) (hQ : 1 ≤ Q) :
    (Nat.choose (Nat.ceil (Real.exp Q) + Nat.ceil (4 / ξ ^ 2) - 2)
      (Nat.ceil (Real.exp Q) - 1) : ℝ) ≤ Real.exp (Cstar u ξ * Q) := by
  let q := Nat.ceil (Real.exp Q)
  let t := Nat.ceil (4 / ξ ^ 2)
  let n := q + t - 2
  have hq : (q : ℝ) ≤ 2 * Real.exp Q := by
    have hceil := Nat.ceil_lt_add_one (Real.exp_nonneg Q)
    have hexp := Real.one_le_exp (by linarith : 0 ≤ Q)
    dsimp [q]
    linarith
  have htpos : 1 ≤ t := by
    have hpos : (0 : ℝ) < 4 / ξ ^ 2 := by positivity
    have hnat : 0 < Nat.ceil (4 / ξ ^ 2) := Nat.ceil_pos.mpr hpos
    dsimp [t]
    omega
  have hCstar := Cstar_ge_four_ceil (u := u) hξ hξlt
  have hCstar' : 4 * (t : ℝ) ≤ Cstar u ξ := by simpa [t] using hCstar
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by
    apply Real.le_exp_of_log_le
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    nlinarith [hlog]
  have hfourpow : (4 : ℝ) ^ t ≤ Real.exp (3 * (t : ℝ)) := by
    calc
      (4 : ℝ) ^ t ≤ (Real.exp 3) ^ t := by gcongr
      _ = Real.exp (3 * (t : ℝ)) := by rw [← Real.exp_nat_mul]; ring
  have hExpMonotone : ∀ a b : ℝ, a ≤ b → Real.exp a ≤ Real.exp b :=
    fun a b hab => Real.exp_le_exp.mpr hab
  by_cases hqt : t ≤ q
  · have hSym : Nat.choose (n) (q - 1) = Nat.choose n (t - 1) := by
      have hqle : q - 1 ≤ n := by dsimp [n]; omega
      have hs := Nat.choose_symm hqle
      have hsub : n - (q - 1) = t - 1 := by dsimp [n]; omega
      rw [hsub] at hs
      exact hs.symm
    have hchooseNat : Nat.choose n (t - 1) ≤ n ^ (t - 1) := Nat.choose_le_pow _ _
    have hnle : n ≤ 2 * q := by dsimp [n]; omega
    have hnReal : (n : ℝ) ≤ 4 * Real.exp Q := by
      have hcast : (2 * q : ℕ) = 2 * q := rfl
      calc
        (n : ℝ) ≤ (2 * q : ℝ) := by exact_mod_cast hnle
        _ = 2 * (q : ℝ) := by norm_num
        _ ≤ 4 * Real.exp Q := by nlinarith [hq]
    have hpow : (n : ℝ) ^ (t - 1) ≤ (4 * Real.exp Q) ^ t := by
      calc
        (n : ℝ) ^ (t - 1) ≤ (4 * Real.exp Q) ^ (t - 1) := by gcongr
        _ ≤ (4 * Real.exp Q) ^ t := by
          have hbase : 1 ≤ 4 * Real.exp Q := by
            have hexp : 1 ≤ Real.exp Q := Real.one_le_exp (by linarith [hQ])
            nlinarith
          apply pow_le_pow_right₀ hbase
          omega
    have hcastChoose :
        (Nat.choose n (t - 1) : ℝ) ≤ (n : ℝ) ^ (t - 1) := by exact_mod_cast hchooseNat
    have hfinal : (4 * Real.exp Q) ^ t ≤ Real.exp (Cstar u ξ * Q) := by
      calc
        (4 * Real.exp Q) ^ t = (4 : ℝ) ^ t * (Real.exp Q) ^ t := by ring
        _ ≤ Real.exp (3 * (t : ℝ)) * Real.exp (Q * (t : ℝ)) := by
          have hpowExp : (Real.exp Q) ^ t = Real.exp (Q * (t : ℝ)) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
          rw [hpowExp]
          exact mul_le_mul_of_nonneg_right hfourpow (by positivity)
        _ = Real.exp ((3 + Q) * (t : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (Cstar u ξ * Q) := by
          apply hExpMonotone
          have h : (3 + Q) * (t : ℝ) ≤ 4 * (t : ℝ) * Q := by nlinarith [hQ]
          exact h.trans (mul_le_mul_of_nonneg_right hCstar' (by linarith [hQ]))
    rw [hSym]
    exact hcastChoose.trans (hpow.trans hfinal)
  · have hq_lt : q < t := by omega
    have hnle : n ≤ 2 * t := by dsimp [n]; omega
    have hchooseNat : Nat.choose n (q - 1) ≤ 2 ^ n := Nat.choose_le_two_pow _ _
    have hcastChoose : (Nat.choose n (q - 1) : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hchooseNat
    have hpow : (2 : ℝ) ^ n ≤ (4 : ℝ) ^ t := by
      have hnat : 2 ^ n ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) hnle
      exact_mod_cast (by simpa [pow_mul] using hnat)
    have hfinal : (4 : ℝ) ^ t ≤ Real.exp (Cstar u ξ * Q) := by
      calc
        (4 : ℝ) ^ t ≤ Real.exp (3 * (t : ℝ)) := hfourpow
        _ ≤ Real.exp (Cstar u ξ * Q) := by
          apply hExpMonotone
          have h : 3 * (t : ℝ) ≤ 4 * (t : ℝ) * Q := by nlinarith [hQ]
          exact h.trans (mul_le_mul_of_nonneg_right hCstar' (by linarith [hQ]))
    simpa [q, t, n] using hcastChoose.trans (hpow.trans hfinal)

theorem correlation_conflict_bound_exp {u N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (π : Law N) (C : Finset (Fin N)) (x : Fin N)
    (ξ θ Q K16 : ℝ) (hξ : 0 < ξ) (hθ : 3 * θ < ξ ^ 2 / 4)
    (hθpos : 0 < θ) (hξlt : ξ < 1) (hQ : 1 ≤ Q) (hK : 2 ≤ K16)
    (hNo : NoClique E c C π.w θ Q) :
    ((C.filter fun z => ξ < |corr E c π.w x z|).card : ℝ) ≤
      K16 * Real.exp (Cstar u ξ * Q) := by
  have hcount := correlation_conflict_card_bound E c π C x ξ θ Q
    hξ hθ hθpos hξlt (by linarith [hQ]) hNo
  have hcast : ((C.filter fun z => ξ < |corr E c π.w x z|).card : ℝ) ≤
      2 * (Nat.choose (Nat.ceil (Real.exp Q) + Nat.ceil (4 / ξ ^ 2) - 2)
        (Nat.ceil (Real.exp Q) - 1) : ℝ) := by exact_mod_cast hcount
  have hchoose := choose_ramsey_le_exp (u := u) hξ hξlt hQ
  have hexp : 0 ≤ Real.exp (Cstar u ξ * Q) := (Real.exp_pos _).le
  calc
    ((C.filter fun z => ξ < |corr E c π.w x z|).card : ℝ) ≤
        2 * (Nat.choose (Nat.ceil (Real.exp Q) + Nat.ceil (4 / ξ ^ 2) - 2)
          (Nat.ceil (Real.exp Q) - 1) : ℝ) := hcast
    _ ≤ K16 * Real.exp (Cstar u ξ * Q) := by
      exact mul_le_mul hK hchoose (by positivity) (by linarith)

private theorem logNatCast_tendsto (T : Stage) :
    Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
      T.S.n_tendsto)

theorem eventually_log_power_dominates (T : Stage) (a b C : ℝ)
    (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ k in atTop,
      C * Real.rpow (Real.log (T.S.n k : ℝ)) a ≤
        Real.rpow (Real.log (T.S.n k : ℝ)) b := by
  have hlog := logNatCast_tendsto T
  have hgap := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp hlog
  filter_upwards [hgap.eventually_ge_atTop C,
    hlog.eventually_ge_atTop (1 : ℝ)] with k hC hL
  have hLpos : 0 < Real.log (T.S.n k : ℝ) := by linarith
  calc
    C * Real.rpow (Real.log (T.S.n k : ℝ)) a ≤
        Real.rpow (Real.log (T.S.n k : ℝ)) (b - a) *
          Real.rpow (Real.log (T.S.n k : ℝ)) a :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by linarith) a)
    _ = Real.rpow (Real.log (T.S.n k : ℝ)) b := by
      calc
        Real.rpow (Real.log (T.S.n k : ℝ)) (b - a) *
            Real.rpow (Real.log (T.S.n k : ℝ)) a =
          Real.rpow (Real.log (T.S.n k : ℝ)) ((b - a) + a) :=
            (Real.rpow_add hLpos (b - a) a).symm
        _ = Real.rpow (Real.log (T.S.n k : ℝ)) b := by congr 1; ring

private theorem log_ratio_bound_of_mass_lower {N M : ℕ} {s : ℝ}
    (hN : 0 < (N : ℝ)) (hM : 0 < (M : ℝ))
    (hmass : (N : ℝ) / 400 * Real.exp (-s) ≤ M) :
    Real.log ((N : ℝ) / M) ≤ Real.log 400 + s := by
  have hratio : (N : ℝ) / M ≤ 400 * Real.exp s := by
    apply (div_le_iff₀ hM).2
    calc
      (N : ℝ) = ((N : ℝ) / 400 * Real.exp (-s)) * (400 * Real.exp s) := by
        rw [Real.exp_neg]
        field_simp [ne_of_gt hN]
      _ ≤ (M : ℝ) * (400 * Real.exp s) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = 400 * Real.exp s * (M : ℝ) := by ring
  calc
    Real.log ((N : ℝ) / M) ≤ Real.log (400 * Real.exp s) :=
      Real.log_le_log (div_pos hN hM) hratio
    _ = Real.log 400 + s := by
      rw [Real.log_mul (by norm_num : (400 : ℝ) ≠ 0) (Real.exp_ne_zero _)]
      simp

private theorem low_patch_log_ratio_bounds {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    (PT.tiling.mode = .bounded →
      Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ Real.log 400) ∧
    (PT.tiling.mode = .lowDirect →
      Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤
        Real.log 400 + (PT.tiling.P i).g ^ κ.aB) ∧
    (PT.tiling.mode = .lowCluster →
      Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤
        Real.log 400 + (PT.tiling.P i).q ^ κ.aC) := by
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hMnat : 0 < (PT.tiling.P i).M := by
    have hY := (hPT.tiling_valid.patch_nonempty i).2
    have hc := Finset.card_pos.mpr hY
    rw [(PT.tiling.P i).cardY] at hc
    exact hc
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by exact_mod_cast hMnat
  refine ⟨?_, ?_, ?_⟩
  · intro hm
    obtain ⟨_, hdata⟩ := hPT.tiling_valid.bounded_data hm
    obtain ⟨_, _, _, hmass, _⟩ := hdata i
    have hmass' : (T.S.N k : ℝ) / 400 * Real.exp (-(0 : ℝ)) ≤
        ((PT.tiling.P i).M : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmass
    simpa using log_ratio_bound_of_mass_lower hN hM hmass'
  · intro hm
    obtain ⟨_, _, hmass, _, _, _, _⟩ :=
      hPT.tiling_valid.direct_data (Or.inl hm) i
    exact log_ratio_bound_of_mass_lower hN hM
      (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmass)
  · intro hm
    obtain ⟨_, _, hmass, _, _, _, _, _, _, _, _, _⟩ :=
      hPT.tiling_valid.cluster_data (Or.inl hm) i
    exact log_ratio_bound_of_mass_lower hN hM
      (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmass)

private theorem patch_prefix_le_of_log_mass {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : 𝒯.Valid) (i : Fin 𝒯.m)
    (hmass : Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤
      (Real.log 2 / 2) * Real.sqrt (Real.log (T.S.n k : ℝ)))
    (hn : 2 ≤ T.S.n k) : ((𝒯.P i).ℓ : ℝ) ≤ Real.sqrt (Real.log (T.S.n k : ℝ)) := by
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hS : 0 < (𝒯.S : ℝ) := by
    have h := h𝒯.S_lower
    have hN' : 0 < (T.S.N k : ℝ) := hN
    nlinarith
  have hM : 0 < ((𝒯.P i).M : ℝ) := by
    have hY := Finset.card_pos.mpr (h𝒯.patch_nonempty i).2
    rw [(𝒯.P i).cardY] at hY
    exact_mod_cast hY
  have hdyad : (𝒯.P i).M / (𝒯.S : ℝ) ≤
      Real.rpow 2 (-((𝒯.P i).ℓ : ℝ)) := by
    simpa [Real.rpow_intCast] using h𝒯.dyadic_mass_lower i
  have hpow : Real.rpow 2 ((𝒯.P i).ℓ : ℝ) ≤ (𝒯.S : ℝ) / (𝒯.P i).M := by
    have hmul := (div_le_iff₀ hS).mp hdyad
    have hmul' : (𝒯.P i).M * Real.rpow 2 ((𝒯.P i).ℓ : ℝ) ≤ 𝒯.S := by
      calc
        (𝒯.P i).M * Real.rpow 2 ((𝒯.P i).ℓ : ℝ) ≤
            (Real.rpow 2 (-((𝒯.P i).ℓ : ℝ)) * (𝒯.S : ℝ)) *
              Real.rpow 2 ((𝒯.P i).ℓ : ℝ) :=
          mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg (by norm_num) _)
        _ = 𝒯.S := by
          rw [mul_assoc]
          have hexp : Real.rpow 2 (-((𝒯.P i).ℓ : ℝ)) *
              Real.rpow 2 ((𝒯.P i).ℓ : ℝ) = 1 := by
            change (2 : ℝ) ^ (-((𝒯.P i).ℓ : ℝ)) *
              (2 : ℝ) ^ ((𝒯.P i).ℓ : ℝ) = 1
            rw [Real.rpow_neg (by norm_num) ((𝒯.P i).ℓ : ℝ)]
            exact inv_mul_cancel₀ (ne_of_gt
              (Real.rpow_pos_of_pos (by norm_num) ((𝒯.P i).ℓ : ℝ)))
          calc
            Real.rpow 2 (-((𝒯.P i).ℓ : ℝ)) *
                ((𝒯.S : ℝ) * Real.rpow 2 ((𝒯.P i).ℓ : ℝ)) =
              (𝒯.S : ℝ) * (Real.rpow 2 (-((𝒯.P i).ℓ : ℝ)) *
                Real.rpow 2 ((𝒯.P i).ℓ : ℝ)) := by ring
            _ = 𝒯.S := by rw [hexp]; ring
    have hmul'' : Real.rpow 2 ((𝒯.P i).ℓ : ℝ) *
        ((𝒯.P i).M : ℝ) ≤ (𝒯.S : ℝ) := by simpa [mul_comm] using hmul'
    exact (le_div_iff₀ hM).2 hmul''
  have hlogPow : ((𝒯.P i).ℓ : ℝ) * Real.log 2 ≤
      Real.log ((𝒯.S : ℝ) / (𝒯.P i).M) := by
    have hpos : 0 < Real.rpow 2 ((𝒯.P i).ℓ : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hlog := Real.log_le_log hpos hpow
    simpa [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] using hlog
  have hSratio : (𝒯.S : ℝ) / (𝒯.P i).M ≤
      (T.S.N k : ℝ) / (𝒯.P i).M :=
    div_le_div_of_nonneg_right (by exact_mod_cast h𝒯.S_upper) (by positivity)
  have hlogRatio := Real.log_le_log (div_pos hS hM) hSratio
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlogn : 0 ≤ Real.log (T.S.n k : ℝ) := by
    have hnR : (2 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hn
    exact Real.log_nonneg (by linarith)
  have hsqrt : 0 ≤ Real.sqrt (Real.log (T.S.n k : ℝ)) := Real.sqrt_nonneg _
  have hsmall := hlogPow.trans (hlogRatio.trans hmass)
  nlinarith [hsmall, hlog2, hsqrt]

structure LowInputScaleEvents (κ : CConsts) (T : Stage) (k : ℕ)
    (K16 : ℝ) : Prop where
  n_large : 2 ≤ T.S.n k
  log_large : 1 ≤ Real.log (T.S.n k : ℝ)
  cluster_height : 2 * Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Mlo) ≤
    Real.rpow (Real.log (T.S.n k : ℝ)) (1 / 10 : ℝ)
  cluster_bin : Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq ≤
    Real.sqrt (Real.log (T.S.n k : ℝ))
  mass_constant : Real.log 400 ≤ (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ))
  mass_cluster : Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.aC) ≤
    (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ))
  mass_direct : Real.rpow (κ.KB * Real.log (T.S.n k : ℝ)) κ.aB ≤
    (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ))
  interaction_cluster : 2 * Cstar κ.u κ.ξ *
      Real.rpow (Real.log (T.S.n k : ℝ)) (2 * κ.cq) ≤
        κ.KB * Real.log (T.S.n k : ℝ)
  degree_cluster : 10 * Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) ≤
    K16 * Real.log (T.S.n k : ℝ)
  interaction_bounded : Cstar κ.u κ.ξ * κ.Qbd ≤ κ.KB * Real.log (T.S.n k : ℝ)

theorem eventually_low_input_scale_events {κ : CConsts} (hκ : CConsts.Admissible κ)
    (T : Stage) (K16 : ℝ) (hKB : 0 < κ.KB)
    (hK16one : 1 ≤ K16) :
    ∀ᶠ k in atTop, LowInputScaleEvents κ T k K16 := by
  have hlog := logNatCast_tendsto T
  have hNlarge : ∀ᶠ k in atTop, 2 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 2
  have hlogLarge : ∀ᶠ k in atTop, 1 ≤ Real.log (T.S.n k : ℝ) :=
    hlog.eventually_ge_atTop 1
  have hCbpos : 100 < κ.Cb := by
    have hr : 0 ≤ 100 * κ.aC / κ.aB :=
      div_nonneg (mul_nonneg (by norm_num) hκ.aC_rng.1.le) hκ.aB_rng.1.le
    have hle : 100 ≤ 100 * κ.aC / κ.aB + 100 := by linarith
    exact lt_of_le_of_lt hle hκ.Cb_big
  have hMlo : 100 < (κ.Mlo : ℝ) := by linarith [hκ.Mlo_big, hCbpos]
  have hMloPos : 0 < (κ.Mlo : ℝ) := by linarith
  have hcqM : κ.cq * (κ.Mlo : ℝ) < 1 / 20 := by
    have hmul := mul_lt_mul_of_pos_right hκ.cq_rng.2 hMloPos
    have heq : (1 / (20 * (κ.Mlo : ℝ))) * (κ.Mlo : ℝ) = 1 / 20 := by
      field_simp [ne_of_gt hMloPos]
    nlinarith [hmul, heq]
  have hCbMlo : κ.Cb < (κ.Mlo : ℝ) := by linarith [hκ.Mlo_big]
  have hcqCb : κ.cq * κ.Cb < 1 / 20 := by
    have hmul := mul_lt_mul_of_pos_left hCbMlo hκ.cq_rng.1
    linarith [hcqM]
  have hcqSmall : 2 * κ.cq < 1 := by
    have hmul := mul_lt_mul_of_pos_right hκ.cq_rng.2 hMloPos
    have heq : (1 / (20 * (κ.Mlo : ℝ))) * (κ.Mlo : ℝ) = 1 / 20 := by
      field_simp [ne_of_gt hMloPos]
    nlinarith [hmul, heq]
  have hmassClusterExp : κ.cq * κ.aC < 1 / 4 := by
    have hmin : min κ.η0 1 ≤ 1 := min_le_right _ _
    have haC : κ.aC < 1 / 10 ^ 6 := by
      apply lt_of_lt_of_le hκ.aC_rng.2
      exact div_le_div_of_nonneg_right hmin (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
    have hmul := mul_lt_mul_of_pos_left haC hκ.cq_rng.1
    have hcqSmall' : κ.cq < 1 / 2000 := by
      have hmul' := mul_lt_mul_of_pos_right hκ.cq_rng.2 hMloPos
      have heq : (1 / (20 * (κ.Mlo : ℝ))) * (κ.Mlo : ℝ) = 1 / 20 := by
        field_simp [ne_of_gt hMloPos]
      nlinarith [hmul', heq, hMlo]
    nlinarith [hmul, hcqSmall']
  have haBhalf : κ.aB < 1 / 2 := by
    have haC : κ.aC < 1 / 10 ^ 6 := by
      exact lt_of_lt_of_le hκ.aC_rng.2
        (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 10 ^ 6))
    exact lt_trans hκ.aB_rng.2.1 (by nlinarith [haC])
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCstarPos : 0 < Cstar κ.u κ.ξ := by
    unfold Cstar
    positivity
  have hMassConstCoeff : 0 < 8 * Real.log 400 / Real.log 2 := by
    have hlog400 : 0 < Real.log 400 := Real.log_pos (by norm_num)
    exact div_pos (mul_pos (by norm_num) hlog400) hlog2
  have hMassClusterCoeff : 0 < 8 / Real.log 2 := by positivity
  have hMassDirectCoeff : 0 < 8 * Real.rpow κ.KB κ.aB / Real.log 2 := by
    exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hKB _)) hlog2
  have hBoundIntCoeff : 0 ≤ Cstar κ.u κ.ξ * κ.Qbd / κ.KB := by positivity
  have hHeight := eventually_log_power_dominates T (κ.cq * κ.Mlo) (1 / 10 : ℝ) 2
    (mul_nonneg hκ.cq_rng.1.le hMloPos.le) (by linarith [hcqM])
  have hcqHalf : κ.cq < 1 / 2 := by linarith [hcqSmall]
  have hBin := eventually_log_power_dominates T κ.cq (1 / 2 : ℝ) 1
    hκ.cq_rng.1.le hcqHalf
  have hMassConst := eventually_log_power_dominates T 0 (1 / 2 : ℝ)
    (8 * Real.log 400 / Real.log 2) (by norm_num) (by norm_num)
  have hMassCluster := eventually_log_power_dominates T (κ.cq * κ.aC) (1 / 2 : ℝ)
    (8 / Real.log 2) (mul_nonneg hκ.cq_rng.1.le hκ.aC_rng.1.le)
    (by linarith [hmassClusterExp])
  have hMassDirect := eventually_log_power_dominates T κ.aB (1 / 2 : ℝ)
    (8 * Real.rpow κ.KB κ.aB / Real.log 2) hκ.aB_rng.1.le haBhalf
  have hIntCluster := eventually_log_power_dominates T (2 * κ.cq) 1
    (2 * Cstar κ.u κ.ξ) (mul_nonneg (by norm_num) hκ.cq_rng.1.le)
    (by linarith [hcqSmall])
  have hDegreeCluster := eventually_log_power_dominates T (κ.cq * κ.Cb) 1
    10 (mul_nonneg hκ.cq_rng.1.le (le_of_lt (by linarith [hCbpos])))
    (by linarith [hcqCb])
  have hIntBounded := eventually_log_power_dominates T 0 1
    (Cstar κ.u κ.ξ * κ.Qbd / κ.KB) (by norm_num) (by norm_num)
  filter_upwards [hNlarge, hlogLarge, hHeight, hBin, hMassConst, hMassCluster,
    hMassDirect, hIntCluster, hDegreeCluster, hIntBounded] with k hn hL hheight hbin
      hmassC hmassCl hmassD hIC hDC hIB
  have hbin' : Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq ≤
      Real.sqrt (Real.log (T.S.n k : ℝ)) := by
    simpa [Real.sqrt_eq_rpow] using hbin
  have hmassConstant : Real.log 400 ≤ (Real.log 2 / 8) *
      Real.sqrt (Real.log (T.S.n k : ℝ)) := by
    have h : 8 * Real.log 400 / Real.log 2 ≤
        Real.sqrt (Real.log (T.S.n k : ℝ)) := by
      simpa [Real.sqrt_eq_rpow] using hmassC
    have hcoeff : 0 < Real.log 2 / 8 := by positivity
    have heq : (Real.log 2 / 8) * (8 * Real.log 400 / Real.log 2) = Real.log 400 := by
      field_simp [ne_of_gt hlog2]
    calc
      Real.log 400 = (Real.log 2 / 8) * (8 * Real.log 400 / Real.log 2) := heq.symm
      _ ≤ (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) :=
        mul_le_mul_of_nonneg_left h hcoeff.le
  have hmassCluster : Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.aC) ≤
      (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) := by
    let A : ℝ := Real.log 2 / 8
    let B : ℝ := 8 / Real.log 2
    let X : ℝ := Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.aC)
    let Y : ℝ := Real.sqrt (Real.log (T.S.n k : ℝ))
    have h : (8 / Real.log 2) * Real.rpow (Real.log (T.S.n k : ℝ))
        (κ.cq * κ.aC) ≤ Real.sqrt (Real.log (T.S.n k : ℝ)) := by
      simpa [Real.sqrt_eq_rpow] using hmassCl
    have hcoeff : 0 < A := by dsimp [A]; positivity
    have heq : A * B = 1 := by
      change (Real.log 2 / 8) * (8 / Real.log 2) = 1
      field_simp [ne_of_gt hlog2]
    have h' : B * X ≤ Y := by
      simpa [B, X, Y] using h
    calc
      X = (A * B) * X := by rw [heq]; ring
      _ = A * (B * X) := by ring
      _ ≤ A * Y := by exact mul_le_mul_of_nonneg_left h' hcoeff.le
      _ = (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) := rfl
  have hmassDirect : Real.rpow (κ.KB * Real.log (T.S.n k : ℝ)) κ.aB ≤
      (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) := by
    have h : (8 * Real.rpow κ.KB κ.aB / Real.log 2) *
        Real.rpow (Real.log (T.S.n k : ℝ)) κ.aB ≤
          Real.sqrt (Real.log (T.S.n k : ℝ)) := by
      simpa [Real.sqrt_eq_rpow] using hmassD
    have hcoeff : 0 < Real.log 2 / 8 := by positivity
    have heq : (Real.log 2 / 8) *
        (8 * Real.rpow κ.KB κ.aB / Real.log 2) = Real.rpow κ.KB κ.aB := by
      field_simp [ne_of_gt hlog2]
    have hLpos : 0 < Real.log (T.S.n k : ℝ) := by linarith
    have hmul : Real.rpow (κ.KB * Real.log (T.S.n k : ℝ)) κ.aB =
        Real.rpow κ.KB κ.aB * Real.rpow (Real.log (T.S.n k : ℝ)) κ.aB :=
      Real.mul_rpow hKB.le hLpos.le
    calc
      Real.rpow (κ.KB * Real.log (T.S.n k : ℝ)) κ.aB =
          (Real.log 2 / 8) * ((8 * Real.rpow κ.KB κ.aB / Real.log 2) *
            Real.rpow (Real.log (T.S.n k : ℝ)) κ.aB) := by
        calc
          _ = Real.rpow κ.KB κ.aB * Real.rpow (Real.log (T.S.n k : ℝ)) κ.aB := hmul
          _ = (Real.log 2 / 8 * (8 * Real.rpow κ.KB κ.aB / Real.log 2)) *
              Real.rpow (Real.log (T.S.n k : ℝ)) κ.aB := by rw [heq]
          _ = _ := by ring
      _ ≤ (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) :=
        mul_le_mul_of_nonneg_left h hcoeff.le
  have hKB1 : 1 ≤ κ.KB := by
    have hPbig := hκ.P_big.2
    rw [hκ.Ac_eq] at hPbig
    have hP : 1 ≤ κ.P := by norm_num at hPbig; omega
    have hR : 1 ≤ κ.R := by rw [hκ.R_eq]; nlinarith
    have hRcast : 1 ≤ (κ.R : ℝ) := by exact_mod_cast hR
    nlinarith [hκ.KB_big, hRcast]
  have hclusterInteraction :
      2 * Cstar κ.u κ.ξ * Real.rpow (Real.log (T.S.n k : ℝ)) (2 * κ.cq) ≤
        κ.KB * Real.log (T.S.n k : ℝ) := by
    have hLnonneg : 0 ≤ Real.log (T.S.n k : ℝ) := le_trans (by norm_num) hL
    calc
      2 * Cstar κ.u κ.ξ * Real.rpow (Real.log (T.S.n k : ℝ)) (2 * κ.cq) ≤
          Real.log (T.S.n k : ℝ) := by simpa [Real.rpow_one] using hIC
      _ ≤ κ.KB * Real.log (T.S.n k : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hKB1 hLnonneg
  have hclusterDegree :
      10 * Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) ≤
        K16 * Real.log (T.S.n k : ℝ) := by
    have hLnonneg : 0 ≤ Real.log (T.S.n k : ℝ) := le_trans (by norm_num) hL
    calc
      10 * Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) ≤
          Real.log (T.S.n k : ℝ) := by simpa [Real.rpow_one] using hDC
      _ ≤ K16 * Real.log (T.S.n k : ℝ) :=
        by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK16one hLnonneg
  have hboundedInteraction : Cstar κ.u κ.ξ * κ.Qbd ≤
      κ.KB * Real.log (T.S.n k : ℝ) := by
    have h : Cstar κ.u κ.ξ * κ.Qbd / κ.KB ≤ Real.log (T.S.n k : ℝ) := by
      simpa [Real.rpow_zero, Real.rpow_one] using hIB
    have hmul := (div_le_iff₀ hKB).mp h
    simpa [mul_comm] using hmul
  exact ⟨hn, hL, hheight, hbin', hmassConstant, hmassCluster, hmassDirect,
    hclusterInteraction, hclusterDegree, hboundedInteraction⟩

theorem low_mode_cases {mode : Mode} (h : mode.isLow) :
    mode = .bounded ∨ mode = .lowDirect ∨ mode = .lowCluster := by
  cases mode <;> simp_all [Mode.isLow]

private theorem one_le_of_isDyadic {d : ℕ} (hd : IsDyadic d) : 1 ≤ d := by
  rcases hd with ⟨j, rfl⟩
  exact Nat.one_le_pow j 2 (by decide)

theorem low_mode_quant_facts_of_events {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (hPT : PT.Valid) (hlow : PT.tiling.mode.isLow)
    (hEv : LowInputScaleEvents κ T k K16) (hK16pos : 0 < K16)
    (hK16two : 2 ≤ K16) (hK16Kbd : κ.Kbd ≤ K16)
    (hK16KB : 4 * κ.KB ≤ K16) :
    HypercubeRamsey.S16.LowModeQuantFacts hκ (PT := PT) K16 := by
  have hlogpos : 0 < Real.log (T.S.n k : ℝ) := by linarith [hEv.log_large]
  have hlognonneg : 0 ≤ Real.log (T.S.n k : ℝ) := le_of_lt hlogpos
  have hnpos : 0 < (T.S.n k : ℝ) := by
    have hn : 0 < T.S.n k := lt_of_lt_of_le (by norm_num) hEv.n_large
    exact_mod_cast hn
  have hrootnonneg : 0 ≤ Real.sqrt (Real.log (T.S.n k : ℝ)) := Real.sqrt_nonneg _
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCstarPos : 0 < Cstar κ.u κ.ξ := by
    unfold Cstar
    positivity
  have hCbpos : 100 < κ.Cb := by
    have hr : 0 ≤ 100 * κ.aC / κ.aB :=
      div_nonneg (mul_nonneg (by norm_num) hκ.aC_rng.1.le) hκ.aB_rng.1.le
    have hle : 100 ≤ 100 * κ.aC / κ.aB + 100 := by linarith
    exact lt_of_le_of_lt hle hκ.Cb_big
  have hlog2upper : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith
  have hMassRatio (i : Fin PT.tiling.m) :
      Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤
        (Real.log 2 / 2) * Real.sqrt (Real.log (T.S.n k : ℝ)) := by
    have hrat := low_patch_log_ratio_bounds hPT i
    have hconst : Real.log 400 ≤ (Real.log 2 / 8) *
        Real.sqrt (Real.log (T.S.n k : ℝ)) := hEv.mass_constant
    have hcoef : Real.log 2 / 8 ≤ Real.log 2 / 4 := by nlinarith
    have hconst' : Real.log 400 ≤ (Real.log 2 / 4) *
        Real.sqrt (Real.log (T.S.n k : ℝ)) := by
      exact hconst.trans (mul_le_mul_of_nonneg_right hcoef hrootnonneg)
    have hcoef' : Real.log 2 / 4 ≤ Real.log 2 / 2 := by nlinarith
    have hconst'' : Real.log 400 ≤ (Real.log 2 / 2) *
        Real.sqrt (Real.log (T.S.n k : ℝ)) := by
      exact hconst'.trans (mul_le_mul_of_nonneg_right hcoef' hrootnonneg)
    rcases low_mode_cases hlow with hb | hd | hc
    · exact (hrat.1 hb).trans hconst''
    · have hGain : (PT.tiling.P i).g ≤ κ.KB * Real.log (T.S.n k : ℝ) := by
        rcases hPT.tiling_valid.direct_data (Or.inl hd) i with
          ⟨_, _, _, _, _, _, hhigh⟩
        apply le_of_not_gt
        intro hlt
        exact (by simp [hd] : PT.tiling.mode ≠ .highDirect) (hhigh.mpr hlt)
      have hpow : Real.rpow (PT.tiling.P i).g κ.aB ≤
          Real.rpow (κ.KB * Real.log (T.S.n k : ℝ)) κ.aB :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hGain hκ.aB_rng.1.le
      have hpow' : Real.rpow (PT.tiling.P i).g κ.aB ≤
          (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) :=
        hpow.trans hEv.mass_direct
      have hsum : Real.log 400 + Real.rpow (PT.tiling.P i).g κ.aB ≤
          (Real.log 2 / 4) * Real.sqrt (Real.log (T.S.n k : ℝ)) := by
        calc
          _ ≤ (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) +
              (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) :=
            add_le_add hconst hpow'
          _ = (Real.log 2 / 4) * Real.sqrt (Real.log (T.S.n k : ℝ)) := by ring
      exact (hrat.2.1 hd).trans (hsum.trans (mul_le_mul_of_nonneg_right hcoef' hrootnonneg))
    · rcases hPT.tiling_valid.cluster_data (Or.inl hc) i with
        ⟨_, _, _, _, _, _, _, _, _, hlowq, _, _⟩
      have hqle : (PT.tiling.P i).q ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq := (hlowq.mp hc)
      have hpow : Real.rpow (PT.tiling.P i).q κ.aC ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.aC) := by
        calc
          Real.rpow (PT.tiling.P i).q κ.aC ≤
              Real.rpow (Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq) κ.aC :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hqle hκ.aC_rng.1.le
          _ = Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.aC) :=
            (Real.rpow_mul (x := Real.log (T.S.n k : ℝ)) hlogpos.le κ.cq κ.aC).symm
      have hpow' : Real.rpow (PT.tiling.P i).q κ.aC ≤
          (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) :=
        hpow.trans hEv.mass_cluster
      have hsum : Real.log 400 + Real.rpow (PT.tiling.P i).q κ.aC ≤
          (Real.log 2 / 4) * Real.sqrt (Real.log (T.S.n k : ℝ)) := by
        calc
          _ ≤ (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) +
              (Real.log 2 / 8) * Real.sqrt (Real.log (T.S.n k : ℝ)) :=
            add_le_add hconst hpow'
          _ = (Real.log 2 / 4) * Real.sqrt (Real.log (T.S.n k : ℝ)) := by ring
      exact (hrat.2.2 hc).trans (hsum.trans (mul_le_mul_of_nonneg_right hcoef' hrootnonneg))
  refine {
    profiled_valid := hPT
    mode_low := hlow
    n_large := hEv.n_large
    K16_pos := hK16pos
    height_bound := ?_
    prefix_bound := ?_
    patch_mass_bound := ?_
    bin_count_bound := ?_
    interaction_scale_bound := ?_
    degree_bound := ?_
    conflict_bound := ?_
  }
  · intro i
    rcases low_mode_cases hlow with hb | hd | hc
    · rcases hPT.tiling_valid.bounded_data hb with ⟨_, hdata⟩
      rcases hdata i with ⟨_, hh, _, _, _⟩
      rw [hh]
      simpa using Real.rpow_nonneg hlognonneg (1 / 10 : ℝ)
    · rcases hPT.tiling_valid.direct_data (Or.inl hd) i with
        ⟨_, _, _, _, hh, _, _⟩
      rw [hh]
      simpa using Real.rpow_nonneg hlognonneg (1 / 10 : ℝ)
    · rcases hPT.tiling_valid.cluster_data (Or.inl hc) i with
        ⟨_, _, _, _, _, _, _, _, hupper, hlowq, _, _⟩
      have hqle : (PT.tiling.P i).q ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq := hlowq.mp hc
      have hpow : Real.rpow (PT.tiling.P i).q (κ.Mlo : ℝ) ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Mlo) := by
        calc
          Real.rpow (PT.tiling.P i).q (κ.Mlo : ℝ) ≤
              Real.rpow (Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq) (κ.Mlo : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hqle (by exact_mod_cast Nat.zero_le κ.Mlo)
          _ = Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Mlo) :=
            (Real.rpow_mul (x := Real.log (T.S.n k : ℝ)) hlogpos.le κ.cq (κ.Mlo : ℝ)).symm
      calc
        (PT.tiling.P i).h ≤ 2 * Real.rpow (PT.tiling.P i).q (κ.Mlo : ℝ) := by
          simpa [hc] using hupper.le
        _ ≤ 2 * Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Mlo) :=
          mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ ≤ Real.rpow (Real.log (T.S.n k : ℝ)) (1 / 10 : ℝ) := hEv.cluster_height
  · intro i
    exact patch_prefix_le_of_log_mass hPT.tiling_valid i (hMassRatio i) hEv.n_large
  · intro i
    have hratio := hMassRatio i
    have hcoef : Real.log 2 / 2 ≤ 1 := by linarith [hlog2upper]
    simpa only [one_mul] using hratio.trans
      (mul_le_mul_of_nonneg_right hcoef hrootnonneg)
  · intro i
    rcases low_mode_cases hlow with hb | hd | hc
    · rcases hPT.tiling_valid.bounded_data hb with ⟨_, hdata⟩
      rcases hdata i with ⟨_, _, hd, _, _⟩
      rw [hd]
      have : 0 ≤ Real.sqrt (Real.log (T.S.n k : ℝ)) := hrootnonneg
      exact_mod_cast Real.one_le_exp hrootnonneg
    · rcases hPT.tiling_valid.direct_data (Or.inl hd) i with
        ⟨_, _, _, _, _, hd, _⟩
      rw [hd]
      exact_mod_cast Real.one_le_exp hrootnonneg
    · rcases hPT.tiling_valid.cluster_data (Or.inl hc) i with
        ⟨_, _, _, _, hlowEq, _, _, _, _, _, _, _⟩
      have hd : (PT.tiling.P i).d = ⌊Real.exp ((PT.tiling.P i).q / 2)⌋₊ := by
        exact hlowEq (Or.inl hc)
      rw [hd]
      have hqle : (PT.tiling.P i).q ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq := by
        rcases hPT.tiling_valid.cluster_data (Or.inl hc) i with
          ⟨_, _, _, _, _, _, _, _, _, hlowq, _, _⟩
        exact hlowq.mp hc
      have hqlog : (PT.tiling.P i).q ≤ Real.sqrt (Real.log (T.S.n k : ℝ)) :=
        hqle.trans hEv.cluster_bin
      have hhalf : ((PT.tiling.P i).q : ℝ) / 2 ≤
          Real.sqrt (Real.log (T.S.n k : ℝ)) := by
        have hqnonneg : 0 ≤ ((PT.tiling.P i).q : ℝ) := Nat.cast_nonneg _
        have hhalfq : ((PT.tiling.P i).q : ℝ) / 2 ≤ (PT.tiling.P i).q := by
          nlinarith [hqnonneg]
        exact hhalfq.trans hqlog
      have hfloor : ((⌊Real.exp ((PT.tiling.P i).q / 2)⌋₊ : ℕ) : ℝ) ≤
          Real.exp ((PT.tiling.P i).q / 2) := Nat.floor_le (le_of_lt (Real.exp_pos _))
      exact hfloor.trans (Real.exp_le_exp.mpr hhalf)
  · intro i
    rcases low_mode_cases hlow with hb | hd | hc
    · rcases hPT.tiling_valid.bounded_data hb with ⟨_, hdata⟩
      rcases hdata i with ⟨_, _, _, _, hQ⟩
      simpa [hQ] using hEv.interaction_bounded
    · have hGain : (PT.tiling.P i).g ≤ κ.KB * Real.log (T.S.n k : ℝ) := by
        rcases hPT.tiling_valid.direct_data (Or.inl hd) i with
          ⟨_, _, _, _, _, _, hhigh⟩
        apply le_of_not_gt
        intro hlt
        exact (by simp [hd] : PT.tiling.mode ≠ .highDirect) (hhigh.mpr hlt)
      rcases (hPT.tiling_valid.clique_scales i).2 (Or.inl hd) with
        ⟨_, _, hQ, _⟩
      have hqnonneg : 0 ≤ ((PT.tiling.P i).g : ℝ) := Nat.cast_nonneg _
      have hrootM1 : 0 < Real.sqrt κ.M1 := Real.sqrt_pos.2 (by linarith [hκ.M1_big.1])
      have hfactor : 0 ≤ 2 * Cstar κ.u κ.ξ / Real.sqrt κ.M1 ∧
          2 * Cstar κ.u κ.ξ / Real.sqrt κ.M1 ≤ 1 := by
        constructor
        · positivity
        · exact (hκ.M1_big.2.trans (by norm_num : (1e-4 : ℝ) ≤ 1))
      have hQscaled : Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ) ≤
          Cstar κ.u κ.ξ * (2 * (PT.tiling.P i).g / Real.sqrt κ.M1) :=
        mul_le_mul_of_nonneg_left hQ hCstarPos.le
      have hFactorGain : Cstar κ.u κ.ξ * (2 * (PT.tiling.P i).g /
          Real.sqrt κ.M1) ≤ (PT.tiling.P i).g := by
        have h := mul_le_mul_of_nonneg_right hfactor.2 hqnonneg
        convert h using 1 <;> field_simp [ne_of_gt hrootM1] <;> ring
      calc
        Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ) ≤
            Cstar κ.u κ.ξ * (2 * (PT.tiling.P i).g / Real.sqrt κ.M1) := hQscaled
        _ ≤ (PT.tiling.P i).g := hFactorGain
        _ ≤ κ.KB * Real.log (T.S.n k : ℝ) := hGain
    · rcases (hPT.tiling_valid.clique_scales i).1 (Or.inl hc) with
        ⟨_, hq2, hQ, _⟩
      have hqle : (PT.tiling.P i).q ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq := by
        rcases hPT.tiling_valid.cluster_data (Or.inl hc) i with
          ⟨_, _, _, _, _, _, _, _, _, hlowq, _, _⟩
        exact hlowq.mp hc
      have hqpow : (PT.tiling.P i).q ^ 2 ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) (2 * κ.cq) := by
        have hbase := Real.rpow_le_rpow (Nat.cast_nonneg (PT.tiling.P i).q)
          hqle (by norm_num : 0 ≤ (2 : ℝ))
        calc
          (PT.tiling.P i).q ^ 2 = Real.rpow (PT.tiling.P i).q 2 :=
            (Real.rpow_natCast (PT.tiling.P i).q 2).symm
          _ ≤ Real.rpow (Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq) 2 := hbase
          _ = Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * 2) :=
            (Real.rpow_mul (x := Real.log (T.S.n k : ℝ)) hlogpos.le κ.cq 2).symm
          _ = Real.rpow (Real.log (T.S.n k : ℝ)) (2 * κ.cq) := by congr 1 <;> ring
      calc
        Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ) ≤
            Cstar κ.u κ.ξ * (2 * (PT.tiling.P i).q ^ 2) :=
          mul_le_mul_of_nonneg_left hQ hCstarPos.le
        _ ≤ 2 * Cstar κ.u κ.ξ *
            Real.rpow (Real.log (T.S.n k : ℝ)) (2 * κ.cq) := by
          calc
            Cstar κ.u κ.ξ * (2 * (PT.tiling.P i).q ^ 2) =
                2 * Cstar κ.u κ.ξ * (PT.tiling.P i).q ^ 2 := by ring
            _ ≤ 2 * Cstar κ.u κ.ξ *
                Real.rpow (Real.log (T.S.n k : ℝ)) (2 * κ.cq) :=
              mul_le_mul_of_nonneg_left hqpow
                (mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) hCstarPos.le)
        _ ≤ κ.KB * Real.log (T.S.n k : ℝ) := hEv.interaction_cluster
  · intro i x hx
    rcases low_mode_cases hlow with hb | hd | hc
    · have hown := (hPT.envelope_degree i x hx)
      simp [OwnDegOK, hb] at hown
      have hscaled : (T.S.n k : ℝ) *
          |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤ κ.Kbd := by
        have h' := (le_div_iff₀ hnpos).mp hown
        simpa [mul_comm] using h'
      have hK16L : κ.Kbd ≤ K16 * Real.log (T.S.n k : ℝ) := by
        calc
          κ.Kbd ≤ K16 := hK16Kbd
          _ = K16 * 1 := by ring
          _ ≤ K16 * Real.log (T.S.n k : ℝ) :=
            mul_le_mul_of_nonneg_left hEv.log_large hK16pos.le
      exact hscaled.trans hK16L
    · have hown := (hPT.envelope_degree i x hx)
      simp [OwnDegOK, hd] at hown
      rcases hown with ⟨hlo, hhi⟩
      have hfrac : 0 ≤ (PT.tiling.P i).g / (4 * (T.S.n k : ℝ)) := by positivity
      have hnonneg : 0 ≤ deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2 := by
        linarith
      have habs : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| =
          deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2 := abs_of_nonneg hnonneg
      have hgap : deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2 ≤
          4 * (PT.tiling.P i).g / (T.S.n k : ℝ) := by linarith
      have hscaled : (T.S.n k : ℝ) *
          |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
          4 * (PT.tiling.P i).g := by
        rw [habs]
        have h' := (le_div_iff₀ hnpos).mp hgap
        simpa [mul_comm] using h'
      have hgain : 4 * (PT.tiling.P i).g ≤ 4 * κ.KB * Real.log (T.S.n k : ℝ) := by
        have h := mul_le_mul_of_nonneg_left
          (show (PT.tiling.P i).g ≤ κ.KB * Real.log (T.S.n k : ℝ) by
            rcases hPT.tiling_valid.direct_data (Or.inl hd) i with
              ⟨_, _, _, _, _, _, hhigh⟩
            apply le_of_not_gt
            intro hlt
            exact (by simp [hd] : PT.tiling.mode ≠ .highDirect) (hhigh.mpr hlt))
          (by norm_num : (0 : ℝ) ≤ 4)
        nlinarith [h]
      have hK16log : 4 * κ.KB * Real.log (T.S.n k : ℝ) ≤
          K16 * Real.log (T.S.n k : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hK16KB hlognonneg
        nlinarith [h]
      exact hscaled.trans (hgain.trans hK16log)
    · have hown := (hPT.envelope_degree i x hx)
      simp [OwnDegOK, hc] at hown
      have hscaled : (T.S.n k : ℝ) *
          |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
          10 * Real.rpow (PT.tiling.P i).q κ.Cb := by
        have h' := (le_div_iff₀ hnpos).mp hown
        simpa [mul_comm] using h'
      rcases hPT.tiling_valid.cluster_data (Or.inl hc) i with
        ⟨_, _, _, _, _, _, _, _, _, hlowq, _, _⟩
      have hqle : (PT.tiling.P i).q ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq := hlowq.mp hc
      have hpow : Real.rpow (PT.tiling.P i).q κ.Cb ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) := by
        calc
          Real.rpow (PT.tiling.P i).q κ.Cb ≤
              Real.rpow (Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq) κ.Cb :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hqle (by linarith [hCbpos])
          _ = Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) :=
            (Real.rpow_mul (x := Real.log (T.S.n k : ℝ)) hlogpos.le κ.cq κ.Cb).symm
      have hscaled' : 10 * Real.rpow (PT.tiling.P i).q κ.Cb ≤
          10 * Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
      exact hscaled.trans (hscaled'.trans hEv.degree_cluster)
  · intro i v hv x
    have hclean := hPT.corner_clean i v hv
    have hNo := hclean.noClique
    have hξlt : κ.ξ < 1 := by
      have hpow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
      have hαpow : κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ κ.α :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hκ.α_rng.1.le
      exact (lt_of_lt_of_le hκ.ξ_rng.2 hαpow).trans (by linarith [hκ.α_rng.2])
    have hdenNat : 4 ≤ 4 ^ (κ.u + 3) := by
      have hpow : 1 ≤ 4 ^ (κ.u + 2) := Nat.one_le_pow _ _ (by decide)
      have hindex : κ.u + 3 = (κ.u + 2) + 1 := by omega
      rw [hindex, pow_succ]
      nlinarith
    have hden : (4 : ℝ) ≤ (4 : ℝ) ^ (κ.u + 3) := by exact_mod_cast hdenNat
    have hθscaled : 3 * κ.θ < κ.ξ ^ 2 / (4 : ℝ) ^ (κ.u + 3) := by
      have hmul := mul_lt_mul_of_pos_left hκ.θ_rng.2 (by norm_num : (0 : ℝ) < 3)
      calc
        3 * κ.θ < 3 * (κ.ξ ^ 2 / (3 * (4 : ℝ) ^ (κ.u + 3))) := hmul
        _ = κ.ξ ^ 2 / (4 : ℝ) ^ (κ.u + 3) := by field_simp
    have hθbound : κ.ξ ^ 2 / (4 : ℝ) ^ (κ.u + 3) ≤ κ.ξ ^ 2 / 4 :=
      div_le_div_of_nonneg_left (sq_nonneg κ.ξ) (by norm_num)
        hden
    have hθ : 3 * κ.θ < κ.ξ ^ 2 / 4 := hθscaled.trans_le hθbound
    have hQdyad : IsDyadic (PT.tiling.Q i) := by
      rcases low_mode_cases hlow with hb | hd | hc
      · rcases hPT.tiling_valid.bounded_data hb with ⟨_, hdata⟩
        rcases hdata i with ⟨_, _, _, _, hQ⟩
        rw [hQ]
        exact hκ.bounded.1
      · exact ((hPT.tiling_valid.clique_scales i).2 (Or.inl hd)).1
      · exact ((hPT.tiling_valid.clique_scales i).1 (Or.inl hc)).1
    have hQone : 1 ≤ (PT.tiling.Q i : ℝ) := by
      exact_mod_cast one_le_of_isDyadic hQdyad
    have hconf := correlation_conflict_bound_exp (u := κ.u) (N := T.S.N k) (T.S.E k)
      PT.tiling.c (PT.π i) (PT.mesh.corner v i) x κ.ξ κ.θ
      (PT.tiling.Q i : ℝ) K16 hκ.ξ_rng.1 hθ hκ.θ_rng.1 hξlt hQone hK16two hNo
    exact hconf

end HypercubeRamsey.S18.Lane_q_s18_bridge
