import HypercubeRamsey.S09.Defs
import HypercubeRamsey.S09.Regime
import HypercubeRamsey.S08.Needs
import HypercubeRamsey.S07.InitialDiscrepancy
import HypercubeRamsey.S08.AsymmetricDiscrepancy

/-!
# Parameter selection and patch preparation helpers for lane p-s09-select
-/

namespace HypercubeRamsey

open Filter OAI.HypercubeRamsey Classical

def PreparedBias9 (P : Params9) (G : Colour) : PairProp :=
  fun n _N E μ ν =>
    μ.WidthLE ((n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) ∧
    ν.WidthLE (P.Ss (n : ℝ)) ∧
    ∀ x, μ.w x ≠ 0 →
      1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x ν

private theorem rowDeg_add_complement {N : ℕ} (E : Fin N → Fin N → Prop)
    (x : Fin N) (ν : Law N) :
    rowDeg E true x ν + rowDeg E false x ν = 1 := by
  classical
  unfold rowDeg
  rw [← Finset.sum_add_distrib]
  have hsum : ∀ y, ν.w y * (if Hits E true x y then 1 else 0) +
      ν.w y * (if Hits E false x y then 1 else 0) = ν.w y := by
    intro y
    by_cases h : E x y <;> simp [Hits, h]
  calc
    (∑ y, (ν.w y * (if Hits E true x y then 1 else 0) +
        ν.w y * (if Hits E false x y then 1 else 0))) = ∑ y, ν.w y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hsum y
    _ = 1 := ν.sum_eq_one

private theorem dens_eq_rowDeg {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ ν : Law N) : dens E c μ ν = ∑ x, μ.w x * rowDeg E c x ν := by
  classical
  unfold dens rowDeg
  congr 1
  ext x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

private theorem rowDeg_le_one {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (x : Fin N) (ν : Law N) : rowDeg E c x ν ≤ 1 := by
  classical
  unfold rowDeg
  calc
    (∑ y, ν.w y * (if Hits E c x y then 1 else 0)) ≤ ∑ y, ν.w y := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases h : Hits E c x y <;> simp [h, ν.nonneg y]
    _ = 1 := ν.sum_eq_one

private theorem goodRows_mass_ge {N : ℕ} (E : Fin N → Fin N → Prop)
    (μ ν : Law N) (c : Colour) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : 1 / 2 + δ ≤ dens E c μ ν) :
    δ ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin N =>
      1 / 2 + δ / 2 ≤ rowDeg E c x ν), μ.w x := by
  classical
  let S := Finset.univ.filter (fun x : Fin N => 1 / 2 + δ / 2 ≤ rowDeg E c x ν)
  have hpoint : ∀ x, rowDeg E c x ν ≤ 1 / 2 + δ / 2 +
      (if x ∈ S then 1 / 2 else 0) := by
    intro x
    by_cases hx : x ∈ S
    · have h := rowDeg_le_one E c x ν
      have hR : (1 : ℝ) ≤ 1 / 2 + δ / 2 + 1 / 2 := by linarith
      simpa [hx] using le_trans h hR
    · have hlt : rowDeg E c x ν < 1 / 2 + δ / 2 := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact lt_of_not_ge hx
      simp only [hx, ite_false, add_zero]
      exact le_of_lt hlt
  have hcalc : dens E c μ ν ≤ 1 / 2 + δ / 2 +
      (1 / 2) * ∑ x ∈ S, μ.w x := by
    rw [dens_eq_rowDeg]
    calc
      (∑ x, μ.w x * rowDeg E c x ν) ≤
          ∑ x, μ.w x * (1 / 2 + δ / 2 + (if x ∈ S then 1 / 2 else 0)) := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hpoint x) (μ.nonneg x)
      _ = 1 / 2 + δ / 2 + (1 / 2) * ∑ x ∈ S, μ.w x := by
        calc
          _ = (∑ x, μ.w x) * (1 / 2 + δ / 2) +
              ∑ x, μ.w x * (if x ∈ S then 1 / 2 else 0) := by
            calc
              _ = ∑ x, (μ.w x * (1 / 2 + δ / 2) +
                  μ.w x * (if x ∈ S then 1 / 2 else 0)) := by
                apply Finset.sum_congr rfl
                intro x hx
                ring
              _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          _ = 1 / 2 + δ / 2 + (1 / 2) * ∑ x ∈ S, μ.w x := by
            rw [μ.sum_eq_one]
            have hterm : ∑ x, μ.w x * (if x ∈ S then 1 / 2 else 0) =
                (1 / 2) * ∑ x ∈ S, μ.w x := by
              calc
                _ = ∑ x, (if x ∈ S then μ.w x else 0) * (1 / 2) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  split_ifs <;> ring
                _ = (∑ x, if x ∈ S then μ.w x else 0) * (1 / 2) := by
                  rw [← Finset.sum_mul]
                _ = (∑ x ∈ S, μ.w x) * (1 / 2) := by
                  have hS : ∑ x ∈ S, μ.w x = ∑ x, if x ∈ S then μ.w x else 0 := by
                    have hEq : S = Finset.univ.filter (fun x : Fin N => x ∈ S) := by
                      ext x
                      simp
                    rw [hEq]
                    simp [Finset.sum_filter]
                  rw [← hS]
                _ = 1 / 2 * ∑ x ∈ S, μ.w x := by ring
            rw [hterm]
            ring
  have := le_trans hd hcalc
  linarith

private theorem goodRows_mass_ge_half {N : ℕ} (E : Fin N → Fin N → Prop)
    (μ ν : Law N) :
    1 / 2 ≤ max
      (∑ x ∈ Finset.univ.filter (fun x : Fin N => 1 / 2 ≤ rowDeg E true x ν), μ.w x)
      (∑ x ∈ Finset.univ.filter (fun x : Fin N => 1 / 2 ≤ rowDeg E false x ν), μ.w x) := by
  classical
  let St := Finset.univ.filter (fun x : Fin N => 1 / 2 ≤ rowDeg E true x ν)
  let Sf := Finset.univ.filter (fun x : Fin N => 1 / 2 ≤ rowDeg E false x ν)
  have hcover : ∀ x, x ∈ St ∨ x ∈ Sf := by
    intro x
    have h := rowDeg_add_complement E x ν
    by_contra hn
    simp only [St, Sf, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    push_neg at hn
    linarith [hn.1, hn.2]
  have hsum : 1 ≤ (∑ x ∈ St, μ.w x) + ∑ x ∈ Sf, μ.w x := by
    calc
      1 = ∑ x, μ.w x := μ.sum_eq_one.symm
      _ ≤ ∑ x, μ.w x * ((if x ∈ St then 1 else 0) + (if x ∈ Sf then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro x hx
        have hcoeff : (1 : ℝ) ≤ (if x ∈ St then 1 else 0) + (if x ∈ Sf then 1 else 0) := by
          rcases hcover x with hx | hx
          · simp only [hx, if_true]
            split_ifs <;> norm_num
          · simp only [hx, if_true]
            split_ifs <;> norm_num
        simpa using mul_le_mul_of_nonneg_left hcoeff (μ.nonneg x)
      _ = (∑ x ∈ St, μ.w x) + ∑ x ∈ Sf, μ.w x := by
        calc
          _ = ∑ x, (μ.w x * (if x ∈ St then 1 else 0) +
              μ.w x * (if x ∈ Sf then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = (∑ x, μ.w x * (if x ∈ St then 1 else 0)) +
              ∑ x, μ.w x * (if x ∈ Sf then 1 else 0) := Finset.sum_add_distrib
          _ = (∑ x ∈ St, μ.w x) + ∑ x ∈ Sf, μ.w x := by
            have hfilter (A : Finset (Fin N)) :
                ∑ x, μ.w x * (if x ∈ A then 1 else 0) = ∑ x ∈ A, μ.w x := by
              calc
                _ = ∑ x, if x ∈ A then μ.w x else 0 := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  split_ifs <;> simp
                _ = ∑ x ∈ A, μ.w x := by
                  have hEq : A = Finset.univ.filter (fun x : Fin N => x ∈ A) := by
                    ext x
                    simp
                  rw [hEq]
                  simp [Finset.sum_filter]
            rw [hfilter St, hfilter Sf]
  by_cases hleft : (∑ x ∈ St, μ.w x) ≥ (∑ x ∈ Sf, μ.w x)
  · rw [max_eq_left hleft]
    linarith
  · rw [max_eq_right (le_of_not_ge hleft)]
    linarith

private theorem restrictPrepared9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X : Finset (Fin N)}
    (G : Colour) (μ ν : Law N) (S : Finset (Fin N))
    (hN : 0 < N) (hpos : 0 < ∑ x ∈ S, μ.w x)
    (hrec : (∑ x ∈ S, μ.w x)⁻¹ ≤
      Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ) + 1))
    (hμX : μ.SupportedIn X)
    (hμw : μ.WidthLE ((n : ℝ) ^ (P.xS : ℝ)))
    (hνw : ν.WidthLE (P.Ss (n : ℝ)))
    (hgood : ∀ x ∈ S, 1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x ν) :
    let μ' := μ.restrict S hpos
    μ'.SupportedIn X ∧
      μ'.WidthLE ((n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) ∧
      ν.WidthLE (P.Ss (n : ℝ)) ∧
      ∀ x, μ'.w x ≠ 0 → 1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x ν := by
  classical
  dsimp
  let μ' := μ.restrict S hpos
  have hsupp : μ'.SupportedIn X := by
    intro x hxX
    by_cases hxS : x ∈ S
    · simp [μ', Law.restrict, hxS, hμX x hxX]
    · simp [μ', Law.restrict, hxS]
  have hwidth : μ'.WidthLE
      ((n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) := by
    intro x
    by_cases hxS : x ∈ S
    · have hval : μ'.w x = μ.w x / (∑ y ∈ S, μ.w y) := by
        simp [μ', Law.restrict, hxS]
      rw [hval]
      unfold Law.WidthLE at hμw
      have hden : 0 < (N : ℝ) := by exact_mod_cast hN
      calc
        μ.w x / (∑ y ∈ S, μ.w y) = μ.w x * (∑ y ∈ S, μ.w y)⁻¹ := by ring
        _ ≤ (Real.exp ((n : ℝ) ^ (P.xS : ℝ)) / (N : ℝ)) *
              (∑ y ∈ S, μ.w y)⁻¹ :=
          mul_le_mul_of_nonneg_right (hμw x) (inv_nonneg.mpr hpos.le)
        _ ≤ (Real.exp ((n : ℝ) ^ (P.xS : ℝ)) / (N : ℝ)) *
              Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hrec (div_nonneg (Real.exp_nonneg _) hden.le)
        _ = Real.exp ((n : ℝ) ^ (P.xS : ℝ) +
              (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) / (N : ℝ) := by
          rw [div_eq_mul_inv]
          calc
            _ = Real.exp ((n : ℝ) ^ (P.xS : ℝ)) *
                Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ) + 1) * (N : ℝ)⁻¹ := by ring
            _ = Real.exp ((n : ℝ) ^ (P.xS : ℝ) +
                ((P.hPlus : ℝ) * Real.log (n : ℝ) + 1)) * (N : ℝ)⁻¹ := by
              rw [← Real.exp_add]
            _ = _ := by congr 1 <;> ring_nf
    · have hval : μ'.w x = 0 := by simp [μ', Law.restrict, hxS]
      rw [hval]
      positivity
  have hrows : ∀ x, μ'.w x ≠ 0 →
      1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x ν := by
    intro x hx
    by_contra hxg
    have hxS : x ∈ S := by
      by_contra hnot
      have : μ'.w x = 0 := by simp [μ', Law.restrict, hnot]
      exact hx this
    exact (not_le_of_gt (lt_of_not_ge hxg)) (hgood x hxS)
  exact ⟨hsupp, hwidth, hνw, hrows⟩

private theorem trimBiasPair9 {P : Params9} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {A B : Finset (Fin N)}
    (hP : P.Valid) (hN : 0 < N) (μ ν : Law N)
    (hμA : μ.SupportedIn A) (hνB : ν.SupportedIn B)
    (hμw : μ.WidthLE ((n : ℝ) ^ (P.xS : ℝ)))
    (hνw : ν.WidthLE (P.Ss (n : ℝ)))
    (hbias : (n : ℝ) ^ (-(P.hPlus : ℝ)) ≤ |dens E true μ ν - 1 / 2|) :
    ∃ G : Colour, ∃ μ' : Law N,
      μ'.SupportedIn A ∧
      μ'.WidthLE ((n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) ∧
      ν.WidthLE (P.Ss (n : ℝ)) ∧
      ∀ x, μ'.w x ≠ 0 →
        1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x ν := by
  classical
  rcases hP with ⟨⟨hXSPos, _, _⟩, ⟨hMinus, hMinusPlus, _⟩, _, _, _, _, _⟩
  have hPlusPos : 0 < (P.hPlus : ℝ) := by
    exact_mod_cast lt_trans hMinus hMinusPlus
  let δ : ℝ := (n : ℝ) ^ (-(P.hPlus : ℝ))
  by_cases hn0 : n = 0
  · subst n
    have hzeroPow : (0 : ℝ) ^ (-(P.hPlus : ℝ)) = 0 :=
      Real.zero_rpow (by linarith)
    have hδ : δ = 0 := by simpa [δ] using hzeroPow
    have hxzero : (0 : ℝ) ^ (P.xS : ℝ) = 0 :=
      Real.zero_rpow (by exact_mod_cast ne_of_gt hXSPos)
    have hhalf := goodRows_mass_ge_half E μ ν
    let St : Finset (Fin N) := Finset.univ.filter
      (fun x : Fin N => 1 / 2 ≤ rowDeg E true x ν)
    let Sf : Finset (Fin N) := Finset.univ.filter
      (fun x : Fin N => 1 / 2 ≤ rowDeg E false x ν)
    let mt : ℝ := ∑ x ∈ St, μ.w x
    let mf : ℝ := ∑ x ∈ Sf, μ.w x
    by_cases hcmp : mf ≤ mt
    · let S : Finset (Fin N) := St
      have hmass : 1 / 2 ≤ ∑ x ∈ S, μ.w x := by
        rcases (le_max_iff).mp hhalf with ht | hf
        · simpa [S, St] using ht
        · have hcomp : (∑ x ∈ Sf, μ.w x) ≤ (∑ x ∈ St, μ.w x) := by
            simpa [mf, mt, Sf, St] using hcmp
          exact le_trans (by simpa [S, Sf] using hf) hcomp
      have hpos : 0 < ∑ x ∈ S, μ.w x := lt_of_lt_of_le (by norm_num) hmass
      have hrec : (∑ x ∈ S, μ.w x)⁻¹ ≤ Real.exp ((P.hPlus : ℝ) * Real.log 0 + 1) := by
        have hinv : (∑ x ∈ S, μ.w x)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
          (inv_le_inv₀ hpos (by norm_num)).2 hmass
        calc
          _ ≤ 2 := by norm_num at hinv ⊢; exact hinv
          _ ≤ Real.exp ((P.hPlus : ℝ) * Real.log 0 + 1) := by
            simp only [Real.log_zero, mul_zero, zero_add]
            nlinarith [Real.add_one_le_exp (1 : ℝ)]
      have hgood : ∀ x ∈ S, 1 / 2 + (0 : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E true x ν := by
        intro x hx
        have hx' : x ∈ St := by simpa [S] using hx
        simpa [hzeroPow] using (Finset.mem_filter.mp hx').2
      let μ' := μ.restrict S hpos
      have hprepared := restrictPrepared9
        (P := P) true μ ν S hN hpos (by simpa [Nat.cast_zero] using hrec) hμA hμw hνw
          (by simpa [Nat.cast_zero, hzeroPow] using hgood)
      rcases hprepared with ⟨hμ'A, hμ'W, hν'W, hrows⟩
      refine ⟨true, μ', hμ'A, ?_, hν'W, ?_⟩
      · simpa [Real.log_zero, hxzero, Nat.cast_zero] using hμ'W
      · simpa [hzeroPow, Nat.cast_zero] using hrows
    · let S : Finset (Fin N) := Sf
      have hmass : 1 / 2 ≤ ∑ x ∈ S, μ.w x := by
        rcases (le_max_iff).mp hhalf with ht | hf
        · have hcomp : (∑ x ∈ St, μ.w x) ≤ (∑ x ∈ Sf, μ.w x) := by
            have hcomp' : mt ≤ mf := by
              rcases le_total mt mf with h | h
              · exact h
              · exact (hcmp h).elim
            simpa [mt, mf, St, Sf] using hcomp'
          exact le_trans (by simpa [St] using ht) hcomp
        · simpa [S, Sf] using hf
      have hpos : 0 < ∑ x ∈ S, μ.w x := lt_of_lt_of_le (by norm_num) hmass
      have hrec : (∑ x ∈ S, μ.w x)⁻¹ ≤ Real.exp ((P.hPlus : ℝ) * Real.log 0 + 1) := by
        have hinv : (∑ x ∈ S, μ.w x)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
          (inv_le_inv₀ hpos (by norm_num)).2 hmass
        calc
          _ ≤ 2 := by norm_num at hinv ⊢; exact hinv
          _ ≤ Real.exp ((P.hPlus : ℝ) * Real.log 0 + 1) := by
            simp only [Real.log_zero, mul_zero, zero_add]
            nlinarith [Real.add_one_le_exp (1 : ℝ)]
      have hgood : ∀ x ∈ S, 1 / 2 + (0 : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E false x ν := by
        intro x hx
        have hx' : x ∈ Sf := by simpa [S] using hx
        simpa [hzeroPow] using (Finset.mem_filter.mp hx').2
      let μ' := μ.restrict S hpos
      have hprepared := restrictPrepared9
        (P := P) false μ ν S hN hpos (by simpa [Nat.cast_zero] using hrec) hμA hμw hνw
          (by simpa [Nat.cast_zero, hzeroPow] using hgood)
      rcases hprepared with ⟨hμ'A, hμ'W, hν'W, hrows⟩
      refine ⟨false, μ', hμ'A, ?_, hν'W, ?_⟩
      · simpa [Real.log_zero, hxzero, Nat.cast_zero] using hμ'W
      · simpa [hzeroPow, Nat.cast_zero] using hrows
  · have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact Real.rpow_pos_of_pos hn _
    have hdens := dens_add_dens_not E μ ν
    by_cases htrue : 1 / 2 + δ ≤ dens E true μ ν
    · let G : Colour := true
      let S : Finset (Fin N) := Finset.univ.filter
        (fun x : Fin N => 1 / 2 + δ / 2 ≤ rowDeg E G x ν)
      have hmass0 := goodRows_mass_ge E μ ν G δ hδpos.le htrue
      have hmass : δ ≤ ∑ x ∈ S, μ.w x := by simpa [S, G, δ] using hmass0
      have hpos : 0 < ∑ x ∈ S, μ.w x := lt_of_lt_of_le hδpos hmass
      have hδeq : δ = Real.exp (-((P.hPlus : ℝ) * Real.log (n : ℝ))) := by
        dsimp [δ]
        rw [Real.rpow_def_of_pos hn]
        congr 1
        ring
      have hδinv : δ⁻¹ = Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ)) := by
        calc
          _ = (Real.exp (-((P.hPlus : ℝ) * Real.log (n : ℝ))))⁻¹ := by rw [← hδeq]
          _ = Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ)) := by
            rw [Real.exp_neg]
            simp
      have hrec : (∑ x ∈ S, μ.w x)⁻¹ ≤
          Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ) + 1) := by
        have hinv : (∑ x ∈ S, μ.w x)⁻¹ ≤ δ⁻¹ :=
          (inv_le_inv₀ hpos hδpos).2 hmass
        calc
          _ ≤ Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ)) := by rw [← hδinv]; exact hinv
          _ ≤ Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ) + 1) :=
            Real.exp_le_exp.mpr (by linarith)
      have hgood : ∀ x ∈ S, 1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x ν := by
        intro x hx
        simpa [S, G, δ] using hx
      let μ' := μ.restrict S hpos
      have hprepared := restrictPrepared9
        (P := P) G μ ν S hN hpos hrec hμA hμw hνw hgood
      rcases hprepared with ⟨hμ'A, hμ'W, hν'W, hrows⟩
      exact ⟨G, μ', hμ'A, hμ'W, hν'W, hrows⟩

    · let G : Colour := false
      have hdevneg : dens E true μ ν - 1 / 2 < 0 := by
        by_contra hnneg
        have habs : |dens E true μ ν - 1 / 2| = dens E true μ ν - 1 / 2 := abs_of_nonneg (le_of_not_gt hnneg)
        linarith [hbias]
      have hdev : δ ≤ -(dens E true μ ν - 1 / 2) := by
        have habs : |dens E true μ ν - 1 / 2| = -(dens E true μ ν - 1 / 2) := abs_of_neg hdevneg
        rw [habs] at hbias
        exact hbias
      have hfalse : 1 / 2 + δ ≤ dens E false μ ν := by linarith
      let S : Finset (Fin N) := Finset.univ.filter
        (fun x : Fin N => 1 / 2 + δ / 2 ≤ rowDeg E G x ν)
      have hmass0 := goodRows_mass_ge E μ ν G δ hδpos.le hfalse
      have hmass : δ ≤ ∑ x ∈ S, μ.w x := by simpa [S, G, δ] using hmass0
      have hpos : 0 < ∑ x ∈ S, μ.w x := lt_of_lt_of_le hδpos hmass
      have hδeq : δ = Real.exp (-((P.hPlus : ℝ) * Real.log (n : ℝ))) := by
        dsimp [δ]
        rw [Real.rpow_def_of_pos hn]
        congr 1
        ring
      have hδinv : δ⁻¹ = Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ)) := by
        calc
          _ = (Real.exp (-((P.hPlus : ℝ) * Real.log (n : ℝ))))⁻¹ := by rw [← hδeq]
          _ = Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ)) := by
            rw [Real.exp_neg]
            simp
      have hrec : (∑ x ∈ S, μ.w x)⁻¹ ≤
          Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ) + 1) := by
        have hinv : (∑ x ∈ S, μ.w x)⁻¹ ≤ δ⁻¹ :=
          (inv_le_inv₀ hpos hδpos).2 hmass
        calc
          _ ≤ Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ)) := by rw [← hδinv]; exact hinv
          _ ≤ Real.exp ((P.hPlus : ℝ) * Real.log (n : ℝ) + 1) :=
            Real.exp_le_exp.mpr (by linarith)
      have hgood : ∀ x ∈ S, 1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x ν := by
        intro x hx
        simpa [S, G, δ] using hx
      let μ' := μ.restrict S hpos
      have hprepared := restrictPrepared9
        (P := P) G μ ν S hN hpos hrec hμA hμw hνw hgood
      rcases hprepared with ⟨hμ'A, hμ'W, hν'W, hrows⟩
      exact ⟨G, μ', hμ'A, hμ'W, hν'W, hrows⟩

private theorem Hpow_le_of_AvP {T : Stage} {x y : ℝ} {h : ℚ}
    (hpos : 0 < h) (hav : AvP T x y h) : Hpow T x y ≤ (h : ℝ) := by
  unfold Hpow
  have hbdd : BddBelow
      ({z : ℝ | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = z ∧ AvP T x y q} ∪ {2}) := by
    refine ⟨0, ?_⟩
    intro z hz
    simp only [Set.mem_union] at hz
    rcases hz with hz | hz
    · rcases hz with ⟨q, hq, hcast, _⟩
      rw [← hcast]
      exact_mod_cast hq.le
    · simp only [Set.mem_singleton_iff] at hz
      rw [hz]
      norm_num
  apply csInf_le hbdd
  exact Set.mem_union_left _ ⟨h, hpos, rfl, hav⟩

private theorem Hpow_ge_of_disc {T : Stage} {x y q : ℚ}
    (hxy : 0 < x ∧ 0 < y) (hq : 0 < q) (hq2 : (q : ℝ) ≤ 2)
    (hd : DiscAt T (pw (x : ℝ)) (pw (y : ℝ))
      (fun n => (n : ℝ) ^ (-(q : ℝ)))) :
    (q : ℝ) ≤ Hpow T (x : ℝ) (y : ℝ) := by
  unfold Hpow
  let S : Set ℝ := {z : ℝ | ∃ r : ℚ, 0 < r ∧ (r : ℝ) = z ∧ AvP T x y r} ∪ {2}
  have hnonempty : S.Nonempty := ⟨2, Set.mem_union_right _ (Set.mem_singleton 2)⟩
  have hbelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro z hz
    change z ∈ ({z : ℝ | ∃ r : ℚ, 0 < r ∧ (r : ℝ) = z ∧ AvP T x y r} ∪ {2}) at hz
    simp only [Set.mem_union] at hz
    rcases hz with hz | hz
    · rcases hz with ⟨r, hr, hcast, _⟩
      rw [← hcast]
      exact_mod_cast hr.le
    · simp only [Set.mem_singleton_iff] at hz
      rw [hz]
      norm_num
  apply (le_csInf_iff hbelow hnonempty).2
  intro z hz
  change z ∈ ({z : ℝ | ∃ r : ℚ, 0 < r ∧ (r : ℝ) = z ∧ AvP T x y r} ∪ {2}) at hz
  simp only [Set.mem_union] at hz
  rcases hz with hz | hz
  · rcases hz with ⟨r, hr, hcast, hav⟩
    by_contra hnot
    have hsmall : (r : ℝ) < (q : ℝ) := by
      rw [hcast]
      exact lt_of_not_ge hnot
    have hNo := not_AvP_of_discAt (T := T) (x := x) (y := y)
      (h := r) (h₀ := q) hxy hr (by exact_mod_cast hsmall) hd
    exact (hNo hav).elim
  · simp only [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hq2

private theorem exists_small_drop9 (f : ℕ → ℝ) (M : ℕ) (ε L U : ℝ)
    (hM : 0 < M) (hε : 0 < ε)
    (hdec : ∀ i, i < M → f (i + 1) ≤ f i)
    (hlow : ∀ i, i ≤ M → L ≤ f i)
    (hhigh : ∀ i, i ≤ M → f i ≤ U)
    (hrange : U - L < (M : ℝ) * ε) :
    ∃ i, i < M ∧ f i - f (i + 1) < ε := by
  classical
  have htel : ∀ m : ℕ, (∑ i ∈ Finset.range m, (f i - f (i + 1))) = f 0 - f m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  by_contra hnot
  push_neg at hnot
  have hsum : (M : ℝ) * ε ≤ ∑ i ∈ Finset.range M, (f i - f (i + 1)) := by
    calc
      (M : ℝ) * ε = ∑ _i ∈ Finset.range M, ε := by simp
      _ ≤ ∑ i ∈ Finset.range M, (f i - f (i + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hnot i (Finset.mem_range.mp hi)
  have hbound : f 0 - f M ≤ U - L := by
    exact sub_le_sub (hhigh 0 (Nat.zero_le M)) (hlow M le_rfl)
  rw [htel] at hsum
  linarith

private def interpQ9 (a b : ℚ) (M j : ℕ) : ℚ :=
  a + (j : ℚ) * (b - a) / (M : ℚ)

private theorem interpQ9_bounds {a b : ℚ} (hab : a ≤ b) {M j : ℕ}
    (hM : 0 < M) (hj : j ≤ M) :
    a ≤ interpQ9 a b M j ∧ interpQ9 a b M j ≤ b := by
  have hM' : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hM
  have hj' : (j : ℚ) ≤ (M : ℚ) := by exact_mod_cast hj
  have hj0 : (0 : ℚ) ≤ (j : ℚ) := by positivity
  let t : ℚ := (j : ℚ) / (M : ℚ)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hM').2 hj'
  constructor
  · dsimp [interpQ9, t]
    have hterm : 0 ≤ (j : ℚ) * (b - a) / (M : ℚ) :=
      div_nonneg (mul_nonneg hj0 (sub_nonneg.mpr hab)) hM'.le
    exact le_add_of_nonneg_right hterm
  · dsimp [interpQ9, t]
    have hprod : ((j : ℚ) / (M : ℚ)) * (b - a) ≤ b - a := by
      simpa using mul_le_mul_of_nonneg_right ht1 (sub_nonneg.mpr hab)
    have hmuleq : (j : ℚ) * (b - a) / (M : ℚ) =
        ((j : ℚ) / (M : ℚ)) * (b - a) := by ring
    rw [hmuleq]
    linarith

private theorem interpQ9_step {a b : ℚ} (hab : a < b) {M j : ℕ}
    (hM : 0 < M) :
    interpQ9 a b M (j + 1) - interpQ9 a b M j = (b - a) / (M : ℚ) := by
  dsimp [interpQ9]
  push_cast
  ring

private theorem interpQ9_zero (a b : ℚ) (M : ℕ) : interpQ9 a b M 0 = a := by
  simp [interpQ9]

private theorem interpQ9_end {a b : ℚ} {M : ℕ} (hM : 0 < M) :
    interpQ9 a b M M = b := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  dsimp [interpQ9]
  field_simp
  ring

set_option maxHeartbeats 100000000 in
theorem p92_select_sublinear_impl (T : Stage) (hT : StabilizedOn T FamB)
    (hH : HdagLtOne T) :
    ∃ P : Params9, P.Valid ∧ P.IsSublinear ∧ P.SubSelection T := by
  classical
  rcases hH with ⟨h0, hh0, hdag⟩
  let hA : ℚ := (max h0 0 + 1) / 2
  have hApos : 0 < hA := by dsimp [hA]; positivity
  have hmaxlt : max h0 0 < 1 := max_lt_iff.mpr ⟨hh0, by norm_num⟩
  have hAlt : hA < 1 := by
    dsimp [hA]
    linarith [hmaxlt]
  have hh0A : h0 ≤ hA := by
    have hmax : max h0 0 ≤ hA := by dsimp [hA]; linarith [hmaxlt]
    exact le_trans (le_max_left _ _) hmax
  obtain ⟨η, hη, hInit⟩ := HypercubeRamsey.S07.initial_discrepancy_proof
  have hD0 := hInit T hT
  have hτ : 0 < tau8 η := by unfold tau8; positivity
  have hAltR : (hA : ℝ) < 1 := by exact_mod_cast hAlt
  let xlim : ℝ := min (1 / 100) (min (tau8 η / 8) ((1 - (hA : ℝ)) / 1000))
  have hxlim : 0 < xlim := by dsimp [xlim]; positivity
  obtain ⟨xb, hxb0, hxbLim⟩ := exists_rat_btwn hxlim
  have hxbR0 : 0 < (xb : ℝ) := hxb0
  have hxbR1 : (xb : ℝ) < 1 / 100 := lt_of_lt_of_le hxbLim (min_le_left _ _)
  have hxbτ : (xb : ℝ) < tau8 η / 8 :=
    lt_of_lt_of_le hxbLim (le_trans (min_le_right _ _) (min_le_left _ _))
  have hxbA : (xb : ℝ) < (1 - (hA : ℝ)) / 1000 :=
    lt_of_lt_of_le hxbLim (le_trans (min_le_right _ _) (min_le_right _ _))
  have hxbQ0 : 0 < xb := by exact_mod_cast hxbR0
  have hxbLt1R : (xb : ℝ) < 1 := lt_trans hxbR1 (by norm_num)
  have hxbLt1 : xb < 1 := by exact_mod_cast hxbLt1R
  obtain ⟨y0, hy00, hy01, hav0⟩ := hdag xb hxbQ0 hxbLt1
  let ybase : ℚ := max y0 (1 - xb / 100)
  have hybase0 : 0 < ybase := lt_of_lt_of_le hy00 (le_max_left _ _)
  have hybase1 : ybase < 1 := by
    apply max_lt_iff.mpr
    constructor
    · exact hy01
    · linarith
  have hybaseNear : 1 - (ybase : ℝ) ≤ (xb : ℝ) / 100 := by
    have hmax : (1 - xb / 100 : ℚ) ≤ ybase := le_max_right _ _
    have hmaxR : (1 - (xb : ℝ) / 100) ≤ (ybase : ℝ) := by exact_mod_cast hmax
    linarith
  have havBase : AvP T (xb : ℝ) (ybase : ℝ) (hA : ℝ) := by
    apply AvP.mono hav0 le_rfl
    · exact_mod_cast (le_max_left y0 (1 - xb / 100))
    · exact_mod_cast hh0A
  let yend : ℚ := (ybase + 1) / 2
  have hybaseEnd : ybase < yend := by dsimp [yend]; linarith [hybase1]
  have hyend1 : yend < 1 := by dsimp [yend]; linarith [hybase1]
  have hyend0 : 0 < yend := lt_trans hybase0 hybaseEnd
  let xend : ℚ := 2 * xb
  have hxend0 : 0 < xend := by dsimp [xend]; positivity
  have hxendτ : (xend : ℝ) < tau8 η / 4 := by
    have hscaled := mul_lt_mul_of_pos_left hxbτ (by norm_num : 0 < (2 : ℝ))
    have hscaled' : 2 * (xb : ℝ) < tau8 η / 4 := by
      calc
        2 * (xb : ℝ) < 2 * (tau8 η / 8) := hscaled
        _ = tau8 η / 4 := by ring
    simpa [xend] using hscaled'
  have hxend1 : xend < 1 := by
    have hxendR : (xend : ℝ) = 2 * (xb : ℝ) := by norm_num [xend]
    have hxend1R : (xend : ℝ) < 1 := by rw [hxendR]; linarith [hxbR1]
    exact_mod_cast hxend1R
  obtain ⟨H, hHpos, hAsym, _⟩ := asymmetric_discrepancy η hη T hT hD0 xend yend
    (by exact_mod_cast hxend0) hxendτ (by exact_mod_cast hyend0) (by exact_mod_cast hyend1)
  have hMinPos : 0 < min H 1 := lt_min hHpos (by norm_num)
  obtain ⟨q, hq0, hqMin⟩ := exists_rat_btwn hMinPos
  have hqPos : 0 < q := by exact_mod_cast hq0
  have hqRPos : 0 < (q : ℝ) := by exact_mod_cast hqPos
  have hqH : (q : ℝ) < H := lt_of_lt_of_le hqMin (min_le_left _ _)
  have hq1 : (q : ℝ) < 1 := lt_of_lt_of_le hqMin (min_le_right _ _)
  have hErr : ∀ᶠ z : ℝ in atTop, z ^ (-H) ≤ z ^ (-(q : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    exact Real.rpow_le_rpow_of_exponent_le hz (by linarith)
  have hDq : DiscAt T (pw (xend : ℝ)) (pw (yend : ℝ))
      (fun z => z ^ (-(q : ℝ))) :=
    DiscAt.mono hAsym (Filter.Eventually.of_forall fun _ => le_rfl)
      (Filter.Eventually.of_forall fun _ => le_rfl) hErr
  have hq2 : (q : ℝ) ≤ 2 := by linarith [hq1]
  have hpowDeep : (q : ℝ) ≤ Hpow T (xend : ℝ) (yend : ℝ) :=
    Hpow_ge_of_disc ⟨by exact_mod_cast hxend0, by exact_mod_cast hyend0⟩ hqPos hq2 hDq
  have hpowShallow : Hpow T (xb : ℝ) (ybase : ℝ) ≤ (hA : ℝ) :=
    Hpow_le_of_AvP hApos havBase
  have hyendR : (yend : ℝ) < 1 := by exact_mod_cast hyend1
  have hχbound : 0 < min ((xb : ℝ) / 100)
      (min ((q : ℝ) / 200)
        (min ((1 - (hA : ℝ)) / 1000) ((1 - (yend : ℝ)) / 20))) := by
    positivity
  obtain ⟨χ, hχ0, hχboundR⟩ := exists_rat_btwn hχbound
  have hχpos : 0 < χ := by exact_mod_cast hχ0
  have hχRpos : 0 < (χ : ℝ) := hχ0
  have hχxb : (χ : ℝ) < (xb : ℝ) / 100 := lt_of_lt_of_le hχboundR (min_le_left _ _)
  have hχrest : (χ : ℝ) <
      min ((q : ℝ) / 200) (min ((1 - (hA : ℝ)) / 1000) ((1 - (yend : ℝ)) / 20)) :=
    lt_of_lt_of_le hχboundR (min_le_right _ _)
  have hχq : (χ : ℝ) < (q : ℝ) / 200 := lt_of_lt_of_le hχrest (min_le_left _ _)
  have hχlast : (χ : ℝ) < min ((1 - (hA : ℝ)) / 1000) ((1 - (yend : ℝ)) / 20) :=
    lt_of_lt_of_le hχrest (min_le_right _ _)
  have hχmargin : (χ : ℝ) < (1 - (hA : ℝ)) / 1000 := lt_of_lt_of_le hχlast (min_le_left _ _)
  have hχy : (χ : ℝ) < (1 - (yend : ℝ)) / 20 := lt_of_lt_of_le hχlast (min_le_right _ _)
  obtain ⟨M, hMgt⟩ := exists_nat_gt (40 / (χ : ℝ))
  have hMposR : 0 < (M : ℝ) := lt_trans (by positivity) hMgt
  have hMpos : 0 < M := by exact_mod_cast hMposR
  have hMε : 1 < (M : ℝ) * ((χ : ℝ) / 40) := by
    have hratio : (40 / (χ : ℝ)) * ((χ : ℝ) / 40) = 1 := by
      field_simp [ne_of_gt hχRpos]
    have hmul := mul_lt_mul_of_pos_right hMgt (by positivity : 0 < (χ : ℝ) / 40)
    rw [hratio] at hmul
    convert hmul using 1 <;> ring
  have hRange : (hA : ℝ) - (q : ℝ) < (M : ℝ) * ((χ : ℝ) / 40) := by
    have hltOne : (hA : ℝ) - (q : ℝ) < 1 := by linarith [hAlt, hqRPos]
    linarith
  let xgrid : ℕ → ℚ := fun j => interpQ9 xb xend M j
  let ygrid : ℕ → ℚ := fun j => interpQ9 ybase yend M j
  let f : ℕ → ℝ := fun j => Hpow T (xgrid j : ℝ) (ygrid j : ℝ)
  have hxle : xb ≤ xend := by dsimp [xend]; linarith
  have hxltend : xb < xend := by dsimp [xend]; linarith [hxbQ0]
  have hdec : ∀ j, j < M → f (j + 1) ≤ f j := by
    intro j hj
    have hstepX : xgrid j < xgrid (j + 1) := by
      have hstep := interpQ9_step (a := xb) (b := xend) hxltend (M := M) (j := j) hMpos
      dsimp [xgrid]
      rw [← sub_pos, hstep]
      exact div_pos (sub_pos.mpr (by dsimp [xend]; linarith)) (by exact_mod_cast hMpos)
    have hstepY : ygrid j < ygrid (j + 1) := by
      have hstep := interpQ9_step (a := ybase) (b := yend) hybaseEnd (M := M) (j := j) hMpos
      dsimp [ygrid]
      rw [← sub_pos, hstep]
      exact div_pos (sub_pos.mpr hybaseEnd) (by exact_mod_cast hMpos)
    calc
      Hpow T (xgrid (j + 1) : ℝ) (ygrid (j + 1) : ℝ) ≤
          Hpow T (xgrid j : ℝ) (ygrid (j + 1) : ℝ) :=
        Hpow_antitone_x (T := T) (by exact_mod_cast hstepX.le)
      _ ≤ Hpow T (xgrid j : ℝ) (ygrid j : ℝ) :=
        Hpow_antitone_y (T := T) (by exact_mod_cast hstepY.le)
  have hlow : ∀ j, j ≤ M → (q : ℝ) ≤ f j := by
    intro j hj
    have hxj := (interpQ9_bounds (a := xb) (b := xend) hxle hMpos hj).2
    have hyj := (interpQ9_bounds (a := ybase) (b := yend) (le_of_lt hybaseEnd) hMpos hj).2
    calc
      (q : ℝ) ≤ Hpow T (xend : ℝ) (yend : ℝ) := hpowDeep
      _ ≤ Hpow T (xgrid j : ℝ) (yend : ℝ) :=
        Hpow_antitone_x (T := T) (by exact_mod_cast hxj)
      _ ≤ Hpow T (xgrid j : ℝ) (ygrid j : ℝ) :=
        Hpow_antitone_y (T := T) (by exact_mod_cast hyj)
  have hhigh : ∀ j, j ≤ M → f j ≤ (hA : ℝ) := by
    intro j hj
    have hxj := (interpQ9_bounds (a := xb) (b := xend) hxle hMpos hj).1
    have hyj := (interpQ9_bounds (a := ybase) (b := yend) (le_of_lt hybaseEnd) hMpos hj).1
    calc
      Hpow T (xgrid j : ℝ) (ygrid j : ℝ) ≤
          Hpow T (xb : ℝ) (ygrid j : ℝ) :=
        Hpow_antitone_x (T := T) (by exact_mod_cast hxj)
      _ ≤ Hpow T (xb : ℝ) (ybase : ℝ) :=
        Hpow_antitone_y (T := T) (by exact_mod_cast hyj)
      _ ≤ (hA : ℝ) := hpowShallow
  obtain ⟨i, hiM, hdrop⟩ := exists_small_drop9 f M ((χ : ℝ) / 40)
    (q : ℝ) (hA : ℝ) hMpos (by positivity) hdec hlow hhigh hRange
  let xs : ℚ := xgrid i
  let xd : ℚ := xgrid (i + 1)
  let ys : ℚ := ygrid i
  let yd : ℚ := ygrid (i + 1)
  have hiSucc : i + 1 ≤ M := by omega
  have hxsBase : xb ≤ xs := by simpa [xs, xgrid] using
    (interpQ9_bounds (a := xb) (b := xend) hxle hMpos (Nat.le_of_lt hiM)).1
  have hxdEnd : xd ≤ xend := by simpa [xd, xgrid] using
    (interpQ9_bounds (a := xb) (b := xend) hxle hMpos hiSucc).2
  have hysBase : ybase ≤ ys := by simpa [ys, ygrid] using
    (interpQ9_bounds (a := ybase) (b := yend) (le_of_lt hybaseEnd) hMpos (Nat.le_of_lt hiM)).1
  have hydEnd : yd ≤ yend := by simpa [yd, ygrid] using
    (interpQ9_bounds (a := ybase) (b := yend) (le_of_lt hybaseEnd) hMpos hiSucc).2
  have hxsPos : 0 < xs := lt_of_lt_of_le hxbQ0 hxsBase
  have hxsxd : xs < xd := by
    have hs := interpQ9_step (a := xb) (b := xend) hxltend (M := M) (j := i) hMpos
    dsimp [xs, xd, xgrid]
    rw [← sub_pos, hs]
    exact div_pos (sub_pos.mpr (by dsimp [xend]; linarith)) (by exact_mod_cast hMpos)
  have hxdPos : 0 < xd := lt_trans hxsPos hxsxd
  have hxd010 : xd < 1 / 10 := by
    have hxbQ : xb < (1 : ℚ) / 100 := by
      have hxbQ' : (xb : ℝ) < ((1 : ℚ) / 100 : ℚ) := by
        norm_num at hxbR1 ⊢
        exact hxbR1
      exact_mod_cast hxbQ'
    have hxdle : xd ≤ 2 * xb := by simpa [xend] using hxdEnd
    have h2 : 2 * xb < (1 : ℚ) / 10 := by nlinarith [hxbQ]
    exact lt_of_le_of_lt hxdle h2
  have hybaseR0 : 0 < (ybase : ℝ) := by exact_mod_cast hybase0
  have hysBaseR : (ybase : ℝ) ≤ (ys : ℝ) := by exact_mod_cast hysBase
  have hysPosR : 0 < (ys : ℝ) := lt_of_lt_of_le hybaseR0 hysBaseR
  have hysPos : 0 < ys := by exact_mod_cast hysPosR
  have hysyd : ys < yd := by
    have hs := interpQ9_step (a := ybase) (b := yend) hybaseEnd (M := M) (j := i) hMpos
    dsimp [ys, yd, ygrid]
    rw [← sub_pos, hs]
    exact div_pos (sub_pos.mpr hybaseEnd) (by exact_mod_cast hMpos)
  have hydPos : 0 < yd := lt_trans hysPos hysyd
  have hyd1 : yd < 1 := lt_of_le_of_lt hydEnd hyend1
  let σ : ℚ := ((1 - yd) + (1 - ys)) / 2
  have hσlo : 1 - yd < σ := by dsimp [σ]; linarith
  have hσhi : σ < 1 - ys := by dsimp [σ]; linarith
  have hσPos : 0 < σ := by linarith [hyd1]
  have hσy : ys < 1 - σ ∧ 1 - σ < yd := by constructor <;> linarith
  have hσxs : σ < xs / 10 := by
    have hNear : 1 - ys ≤ xb / 100 := by
      have hbaseNear : 1 - ybase ≤ xb / 100 := by exact_mod_cast hybaseNear
      linarith [hysBase]
    linarith [hσhi, hNear, hxsBase]
  let ym : ℚ := (ys + (1 - σ)) / 2
  have hysym : ys < ym := by dsimp [ym]; linarith [hσy.1]
  have hymSig : ym < 1 - σ := by dsimp [ym]; linarith [hσy.1]
  obtain ⟨hPlus, hpluslo, hplushi⟩ :=
    exists_rat_btwn (show f i < f i + (χ : ℝ) / 80 by linarith [hχRpos])
  obtain ⟨hMinus, hminuslo, hminusHi⟩ :=
    exists_rat_btwn (show f (i + 1) - (χ : ℝ) / 80 < f (i + 1) by linarith [hχRpos])
  have hplusRlo : f i < (hPlus : ℝ) := hpluslo
  have hplusRhi : (hPlus : ℝ) < f i + (χ : ℝ) / 80 := hplushi
  have hminusRlo : f (i + 1) - (χ : ℝ) / 80 < (hMinus : ℝ) := hminuslo
  have hminusRhi : (hMinus : ℝ) < f (i + 1) := hminusHi
  have hfiLow : (q : ℝ) ≤ f (i + 1) := hlow (i + 1) hiSucc
  have hfiHigh : f i ≤ (hA : ℝ) := hhigh i (Nat.le_of_lt hiM)
  have hchiSmall : (χ : ℝ) / 80 < (q : ℝ) / 2 := by
    have := hχq
    nlinarith
  have hminusRpos : 0 < (hMinus : ℝ) := by
    have hqminus : (q : ℝ) - (χ : ℝ) / 80 < (hMinus : ℝ) := by
      linarith [hfiLow, hminusRlo]
    linarith
  have hplusRpos : 0 < (hPlus : ℝ) := by
    linarith [hplusRlo, hlow i (Nat.le_of_lt hiM), hqRPos]
  have hplusRone : (hPlus : ℝ) < 1 := by
    have hmargin : (χ : ℝ) / 80 < 1 - (hA : ℝ) := by linarith [hχmargin]
    linarith [hplusRhi, hfiHigh]
  have hminusPos : 0 < hMinus := by exact_mod_cast hminusRpos
  have hplusPos : 0 < hPlus := by exact_mod_cast hplusRpos
  have hplusOne : hPlus < 1 := by exact_mod_cast hplusRone
  have hfiDrop : f (i + 1) ≤ f i := hdec i hiM
  have hminusLtPlusR : (hMinus : ℝ) < (hPlus : ℝ) := by
    linarith [hplusRlo, hminusRhi, hfiDrop]
  have hminusLtPlus : hMinus < hPlus := by exact_mod_cast hminusLtPlusR
  have hgapR : (hPlus : ℝ) - (hMinus : ℝ) < (χ : ℝ) / 10 := by
    have hsmallDrop : f i - f (i + 1) < (χ : ℝ) / 40 := by
      have := hdrop
      simpa using this
    have htmp : (hPlus : ℝ) - (hMinus : ℝ) <
        (f i - f (i + 1)) + (χ : ℝ) / 40 := by
      linarith [hplusRhi, hminusRlo]
    linarith [htmp, hsmallDrop, hχRpos]
  have hgap : hPlus - hMinus < χ / 10 := by exact_mod_cast hgapR
  have hminusHalf : (q : ℝ) / 2 < (hMinus : ℝ) := by linarith [hminusRpos, hchiSmall, hfiLow, hminusRlo]
  have hχminus : (χ : ℝ) < (hMinus : ℝ) / 100 := by
    have h := hχq
    linarith [hminusHalf]
  have hplusUB : (hPlus : ℝ) < (hA : ℝ) + (χ : ℝ) / 80 := by
    linarith [hplusRhi, hfiHigh]
  have hχone : (χ : ℝ) < (1 - (hPlus : ℝ)) / 100 := by
    linarith [hχmargin, hplusUB]
  have hχxs : (χ : ℝ) < (xs : ℝ) / 100 := by
    have hxbxs : (xb : ℝ) ≤ (xs : ℝ) := by exact_mod_cast hxsBase
    linarith [hχxb, hxbxs]
  have hchiSigma : (χ : ℝ) < (σ : ℝ) / 10 := by
    have hdecrease : 1 - (yend : ℝ) ≤ 1 - (yd : ℝ) := by
      have h : (yd : ℝ) ≤ (yend : ℝ) := by exact_mod_cast hydEnd
      linarith
    have hsigmaLower : 1 - (yend : ℝ) < (σ : ℝ) := by
      have h : 1 - (yd : ℝ) < (σ : ℝ) := by exact_mod_cast hσlo
      exact lt_of_le_of_lt hdecrease h
    have hχ : (χ : ℝ) < (1 - (yend : ℝ)) / 20 := hχy
    linarith
  have hxdGapR : (xd : ℝ) < (1 - (hPlus : ℝ)) / 10 := by
    have hxdR : (xd : ℝ) ≤ (xend : ℝ) := by exact_mod_cast hxdEnd
    have hxendR : (xend : ℝ) = 2 * (xb : ℝ) := by norm_num [xend]
    have hsmall : ((χ : ℝ) / 80) < (1 - (hA : ℝ)) / 2 := by linarith [hχmargin]
    have hmargin : (1 - (hA : ℝ)) / 20 < (1 - (hPlus : ℝ)) / 10 := by
      linarith [hplusUB, hsmall]
    have hxsmall : (xend : ℝ) < (1 - (hA : ℝ)) / 500 := by
      rw [hxendR]
      linarith [hxbA]
    linarith
  have hxdGap : xd < (1 - hPlus) / 10 := by exact_mod_cast hxdGapR
  let P : Params9 :=
    ⟨xs, xd, hMinus, hPlus, σ, χ, .sub ys yd ym⟩
  have hValid : P.Valid := by
    dsimp [P, Params9.Valid]
    refine ⟨⟨?_, ?_, hxd010⟩, ⟨hminusPos, hminusLtPlus, hplusOne⟩,
      hxdGap, ⟨hσPos, hσxs⟩, ⟨hχpos, ?_⟩, hgap, ?_⟩
    · exact hxsPos
    · exact hxsxd
    · have hchiMin : (χ : ℝ) * 100 <
          min (xs : ℝ) (min (hMinus : ℝ) (1 - (hPlus : ℝ))) := by
        apply lt_min
        · have hmul := mul_lt_mul_of_pos_right hχxs (by norm_num : 0 < (100 : ℝ))
          have hEq : ((xs : ℝ) / 100) * 100 = xs := by ring
          rw [hEq] at hmul
          exact hmul
        · apply lt_min
          · have hmul := mul_lt_mul_of_pos_right hχminus (by norm_num : 0 < (100 : ℝ))
            have hEq : ((hMinus : ℝ) / 100) * 100 = hMinus := by ring
            rw [hEq] at hmul
            exact hmul
          · have hmul := mul_lt_mul_of_pos_right hχone (by norm_num : 0 < (100 : ℝ))
            have hEq : ((1 - (hPlus : ℝ)) / 100) * 100 = 1 - (hPlus : ℝ) := by ring
            rw [hEq] at hmul
            exact hmul
      have hchiMinDiv : (χ : ℝ) <
          min (xs : ℝ) (min (hMinus : ℝ) (1 - (hPlus : ℝ))) / 100 :=
        (lt_div_iff₀ (by norm_num : (0 : ℝ) < 100)).2 hchiMin
      exact_mod_cast hchiMinDiv
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hysPos
      · exact hysym
      · exact hymSig
      · exact hσy.2
      · exact hyd1
      · exact_mod_cast hchiSigma
  have hSub : P.IsSublinear := ⟨ys, yd, ym, rfl⟩
  have hAvailSel : AvP T (xs : ℝ) (ys : ℝ) (hPlus : ℝ) := by
    have hlt : Hpow T (xs : ℝ) (ys : ℝ) < (hPlus : ℝ) := by
      simpa [f, xs, ys, xgrid, ygrid] using hplusRlo
    exact Hpow_lt_available hlt (by exact_mod_cast hplusPos) (by linarith [hplusOne])
  have hdeepExp : (hMinus : ℝ) < Hpow T (xd : ℝ) (yd : ℝ) := by
    have hlt : (hMinus : ℝ) < f (i + 1) := hminusRhi
    simpa [f, xd, yd, xgrid, ygrid] using hlt
  have hNoDeep : ¬ AvP T (xd : ℝ) (yd : ℝ) hMinus :=
    Hpow_gt_not_available hminusPos hdeepExp
  have hDeepDisc := discAt_of_not_AvP hT
    (by exact_mod_cast hxdPos) (by exact_mod_cast hydPos) hminusPos hNoDeep
  have hDeep : P.DeepOnStage T := by
    change DiscAt T (pw (xd : ℝ)) (pw (yd : ℝ))
      (fun n => (n : ℝ) ^ (-(hMinus : ℝ)))
    exact hDeepDisc
  refine ⟨P, hValid, hSub, ?_⟩
  exact ⟨ys, yd, ym, rfl, hAvailSel, hDeep⟩

private theorem Hlin_le_of_AvL {T : Stage} {x α : ℝ} {h : ℚ}
    (hpos : 0 < h) (hav : AvL T x α h) : Hlin T x α ≤ (h : ℝ) := by
  unfold Hlin
  have hbdd : BddBelow
      ({z : ℝ | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = z ∧ AvL T x α q} ∪ {2}) := by
    refine ⟨0, ?_⟩
    intro z hz
    change z ∈ ({z : ℝ | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = z ∧ AvL T x α q} ∪ {2}) at hz
    simp only [Set.mem_union] at hz
    rcases hz with hz | hz
    · rcases hz with ⟨q, hq, hcast, _⟩
      rw [← hcast]
      exact_mod_cast hq.le
    · simp only [Set.mem_singleton_iff] at hz
      rw [hz]
      norm_num
  apply csInf_le hbdd
  exact Set.mem_union_left _ ⟨h, hpos, rfl, hav⟩

private theorem Hlin_ge_of_unavailable_below {T : Stage} {x α : ℝ} {h₀ : ℚ}
    (h₀pos : 0 < h₀) (h₀two : (h₀ : ℝ) ≤ 2)
    (hNo : ∀ q : ℚ, 0 < q → q < h₀ → ¬ AvL T x α q) :
    (h₀ : ℝ) ≤ Hlin T x α := by
  unfold Hlin
  let S : Set ℝ := {z : ℝ | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = z ∧ AvL T x α q} ∪ {2}
  have hnonempty : S.Nonempty := ⟨2, Set.mem_union_right _ (Set.mem_singleton 2)⟩
  have hbelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro z hz
    change z ∈ ({z : ℝ | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = z ∧ AvL T x α q} ∪ {2}) at hz
    simp only [Set.mem_union] at hz
    rcases hz with hz | hz
    · rcases hz with ⟨q, hq, hcast, _⟩
      rw [← hcast]
      exact_mod_cast hq.le
    · simp only [Set.mem_singleton_iff] at hz
      rw [hz]
      norm_num
  apply (le_csInf_iff hbelow hnonempty).2
  intro z hz
  change z ∈ ({z : ℝ | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = z ∧ AvL T x α q} ∪ {2}) at hz
  simp only [Set.mem_union] at hz
  rcases hz with hz | hz
  · rcases hz with ⟨q, hq, hcast, hav⟩
    by_contra hnot
    have hsmall : q < h₀ := by
      have hsmallR : (q : ℝ) < (h₀ : ℝ) := by
        rw [hcast]
        exact lt_of_not_ge hnot
      exact_mod_cast hsmallR
    exact (hNo q hq hsmall hav).elim
  · simp only [Set.mem_singleton_iff] at hz
    rw [hz]
    exact h₀two

private def HlinSet9 (T : Stage) (x : ℝ) (αmax : ℚ) : Set ℝ :=
  {z | ∃ α : ℚ, 0 < α ∧ α ≤ αmax ∧ z = Hlin T x (α : ℝ)}

private noncomputable def HlinSup9 (T : Stage) (x : ℝ) (αmax : ℚ) : ℝ :=
  sSup (HlinSet9 T x αmax)

private theorem HlinSet9_nonempty {T : Stage} {x : ℝ} {αmax : ℚ} (hα : 0 < αmax) :
    (HlinSet9 T x αmax).Nonempty := by
  exact ⟨Hlin T x (αmax : ℝ), αmax, hα, le_rfl, rfl⟩

private theorem Hlin_le_two (T : Stage) (x α : ℝ) : Hlin T x α ≤ 2 := by
  unfold Hlin
  have hbdd : BddBelow
      ({z : ℝ | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = z ∧ AvL T x α q} ∪ {2}) := by
    refine ⟨0, ?_⟩
    intro z hz
    simp only [Set.mem_union] at hz
    rcases hz with hz | hz
    · rcases hz with ⟨q, hq, hcast, _⟩
      rw [← hcast]
      exact_mod_cast hq.le
    · simp only [Set.mem_singleton_iff] at hz
      rw [hz]
      norm_num
  apply csInf_le hbdd
  exact Set.mem_union_right _ (Set.mem_singleton 2)

private theorem HlinSup9_antitone {T : Stage} {x x' : ℝ} {αmax : ℚ}
    (hαmax : 0 < αmax) (hxx : x ≤ x') : HlinSup9 T x' αmax ≤ HlinSup9 T x αmax := by
  classical
  let S := HlinSet9 T x αmax
  let S' := HlinSet9 T x' αmax
  have hne : S'.Nonempty := HlinSet9_nonempty hαmax
  have hbdd : BddAbove S := by
    refine ⟨2, ?_⟩
    intro z hz
    rcases hz with ⟨α, hα, hαmax, rfl⟩
    exact Hlin_le_two T x (α : ℝ)
  apply csSup_le hne
  intro z hz
  rcases hz with ⟨α, hα, hαmax, rfl⟩
  have hanti : Hlin T x' (α : ℝ) ≤ Hlin T x (α : ℝ) :=
    Hlin_antitone_x (T := T) (x := x) (x' := x') (α := (α : ℝ)) hxx
  exact le_trans hanti (le_csSup hbdd ⟨α, hα, hαmax, rfl⟩)

private theorem unavailableLinearWitness9 {T : Stage} (h : ¬ HLdagZero T) :
    ∃ x α e : ℚ, 0 < x ∧ x < 1 ∧ 0 < α ∧ 0 < e ∧ ¬ AvL T x α e := by
  have hnot : ¬ ∀ x α e : ℚ,
      0 < x → x < 1 → 0 < α → 0 < e → AvL T x α e := by
    simpa [HLdagZero] using h
  obtain ⟨x, hnotx⟩ := not_forall.mp hnot
  obtain ⟨α, hnotα⟩ := not_forall.mp hnotx
  obtain ⟨e, hnote⟩ := not_forall.mp hnotα
  push_neg at hnote
  exact ⟨x, α, e, hnote⟩

private theorem noPowerWidth9 {T : Stage} {e : ℚ}
    (hNo : ¬ HdagLtOne T) (he : e < 1) :
    ∃ x : ℚ, 0 < x ∧ x < 1 ∧
      ∀ y : ℚ, 0 < y → y < 1 → ¬ AvP T x y e := by
  have hnot : ¬ (∀ x : ℚ, 0 < x → x < 1 → ∃ y : ℚ,
      0 < y ∧ y < 1 ∧ AvP T x y e) := by
    intro hforall
    exact hNo ⟨e, he, hforall⟩
  obtain ⟨x, hnotx⟩ := not_forall.mp hnot
  push_neg at hnotx
  exact ⟨x, hnotx⟩

set_option maxHeartbeats 100000000 in
theorem p92_select_linear_impl (T : Stage) (hT : StabilizedOn T FamB)
    (hNoH : ¬ HdagLtOne T) (hHL : HLdagLtOne T) (hNotZero : ¬ HLdagZero T) :
    ∃ P : Params9, P.Valid ∧ P.IsLinear ∧ P.LinearSelection T := by
  classical
  rcases hHL with ⟨h1, hh1, hLinAll⟩
  let hA : ℚ := (max h1 0 + 1) / 2
  have hApos : 0 < hA := by dsimp [hA]; positivity
  have hmaxlt : max h1 0 < 1 := max_lt_iff.mpr ⟨hh1, by norm_num⟩
  have hAlt : hA < 1 := by dsimp [hA]; linarith [hmaxlt]
  have hh1A : h1 ≤ hA := by
    have hmax : max h1 0 ≤ hA := by dsimp [hA]; linarith [hmaxlt]
    exact le_trans (le_max_left _ _) hmax
  have hh1AR : (h1 : ℝ) ≤ (hA : ℝ) := by exact_mod_cast hh1A
  have hBad : ∃ x α e : ℚ, 0 < x ∧ x < 1 ∧ 0 < α ∧ 0 < e ∧ ¬ AvL T x α e :=
    unavailableLinearWitness9 hNotZero
  obtain ⟨x0, α0, e0, hx0, hx01, hα0, he0, hNo0⟩ := hBad
  have hAvailAtBad : AvL T x0 α0 hA := by
    have hav := hLinAll x0 α0 hx0 hx01 hα0
    exact AvL.mono hav le_rfl le_rfl (by exact_mod_cast hh1A)
  have he0LtA : e0 < hA := by
    by_contra hn
    have hA_le_e0 : (hA : ℝ) ≤ (e0 : ℝ) := by exact_mod_cast (le_of_not_gt hn)
    exact hNo0 (AvL.mono hAvailAtBad le_rfl le_rfl hA_le_e0)
  have hAltR : (hA : ℝ) < 1 := by exact_mod_cast hAlt
  have he0Rpos : 0 < (e0 : ℝ) := by exact_mod_cast he0
  have he0Rlt1 : (e0 : ℝ) < 1 := by exact_mod_cast (lt_trans he0LtA hAlt)
  have he0le2 : (e0 : ℝ) ≤ 2 := by linarith [he0Rlt1]
  let hB : ℚ := (hA + 1) / 2
  have hA_lt_hB : hA < hB := by dsimp [hB]; linarith [hAlt]
  have hBlt1 : hB < 1 := by dsimp [hB]; linarith [hAlt]
  obtain ⟨xB, hxB, hxB1, hNoY⟩ := noPowerWidth9 hNoH hBlt1
  let xend : ℚ := min (x0 / 2) (min (xB / 2) (min (1 / 20) ((1 - hB) / 100)))
  have hxendPos : 0 < xend := by
    dsimp [xend]
    positivity
  have hxend_x0 : xend ≤ x0 := by
    have h₁ : xend ≤ x0 / 2 := min_le_left _ _
    have h₂ : x0 / 2 ≤ x0 := by linarith [hx0]
    exact le_trans h₁ h₂
  have hxend_xB : xend ≤ xB := by
    have h₁ : xend ≤ xB / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    have h₂ : xB / 2 ≤ xB := by linarith [hxB]
    exact le_trans h₁ h₂
  have hxend_small : xend ≤ 1 / 20 := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hxend_gap : xend ≤ (1 - hB) / 100 := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hxend_lt1 : xend < 1 := by linarith [hxend_small]
  let xstart : ℚ := xend / 2
  have hxstartPos : 0 < xstart := by dsimp [xstart]; positivity
  have hxstartEnd : xstart < xend := by dsimp [xstart]; linarith [hxendPos]
  let αmax : ℚ := min (α0 / 2) (1 / 200)
  have hαmaxPos : 0 < αmax := by dsimp [αmax]; positivity
  have hαmax_le0 : αmax ≤ α0 := by
    have h₁ : αmax ≤ α0 / 2 := min_le_left _ _
    linarith [hα0]
  have hαmax_small : αmax ≤ 1 / 200 := min_le_right _ _
  have hαmax_lt : αmax < 1 / 100 := by linarith [hαmax_small]
  let cLim : ℚ := min (xstart / 100) (min (e0 / 1000) ((1 - hA) / 1000))
  have hcLimPos : 0 < cLim := by
    dsimp [cLim]
    positivity
  obtain ⟨χ, hχpos, hχlim⟩ := exists_rat_btwn hcLimPos
  have hχx : χ < xstart / 100 := lt_of_lt_of_le hχlim (min_le_left _ _)
  have hχrest : χ < min (e0 / 1000) ((1 - hA) / 1000) :=
    lt_of_lt_of_le hχlim (min_le_right _ _)
  have hχe0 : χ < e0 / 1000 := lt_of_lt_of_le hχrest (min_le_left _ _)
  have hχmargin : χ < (1 - hA) / 1000 := lt_of_lt_of_le hχrest (min_le_right _ _)
  have hχRpos : 0 < (χ : ℝ) := by exact_mod_cast hχpos
  obtain ⟨M, hMgt⟩ := exists_nat_gt (40 / (χ : ℝ))
  have hMposR : 0 < (M : ℝ) := lt_trans (by positivity) hMgt
  have hMpos : 0 < M := by exact_mod_cast hMposR
  have hMε : 1 < (M : ℝ) * ((χ : ℝ) / 40) := by
    have hratio : (40 / (χ : ℝ)) * ((χ : ℝ) / 40) = 1 := by
      field_simp [ne_of_gt (by exact_mod_cast hχpos : (0 : ℝ) < χ)]
    have hmul := mul_lt_mul_of_pos_right hMgt (by positivity : 0 < (χ : ℝ) / 40)
    rw [hratio] at hmul
    convert hmul using 1 <;> ring
  have hRange : (hA : ℝ) - (e0 : ℝ) < (M : ℝ) * ((χ : ℝ) / 40) := by
    have hltOne : (hA : ℝ) - (e0 : ℝ) < 1 := by linarith [hAltR, he0Rpos]
    linarith
  let xgrid : ℕ → ℚ := fun j => interpQ9 xstart xend M j
  let G : ℕ → ℝ := fun j => HlinSup9 T (xgrid j : ℝ) αmax
  have hxle : xstart ≤ xend := le_of_lt hxstartEnd
  have hdec : ∀ j, j < M → G (j + 1) ≤ G j := by
    intro j hj
    have hs : xgrid j < xgrid (j + 1) := by
      have heq := interpQ9_step (a := xstart) (b := xend) hxstartEnd (M := M) (j := j) hMpos
      dsimp [xgrid]
      rw [← sub_pos, heq]
      exact div_pos (sub_pos.mpr hxstartEnd) (by exact_mod_cast hMpos)
    exact HlinSup9_antitone hαmaxPos (by exact_mod_cast hs.le)
  have hGlo : ∀ j, j ≤ M → (e0 : ℝ) ≤ G j := by
    intro j hj
    have hxj := (interpQ9_bounds (a := xstart) (b := xend) hxle hMpos hj).2
    have hxjPosQ : 0 < xgrid j := lt_of_lt_of_le hxstartPos (interpQ9_bounds hxle hMpos hj).1
    have hxjLeX0 : xgrid j ≤ x0 := le_trans hxj hxend_x0
    have hαmaxLe : (αmax : ℝ) ≤ (α0 : ℝ) := by exact_mod_cast hαmax_le0
    have hNoSmall : ∀ q : ℚ, 0 < q → q < e0 → ¬ AvL T (xgrid j : ℝ) (αmax : ℝ) q := by
      intro q hq hqE hav
      have hxR : (xgrid j : ℝ) ≤ (x0 : ℝ) := by exact_mod_cast hxjLeX0
      have hqR : (q : ℝ) ≤ (e0 : ℝ) := by exact_mod_cast hqE.le
      exact hNo0 (AvL.mono hav hxR hαmaxLe hqR)
    have hlower : (e0 : ℝ) ≤ Hlin T (xgrid j : ℝ) (αmax : ℝ) :=
      Hlin_ge_of_unavailable_below he0 he0le2 hNoSmall
    have hBdd : BddAbove (HlinSet9 T (xgrid j : ℝ) αmax) := by
      refine ⟨2, ?_⟩
      intro z hz
      rcases hz with ⟨α, hα, hαle, rfl⟩
      exact Hlin_le_two T (xgrid j : ℝ) (α : ℝ)
    exact le_trans hlower (le_csSup hBdd ⟨αmax, hαmaxPos, le_rfl, rfl⟩)
  have hGhi : ∀ j, j ≤ M → G j ≤ (hA : ℝ) := by
    intro j hj
    have hxj := (interpQ9_bounds (a := xstart) (b := xend) hxle hMpos hj)
    have hxjPosQ : 0 < xgrid j := lt_of_lt_of_le hxstartPos hxj.1
    have hxjLt1 : xgrid j < 1 := lt_of_le_of_lt hxj.2 hxend_lt1
    have hUpper : ∀ z ∈ HlinSet9 T (xgrid j : ℝ) αmax, z ≤ (hA : ℝ) := by
      intro z hz
      rcases hz with ⟨α, hα, hαle, rfl⟩
      have hav1 := hLinAll (xgrid j) α hxjPosQ hxjLt1 hα
      have havA := AvL.mono hav1 le_rfl le_rfl hh1AR
      exact Hlin_le_of_AvL hApos havA
    exact csSup_le (HlinSet9_nonempty hαmaxPos) hUpper
  obtain ⟨i, hiM, hGdrop⟩ := exists_small_drop9 G M ((χ : ℝ) / 40)
    (e0 : ℝ) (hA : ℝ) hMpos (by positivity) hdec hGlo hGhi hRange
  let xs : ℚ := xgrid i
  let xd : ℚ := xgrid (i + 1)
  have hiSucc : i + 1 ≤ M := by omega
  have hxsBase : xstart ≤ xs := by
    simpa [xs, xgrid] using (interpQ9_bounds (a := xstart) (b := xend) hxle hMpos (Nat.le_of_lt hiM)).1
  have hxdEnd : xd ≤ xend := by
    simpa [xd, xgrid] using (interpQ9_bounds (a := xstart) (b := xend) hxle hMpos hiSucc).2
  have hxsPos : 0 < xs := lt_of_lt_of_le hxstartPos hxsBase
  have hxsxd : xs < xd := by
    have heq := interpQ9_step (a := xstart) (b := xend) hxstartEnd (M := M) (j := i) hMpos
    dsimp [xs, xd, xgrid]
    rw [← sub_pos, heq]
    exact div_pos (sub_pos.mpr hxstartEnd) (by exact_mod_cast hMpos)
  have hxdPos : 0 < xd := lt_trans hxsPos hxsxd
  have hxdEndR : (xd : ℝ) ≤ (xend : ℝ) := by exact_mod_cast hxdEnd
  have hxd010 : xd < 1 / 10 := by
    have hxendSmall : xend ≤ 1 / 20 := by
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hxendSmall' : xend < (1 : ℚ) / 10 := by linarith [hxendSmall]
    exact lt_of_le_of_lt hxdEnd hxendSmall'
  have hxdGap : xd < (1 - hB) / 10 := by
    have hxendGap : xend ≤ (1 - hB) / 100 := by
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hmargin : (1 - hB) / 100 < (1 - hB) / 10 := by
      have hpos : 0 < 1 - hB := sub_pos.mpr hBlt1
      nlinarith [hpos]
    exact lt_of_le_of_lt (le_trans hxdEnd hxendGap) hmargin
  have hlinUpperAt : ∀ j, j ≤ M → ∀ α : ℚ, 0 < α → α ≤ αmax →
      Hlin T (xgrid j : ℝ) (α : ℝ) ≤ (hA : ℝ) := by
    intro j hj α hα hαmax'
    have hxj := (interpQ9_bounds (a := xstart) (b := xend) hxle hMpos hj)
    have hxjPos : 0 < xgrid j := lt_of_lt_of_le hxstartPos hxj.1
    have hxjLt1 : xgrid j < 1 := lt_of_le_of_lt hxj.2 hxend_lt1
    have hav1 := hLinAll (xgrid j) α hxjPos hxjLt1 hα
    exact Hlin_le_of_AvL hApos (AvL.mono hav1 le_rfl le_rfl (by exact_mod_cast hh1A))
  have hBddXs : BddAbove (HlinSet9 T (xs : ℝ) αmax) := by
    refine ⟨(hA : ℝ), ?_⟩
    intro z hz
    rcases hz with ⟨α, hα, hαle, rfl⟩
    exact hlinUpperAt i (Nat.le_of_lt hiM) α hα hαle
  have hFShallowUpper : Hlin T (xs : ℝ) (αmax : ℝ) ≤ HlinSup9 T (xs : ℝ) αmax :=
    le_csSup hBddXs ⟨αmax, hαmaxPos, le_rfl, rfl⟩
  have hε : 0 < (χ : ℝ) / 100 := by positivity
  have hdeepSupGap : G (i + 1) - (χ : ℝ) / 100 < G (i + 1) := sub_lt_self _ hε
  have hdeepSupGap' : G (i + 1) - (χ : ℝ) / 100 <
      sSup (HlinSet9 T (xgrid (i + 1) : ℝ) αmax) := by
    simpa [G, HlinSup9, xgrid] using hdeepSupGap
  obtain ⟨z, hzSet, hzGap⟩ :=
    exists_lt_of_lt_csSup (HlinSet9_nonempty hαmaxPos) hdeepSupGap'
  rcases hzSet with ⟨αD, hαDpos, hαDle, hzEq⟩
  have hdeepLinGap : G (i + 1) - (χ : ℝ) / 100 < Hlin T (xgrid (i + 1) : ℝ) (αD : ℝ) := by
    rw [hzEq] at hzGap
    exact hzGap
  let αS : ℚ := αD / 200
  have hαSpos : 0 < αS := by dsimp [αS]; positivity
  have hαSleD : αS ≤ αD := by dsimp [αS]; nlinarith [hαDpos]
  have hαSleMax : αS ≤ αmax := le_trans hαSleD hαDle
  have hαratio : 100 * αS < αD := by dsimp [αS]; nlinarith [hαDpos]
  have hαDsmall : αD < 1 / 100 := lt_of_le_of_lt hαDle hαmax_lt
  have hFSleG : Hlin T (xs : ℝ) (αS : ℝ) ≤ G i := by
    have hBdd : BddAbove (HlinSet9 T (xs : ℝ) αmax) := hBddXs
    have hmem : Hlin T (xs : ℝ) (αS : ℝ) ∈ HlinSet9 T (xs : ℝ) αmax :=
      ⟨αS, hαSpos, hαSleMax, rfl⟩
    simpa [G, HlinSup9, xgrid] using le_csSup hBdd hmem
  have hFDeepLeShallow : Hlin T (xgrid (i + 1) : ℝ) (αD : ℝ) ≤
      Hlin T (xs : ℝ) (αS : ℝ) := by
    calc
      Hlin T (xgrid (i + 1) : ℝ) (αD : ℝ) ≤ Hlin T (xs : ℝ) (αD : ℝ) :=
        Hlin_antitone_x (T := T) (by
          have hxsxgrid : xs ≤ xgrid (i + 1) := by simpa [xd] using hxsxd.le
          exact_mod_cast hxsxgrid)
      _ ≤ Hlin T (xs : ℝ) (αS : ℝ) :=
        Hlin_antitone_α (T := T) (by exact_mod_cast hαSleD)
  obtain ⟨hPlus, hpluslo, hplushi⟩ :=
    exists_rat_btwn (show Hlin T (xs : ℝ) (αS : ℝ) <
      Hlin T (xs : ℝ) (αS : ℝ) + (χ : ℝ) / 100 by linarith [hε])
  have hplusRlo : Hlin T (xs : ℝ) (αS : ℝ) < (hPlus : ℝ) := hpluslo
  have hplusRhi : (hPlus : ℝ) < Hlin T (xs : ℝ) (αS : ℝ) + (χ : ℝ) / 100 := hplushi
  have hplusUpper : (hPlus : ℝ) < (hA : ℝ) + (χ : ℝ) / 100 := by
    linarith [hFSleG, hGhi i (Nat.le_of_lt hiM), hplusRhi]
  have hplus_lt_hB_R : (hPlus : ℝ) < (hB : ℝ) := by
    have hhB : (hB : ℝ) = ((hA : ℝ) + 1) / 2 := by norm_num [hB]
    have hχmarginR : (χ : ℝ) < (1 - (hA : ℝ)) / 1000 := by exact_mod_cast hχmargin
    have hmargin : (χ : ℝ) / 100 < (1 - (hA : ℝ)) / 2 := by nlinarith [hχmarginR]
    rw [hhB]
    linarith [hplusUpper, hmargin]
  have hplus_lt_hB : hPlus < hB := by exact_mod_cast hplus_lt_hB_R
  obtain ⟨hMinus, hminuslo, hminusHi⟩ :=
    exists_rat_btwn (show Hlin T (xgrid (i + 1) : ℝ) (αD : ℝ) - (χ : ℝ) / 100 <
      Hlin T (xgrid (i + 1) : ℝ) (αD : ℝ) by linarith [hε])
  have hminusRlo : Hlin T (xgrid (i + 1) : ℝ) (αD : ℝ) - (χ : ℝ) / 100 <
      (hMinus : ℝ) := hminuslo
  have hminusRhi : (hMinus : ℝ) < Hlin T (xgrid (i + 1) : ℝ) (αD : ℝ) := hminusHi
  have hεe0 : (χ : ℝ) / 100 < (e0 : ℝ) / 2 := by
    have hχe0R : (χ : ℝ) < (e0 : ℝ) / 1000 := by exact_mod_cast hχe0
    linarith
  have hminusHalf : (e0 : ℝ) / 2 < (hMinus : ℝ) := by
    have hdeepLow : (e0 : ℝ) ≤ G (i + 1) := hGlo (i + 1) hiSucc
    have hdeepLower : (e0 : ℝ) - (χ : ℝ) / 100 <
        Hlin T (xgrid (i + 1) : ℝ) (αD : ℝ) := by linarith [hdeepLinGap, hdeepLow]
    have hχtiny : (χ : ℝ) / 100 < (e0 : ℝ) / 100000 := by
      have hχe0R : (χ : ℝ) < (e0 : ℝ) / 1000 := by exact_mod_cast hχe0
      linarith
    linarith [hdeepLower, hminusRlo, hχtiny]
  have hminusRpos : 0 < (hMinus : ℝ) := by
    have hdeepLow : (e0 : ℝ) ≤ G (i + 1) := hGlo (i + 1) hiSucc
    linarith [hdeepLinGap, hminusRlo, hεe0, hdeepLow]
  have hminusPos : 0 < hMinus := by exact_mod_cast hminusRpos
  have hplusPos : 0 < hPlus := by
    have hdeepPos : 0 < Hlin T (xgrid (i + 1) : ℝ) (αD : ℝ) :=
      lt_trans hminusRpos hminusRhi
    have hsmallPos : 0 < Hlin T (xs : ℝ) (αS : ℝ) :=
      lt_of_lt_of_le hdeepPos hFDeepLeShallow
    exact_mod_cast lt_trans hsmallPos hplusRlo
  have hplusOneR : (hPlus : ℝ) < 1 := by
    have hχmarginR : (χ : ℝ) < (1 - (hA : ℝ)) / 1000 := by exact_mod_cast hχmargin
    have hsmall : (χ : ℝ) / 100 < 1 - (hA : ℝ) := by nlinarith [hχmarginR]
    linarith [hplusUpper]
  have hplusOne : hPlus < 1 := by exact_mod_cast hplusOneR
  have hbaseDiff : Hlin T (xs : ℝ) (αS : ℝ) -
      Hlin T (xgrid (i + 1) : ℝ) (αD : ℝ) <
      (G i - G (i + 1)) + (χ : ℝ) / 100 := by
    linarith [hFSleG, hdeepLinGap]
  have hMinusLtPlusR : (hMinus : ℝ) < (hPlus : ℝ) := by
    linarith [hplusRlo, hminusRhi, hFDeepLeShallow]
  have hMinusLtPlus : hMinus < hPlus := by exact_mod_cast hMinusLtPlusR
  have hgapR : (hPlus : ℝ) - (hMinus : ℝ) < (χ : ℝ) / 10 := by
    linarith [hplusRhi, hminusRlo, hbaseDiff, hGdrop, hχRpos]
  have hgap : hPlus - hMinus < χ / 10 := by exact_mod_cast hgapR
  have hχminus : (χ : ℝ) < (hMinus : ℝ) / 100 := by
    have hχe0R : (χ : ℝ) < (e0 : ℝ) / 1000 := by exact_mod_cast hχe0
    linarith [hminusHalf]
  have hplusMargin : (1 - (hA : ℝ)) / 2 < 1 - (hPlus : ℝ) := by
    have hχmarginR : (χ : ℝ) < (1 - (hA : ℝ)) / 1000 := by exact_mod_cast hχmargin
    linarith [hplusUpper, hχmarginR]
  have hχone : (χ : ℝ) < (1 - (hPlus : ℝ)) / 100 := by
    have hχmarginR : (χ : ℝ) < (1 - (hA : ℝ)) / 1000 := by exact_mod_cast hχmargin
    linarith [hplusMargin, hχmarginR]
  have hχxs : (χ : ℝ) < (xs : ℝ) / 100 := by
    have hxsR : (xstart : ℝ) ≤ (xs : ℝ) := by exact_mod_cast hxsBase
    have hχxR : (χ : ℝ) < (xstart : ℝ) / 100 := by exact_mod_cast hχx
    linarith
  let σ : ℚ := min (χ / 20) (xs / 20)
  have hσpos : 0 < σ := by dsimp [σ]; positivity
  have hσchi : σ < χ / 10 := by
    have hle : σ ≤ χ / 20 := min_le_left _ _
    dsimp [σ] at hle ⊢
    linarith [hχpos]
  have hσxs : σ < xs / 10 := by
    have hle : σ ≤ xs / 20 := min_le_right _ _
    dsimp [σ] at hle ⊢
    linarith [hxsPos]
  let yB : ℚ := 1 / 2
  have hyBpos : 0 < yB := by norm_num [yB]
  have hyBlt : yB < 1 := by norm_num [yB]
  have hχRpos : 0 < (χ : ℝ) := by exact_mod_cast hχpos
  have hBpos : 0 < hB := lt_trans hApos hA_lt_hB
  have hplusRpos : 0 < (hPlus : ℝ) := by exact_mod_cast hplusPos
  have hplusRlt2 : (hPlus : ℝ) ≤ 2 := by linarith [hplusOneR]
  have hAvailLin : AvL T (xs : ℝ) (αS : ℝ) (hPlus : ℝ) := by
    have hlt : Hlin T (xs : ℝ) (αS : ℝ) < (hPlus : ℝ) := hplusRlo
    exact Hlin_lt_available hlt hplusRpos hplusRlt2
  have hNoBroad : ¬ AvP T (xd : ℝ) (yB : ℝ) hB := by
    intro hav
    have hxdB : (xd : ℝ) ≤ (xB : ℝ) := by
      have hxdendR : (xd : ℝ) ≤ (xend : ℝ) := hxdEndR
      have hxendBR : (xend : ℝ) ≤ (xB : ℝ) := by exact_mod_cast hxend_xB
      exact le_trans hxdendR hxendBR
    exact hNoY yB hyBpos hyBlt
      (AvP.mono hav hxdB le_rfl le_rfl)
  have hBroadDisc := discAt_of_not_AvP hT
    (by exact_mod_cast hxdPos) (by norm_num [yB]) hBpos hNoBroad
  have hNoDeepLin : ¬ AvL T (xd : ℝ) (αD : ℝ) hMinus :=
    Hlin_gt_not_available hminusPos (by exact_mod_cast hminusRhi)
  have hDeepDisc := discAt_of_not_AvL hT
    (by exact_mod_cast hxdPos) (by exact_mod_cast hαDpos) hminusPos hNoDeepLin
  have hxdGapR : (xd : ℝ) < (1 - (hPlus : ℝ)) / 10 := by
    have hxdendR : (xd : ℝ) ≤ (xend : ℝ) := hxdEndR
    have hxendgapR : (xend : ℝ) ≤ (1 - (hB : ℝ)) / 100 := by exact_mod_cast hxend_gap
    have hPlusB : (hPlus : ℝ) < (hB : ℝ) := by exact_mod_cast hplus_lt_hB_R
    have hBltR : (hB : ℝ) < 1 := by exact_mod_cast hBlt1
    have hpositive : 0 < 1 - (hB : ℝ) := sub_pos.mpr hBltR
    linarith
  have hxdGap' : xd < (1 - hPlus) / 10 := by exact_mod_cast hxdGapR
  let P : Params9 := ⟨xs, xd, hMinus, hPlus, σ, χ, .lin αS αD hB yB⟩
  have hValid : P.Valid := by
    dsimp [P, Params9.Valid]
    refine ⟨⟨hxsPos, hxsxd, hxd010⟩, ⟨hminusPos, hMinusLtPlus, hplusOne⟩,
      hxdGap', ⟨hσpos, hσxs⟩, ⟨hχpos, ?_⟩, hgap, ?_⟩
    · have hchiMin : (χ : ℝ) * 100 <
          min (xs : ℝ) (min (hMinus : ℝ) (1 - (hPlus : ℝ))) := by
        apply lt_min
        · have hmul := mul_lt_mul_of_pos_right hχxs (by norm_num : 0 < (100 : ℝ))
          have hEq : ((xs : ℝ) / 100) * 100 = xs := by ring
          rw [hEq] at hmul
          exact hmul
        · apply lt_min
          · have hmul := mul_lt_mul_of_pos_right hχminus (by norm_num : 0 < (100 : ℝ))
            have hEq : ((hMinus : ℝ) / 100) * 100 = hMinus := by ring
            rw [hEq] at hmul
            exact hmul
          · have hmul := mul_lt_mul_of_pos_right hχone (by norm_num : 0 < (100 : ℝ))
            have hEq : ((1 - (hPlus : ℝ)) / 100) * 100 = 1 - (hPlus : ℝ) := by ring
            rw [hEq] at hmul
            exact hmul
      have hchiMinDiv : (χ : ℝ) <
          min (xs : ℝ) (min (hMinus : ℝ) (1 - (hPlus : ℝ))) / 100 :=
        (lt_div_iff₀ (by norm_num : (0 : ℝ) < 100)).2 hchiMin
      exact_mod_cast hchiMinDiv
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp [αS]
        positivity
      · exact hαratio
      · exact hαDsmall
      · exact hσchi
      · exact hplus_lt_hB
      · exact hBlt1
      · norm_num [yB]
      · norm_num [yB]
  have hLinear : P.IsLinear := ⟨αS, αD, hB, yB, rfl⟩
  have hDeep : P.DeepOnStage T := by
    change DiscAt T (pw (xd : ℝ)) (lw (αD : ℝ))
      (fun n => (n : ℝ) ^ (-(hMinus : ℝ)))
    exact hDeepDisc
  have hBroad : P.BroadOnStage T := by
    change DiscAt T (pw (xd : ℝ)) (pw (yB : ℝ))
      (fun n => (n : ℝ) ^ (-(hB : ℝ)))
    exact hBroadDisc
  refine ⟨P, hValid, hLinear, ?_⟩
  exact ⟨αS, αD, hB, yB, rfl, hAvailLin, hDeep, hBroad⟩

theorem preparedAvailable9 {P : Params9} {κ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (hP : P.Valid) (hκ : 0 < κ) (hN : 0 < N)
    (hAvail : AvailableAt κ P.BiasProperty n N E X Y) :
    ∃ G : Colour, AvailableAt (κ / 2) (PreparedBias9 P G).toPatch n N E X Y := by
  classical
  let Pos : PatchProp := (PreparedBias9 P true).toPatch
  let Neg : PatchProp := (PreparedBias9 P false).toPatch
  have hsub : P.BiasProperty n N E ⊆ Pos n N E ∪ Neg n N E := by
    intro AB hAB
    cases hp : P.case with
    | sub yS yD yM =>
        rw [Params9.BiasProperty, hp] at hAB
        rcases hAB with ⟨μ, ν, hμ, hν, hQ⟩
        change μ.WidthLE ((n : ℝ) ^ (P.xS : ℝ)) ∧
          ν.WidthLE ((n : ℝ) ^ (yS : ℝ)) ∧
          (n : ℝ) ^ (-(P.hPlus : ℝ)) ≤ |dens E true μ ν - 1 / 2| at hQ
        rcases hQ with ⟨hμw, hνw, hbias⟩
        obtain ⟨G, μ', hμ'A, hμ'W, hν'W, hrows⟩ :=
          trimBiasPair9 hP hN μ ν hμ hν hμw (by simpa [Params9.Ss, hp] using hνw) hbias
        have hPrep : PreparedBias9 P G n N E μ' ν := by
          exact ⟨hμ'W, hν'W, hrows⟩
        change AB ∈ Pos n N E ∪ Neg n N E
        cases G with
        | false =>
            apply Or.inr
            exact ⟨μ', ν, hμ'A, hν, hPrep⟩
        | true =>
            apply Or.inl
            exact ⟨μ', ν, hμ'A, hν, hPrep⟩
    | lin αS αD hB yB =>
        rw [Params9.BiasProperty, hp] at hAB
        rcases hAB with ⟨μ, ν, hμ, hν, hQ⟩
        change μ.WidthLE ((n : ℝ) ^ (P.xS : ℝ)) ∧
          ν.WidthLE ((αS : ℝ) * n) ∧
          (n : ℝ) ^ (-(P.hPlus : ℝ)) ≤ |dens E true μ ν - 1 / 2| at hQ
        rcases hQ with ⟨hμw, hνw, hbias⟩
        obtain ⟨G, μ', hμ'A, hμ'W, hν'W, hrows⟩ :=
          trimBiasPair9 hP hN μ ν hμ hν hμw (by simpa [Params9.Ss, hp] using hνw) hbias
        have hPrep : PreparedBias9 P G n N E μ' ν := by
          exact ⟨hμ'W, hν'W, hrows⟩
        change AB ∈ Pos n N E ∪ Neg n N E
        cases G with
        | false =>
            apply Or.inr
            exact ⟨μ', ν, hμ'A, hν, hPrep⟩
        | true =>
            apply Or.inl
            exact ⟨μ', ν, hμ'A, hν, hPrep⟩
  have hUnion : AvailableAt κ (fun n N E => Pos n N E ∪ Neg n N E) n N E X Y :=
    AvailableAt.mono hsub hAvail
  rcases AvailableAt.union hUnion with hPos | hNeg
  · exact ⟨true, by simpa [Pos] using hPos⟩
  · exact ⟨false, by simpa [Neg] using hNeg⟩

theorem p92_patch_preparation_impl {P : Params9} {κ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (hP : P.Valid) (hκ : 0 < κ) (hN : 0 < N)
    (hAvail : AvailableAt κ P.BiasProperty n N E X Y) :
    ∃ G : Colour, ∃ M : TagMix N,
      M.Balanced (8 / κ) ∧
      (∀ i, 0 < M.Λ i → (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
        (M.μ i).WidthLE ((n : ℝ) ^ (P.xS : ℝ) +
          (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) ∧
        (M.ν i).WidthLE (P.Ss (n : ℝ)) ∧
        ∀ x, (M.μ i).w x ≠ 0 →
          1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x (M.ν i)) := by
  obtain ⟨G, hA⟩ := preparedAvailable9 hP hκ hN hAvail
  have hκhalf : 0 < κ / 2 := by positivity
  obtain ⟨M, hBal, hWit⟩ := L3_3a_consumed
    (κ / 2) n N E X Y (PreparedBias9 P G) hκhalf hA
  have hBal' : M.Balanced (8 / κ) := by
    have hscale : 4 / (κ / 2) = 8 / κ := by field_simp [ne_of_gt hκ]; ring
    rw [← hscale]
    exact hBal
  refine ⟨G, M, hBal', ?_⟩
  intro i hi
  rcases hWit i hi with ⟨hμsupp, hνsupp, hQ⟩
  exact ⟨hμsupp, hνsupp, hQ.1, hQ.2.1, hQ.2.2⟩

end HypercubeRamsey
