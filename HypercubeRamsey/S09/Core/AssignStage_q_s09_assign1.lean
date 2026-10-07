import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.S09.Core.Scales
import HypercubeRamsey.S09.Core.Experiment

namespace HypercubeRamsey.Lane_q_s09_assign1

open Filter
open OAI.HypercubeRamsey
open scoped BigOperators

/-- A Hamming ball of radius `r` in a Boolean cube has at most `(d + 1)^r` vertices. -/
theorem hammingBallCardBound9 {d r : ℕ} (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist v u ≤ r)).card ≤
      (d + 1) ^ r := by
  classical
  let B := Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist v u ≤ r)
  let support : CubeVertex d → Finset (Fin d) := fun u =>
    Finset.univ.filter (fun i => u i ≠ v i)
  have hsupportDist (u : CubeVertex d) : (support u).card = _root_.hammingDist v u := by
    simp [support, _root_.hammingDist, ne_comm]
  have hinj : Set.InjOn support (B : Set (CubeVertex d)) := by
    intro x hx y hy hxy
    funext i
    have hiff : x i ≠ v i ↔ y i ≠ v i := by
      have h := congrArg (fun s : Finset (Fin d) => i ∈ s) hxy
      simpa [support] using h
    cases hv : v i <;> cases hxv : x i <;> cases hyv : y i <;> simp_all
  let Q := (Finset.univ : Finset (Fin d)).powerset.filter (fun s => s.card ≤ r)
  have hsubset : B.image support ⊆ Q := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    have hu' : u ∈ B := by simpa [B] using hu
    have hdistle : _root_.hammingDist v u ≤ r := (Finset.mem_filter.mp hu').2
    rw [hsupportDist]
    exact hdistle
  have hcard : B.card ≤ Q.card := by
    calc
      B.card = (B.image support).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Q.card := Finset.card_le_card hsubset
  have hQsum : Q.card =
      ∑ k ∈ Finset.range (d + 1), if k ≤ r then Nat.choose d k else 0 := by
    calc
      Q.card = ∑ s ∈ (Finset.univ : Finset (Fin d)).powerset,
          if s.card ≤ r then 1 else 0 := by
        simpa [Q] using
          (Finset.natCast_card_filter (R := ℕ)
            (p := fun s : Finset (Fin d) => s.card ≤ r)
            (s := (Finset.univ : Finset (Fin d)).powerset))
      _ = ∑ k ∈ Finset.range (d + 1),
          Nat.choose d k * (if k ≤ r then 1 else 0) := by
        simpa [Fintype.card_fin, nsmul_eq_mul] using
          (Finset.sum_powerset_apply_card
            (f := fun k : ℕ => if k ≤ r then (1 : ℕ) else 0)
            (x := (Finset.univ : Finset (Fin d))))
      _ = _ := by simp
  let q := min r d
  have hQsum' : Q.card =
      ∑ k ∈ Finset.range (d + 1), if k ≤ q then Nat.choose d k else 0 := by
    rw [hQsum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkd : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    by_cases hkr : k ≤ r
    · have hkq : k ≤ q := by dsimp [q]; omega
      simp [hkr, hkq]
    · have hkq : ¬ k ≤ q := by dsimp [q]; omega
      simp [hkr, hkq]
  have hterm (k : ℕ) (hkd : k ≤ d) (hkq : k ≤ q) :
      Nat.choose d k ≤ Nat.choose q k * d ^ k := by
    have hchoose : Nat.choose d k ≤ d ^ k := Nat.choose_le_pow d k
    have hpos : 1 ≤ Nat.choose q k := Nat.succ_le_iff.mpr (Nat.choose_pos hkq)
    calc
      Nat.choose d k ≤ d ^ k := hchoose
      _ = 1 * d ^ k := by simp
      _ ≤ Nat.choose q k * d ^ k := Nat.mul_le_mul_right _ hpos
  have hsumle : Q.card ≤
      ∑ k ∈ Finset.range (d + 1), Nat.choose q k * d ^ k := by
    rw [hQsum']
    apply Finset.sum_le_sum
    intro k hk
    by_cases hkq : k ≤ q
    · simp only [if_pos hkq]
      exact hterm k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hkq
    · have hqk : q < k := by omega
      simp [hkq, Nat.choose_eq_zero_of_lt hqk]
  have hsumEq :
      (∑ k ∈ Finset.range (d + 1), Nat.choose q k * d ^ k) =
        ∑ k ∈ Finset.range (q + 1), Nat.choose q k * d ^ k := by
    have hfilter :
        (Finset.range (d + 1)).filter (fun k => k ≤ q) = Finset.range (q + 1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    calc
      (∑ k ∈ Finset.range (d + 1), Nat.choose q k * d ^ k) =
          ∑ k ∈ Finset.range (d + 1),
            if k ≤ q then Nat.choose q k * d ^ k else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hqk : k ≤ q
              · simp [hqk]
              · have hqk' : q < k := by omega
                simp [hqk, Nat.choose_eq_zero_of_lt hqk']
      _ = ∑ k ∈ (Finset.range (d + 1)).filter (fun k => k ≤ q),
            Nat.choose q k * d ^ k := by simp [Finset.sum_filter]
      _ = ∑ k ∈ Finset.range (q + 1), Nat.choose q k * d ^ k := by rw [hfilter]
  have hbin :
      (∑ k ∈ Finset.range (q + 1), Nat.choose q k * d ^ k) = (d + 1) ^ q := by
    simpa [mul_comm] using (add_pow d 1 q).symm
  calc
    B.card ≤ Q.card := hcard
    _ ≤ ∑ k ∈ Finset.range (d + 1), Nat.choose q k * d ^ k := hsumle
    _ = ∑ k ∈ Finset.range (q + 1), Nat.choose q k * d ^ k := hsumEq
    _ = (d + 1) ^ q := hbin
    _ ≤ (d + 1) ^ r := pow_le_pow_right' (by omega) (min_le_left r d)

open Classical in
/-- A parity subtype contains no more points in a Hamming ball than the full cube. -/
theorem subtypeHammingBallCardBound9 {n : ℕ} (p : CubeVertex n → Prop)
    [Fintype {v : CubeVertex n // p v}] (v : CubeVertex n) (r : ℕ) :
    (Finset.univ.filter (fun x : {x : CubeVertex n // p x} =>
      _root_.hammingDist v x.1 ≤ r)).card ≤ (n + 1) ^ r := by
  let C := Finset.univ.filter (fun x : {x : CubeVertex n // p x} =>
    _root_.hammingDist v x.1 ≤ r)
  let B := Finset.univ.filter (fun x : CubeVertex n => _root_.hammingDist v x ≤ r)
  have hsubset : C.image Subtype.val ⊆ B := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨x', hx', rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx').2⟩
  have himage : (C.image Subtype.val).card = C.card :=
    Finset.card_image_of_injective C Subtype.val_injective
  calc
    C.card = (C.image Subtype.val).card := himage.symm
    _ ≤ B.card := Finset.card_le_card hsubset
    _ ≤ (n + 1) ^ r := hammingBallCardBound9 (r := r) v

/-- The Hamming distance on a cube is at most the sum of its special and residual coordinate distances. -/
theorem hammingDistSplitBound9 {m n : ℕ} (u v : CubeVertex n) :
    _root_.hammingDist u v ≤
      _root_.hammingDist (specialWord9 m u) (specialWord9 m v) +
        _root_.hammingDist (residualWord9 m u) (residualWord9 m v) := by
  classical
  let D : Finset (Fin n) := Finset.univ.filter (fun i => u i ≠ v i)
  let S : Finset (Fin m) :=
    Finset.univ.filter (fun i => specialWord9 m u i ≠ specialWord9 m v i)
  let R : Finset (Fin (n - m)) :=
    Finset.univ.filter (fun i => residualWord9 m u i ≠ residualWord9 m v i)
  let D' := {i : Fin n // i ∈ D}
  let S' := {i : Fin m // i ∈ S}
  let R' := {i : Fin (n - m) // i ∈ R}
  let f : D' → S' ⊕ R' := fun i =>
    if hi : i.1.val < m then
      let j : Fin m := ⟨i.1.val, hi⟩
      have hdiff : u i.1 ≠ v i.1 := (Finset.mem_filter.mp i.2).2
      have hj : j ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [j, specialWord9] using hdiff
      Sum.inl ⟨j, hj⟩
    else
      let j : Fin (n - m) := ⟨i.1.val - m, by omega⟩
      have hidx : (⟨m + j.val, by omega⟩ : Fin n) = i.1 := by
        apply Fin.ext
        dsimp [j]
        omega
      have hdiff : residualWord9 m u j ≠ residualWord9 m v j := by
        have hfull : u (⟨m + j.val, by omega⟩ : Fin n) ≠
            v (⟨m + j.val, by omega⟩ : Fin n) := by
          simpa [hidx] using (Finset.mem_filter.mp i.2).2
        simpa [residualWord9] using hfull
      have hj : j ∈ R := by simpa [R, hdiff]
      Sum.inr ⟨j, hj⟩
  have hinj : Function.Injective f := by
    intro i i' h
    by_cases hi : i.1.val < m <;> by_cases hi' : i'.1.val < m
    · have hsum := h
      simp [f, hi, hi'] at hsum
      have hval : i.1.val = i'.1.val := by
        have hh := congrArg (fun q : S' ⊕ R' => q.elim (fun s => s.1.val) (fun _ => 0)) h
        simpa [f, hi, hi'] using hh
      apply Subtype.ext
      exact Fin.ext hval
    · simp [f, hi, hi'] at h
    · simp [f, hi, hi'] at h
    · have hval : i.1.val - m = i'.1.val - m := by
        have hh := congrArg (fun q : S' ⊕ R' => q.elim (fun _ => 0) (fun r => r.1.val)) h
        simpa [f, hi, hi'] using hh
      have hval' : i.1.val = i'.1.val := by omega
      apply Subtype.ext
      exact Fin.ext hval'
  have hcard' : Fintype.card D' ≤ Fintype.card S' + Fintype.card R' := by
    calc
      Fintype.card D' ≤ Fintype.card (S' ⊕ R') :=
        Fintype.card_le_of_injective f hinj
      _ = Fintype.card S' + Fintype.card R' := Fintype.card_sum
  have hcard : D.card ≤ S.card + R.card := by
    simpa [D', S', R'] using hcard'
  have hD : _root_.hammingDist u v = D.card := by
    change (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = D.card
    rfl
  have hS : _root_.hammingDist (specialWord9 m u) (specialWord9 m v) = S.card := by
    change (Finset.univ.filter
      (fun i : Fin m => specialWord9 m u i ≠ specialWord9 m v i)).card = S.card
    rfl
  have hR : _root_.hammingDist (residualWord9 m u) (residualWord9 m v) = R.card := by
    change (Finset.univ.filter
      (fun i : Fin (n - m) => residualWord9 m u i ≠ residualWord9 m v i)).card = R.card
    rfl
  rw [hD, hS, hR]
  exact hcard

open Classical in
/-- Each special-coordinate slice contains at most all residual words worth of odd sites. -/
theorem oddSliceFiberCardBound9 {n m : ℕ} (hm : m ≤ n) (z : CubeVertex m) :
    Fintype.card {b : OddSites9 n // specialWord9 m b.1 = z} ≤ 2 ^ (n - m) := by
  let f : {b : OddSites9 n // specialWord9 m b.1 = z} → CubeVertex (n - m) :=
    fun b => residualWord9 m b.1.1
  have hinj : Function.Injective f := by
    intro b b' h
    apply Subtype.ext
    apply Subtype.ext
    have hspecial : specialWord9 m b.1.1 = specialWord9 m b'.1.1 := b.2.trans b'.2.symm
    have hresidual : residualWord9 m b.1.1 = residualWord9 m b'.1.1 := h
    funext i
    by_cases hi : (i : ℕ) < m
    · have hs := congrFun hspecial (⟨i.val, hi⟩ : Fin m)
      simpa [specialWord9, hi] using hs
    · let j : Fin (n - m) := ⟨i.val - m, by omega⟩
      have hidx : (⟨m + j.val, by omega⟩ : Fin n) = i := by
        apply Fin.ext
        dsimp [j]
        omega
      have hr := congrFun hresidual j
      simpa [residualWord9, hidx, j] using hr
  calc
    Fintype.card {b : OddSites9 n // specialWord9 m b.1 = z} ≤ Fintype.card (CubeVertex (n - m)) :=
      Fintype.card_le_of_injective f hinj
    _ = 2 ^ (n - m) := by simp [OAI.HypercubeRamsey.card_cubeVertex]

open Classical in
/-- The odd parity class has half the vertices of every positive-dimensional cube. -/
theorem oddSitesCardPow9 {n : ℕ} (hn : 0 < n) :
    Fintype.card (OddSites9 n) = 2 ^ (n - 1) := by
  let j : Fin n := ⟨0, by omega⟩
  let flip : CubeVertex n → CubeVertex n := fun v => cubeFlip v j
  have hinv (v : CubeVertex n) : flip (flip v) = v := by
    funext i
    by_cases hi : i = j
    · subst i
      simp [flip, cubeFlip]
    · simp [flip, cubeFlip, hi]
  let e : OddSites9 n ≃ EvenSites9 n :=
    { toFun := fun b => (⟨flip b.1, (cubeFlip_parity b.1 j).2 b.2⟩ : EvenSites9 n)
      invFun := fun v => (⟨flip v.1, by
        intro hflip
        exact ((cubeFlip_parity v.1 j).mp hflip) v.2⟩ : OddSites9 n)
      left_inv := fun b => by
        apply Subtype.ext
        exact hinv b.1
      right_inv := fun v => by
        apply Subtype.ext
        exact hinv v.1 }
  have hEven : Fintype.card (EvenSites9 n) = (evenRoleSet n).card := by
    simp [EvenSites9, evenRoleSet, Fintype.card_subtype]
  calc
    Fintype.card (OddSites9 n) = Fintype.card (EvenSites9 n) := Fintype.card_congr e
    _ = (evenRoleSet n).card := hEven
    _ = 2 ^ (n - 1) := (parity_class_card hn).1

open Classical in
/-- A vertex is determined by its special and residual coordinate words. -/
theorem specialResidualEq9 {n m : ℕ} (hm : m ≤ n) (u v : CubeVertex n)
    (hs : specialWord9 m u = specialWord9 m v)
    (hr : residualWord9 m u = residualWord9 m v) : u = v := by
  funext i
  by_cases hi : (i : ℕ) < m
  · have h := congrFun hs (⟨i.val, hi⟩ : Fin m)
    simpa [specialWord9, hi] using h
  · let j : Fin (n - m) := ⟨i.val - m, by omega⟩
    have hidx : (⟨m + j.val, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    have h := congrFun hr j
    simpa [residualWord9, hidx, j] using h

open Classical in
/-- Averaging a nonnegative slice load over odd vertices costs at most a factor two from the uniform slice
average, since every odd vertex embeds into the product of its special and residual words. -/
theorem oddSpecialAverageBound9 {n m : ℕ} (hm : m ≤ n) (hn : 0 < n)
    (g : CubeVertex m → ℝ) (hg : ∀ z, 0 ≤ g z) :
    (Fintype.card (OddSites9 n) : ℝ)⁻¹ *
        ∑ b : OddSites9 n, g (specialWord9 m b.1) ≤
      2 * (Fintype.card (CubeVertex m) : ℝ)⁻¹ * ∑ z, g z := by
  let ψ : OddSites9 n → CubeVertex m × CubeVertex (n - m) := fun b =>
    (specialWord9 m b.1, residualWord9 m b.1)
  have hψ : Function.Injective ψ := by
    intro b b' h
    apply Subtype.ext
    exact specialResidualEq9 hm b.1 b'.1 (congrArg Prod.fst h) (congrArg Prod.snd h)
  let A : Finset (CubeVertex m × CubeVertex (n - m)) := Finset.univ.image ψ
  have hsumImage :
      (∑ b : OddSites9 n, g (specialWord9 m b.1)) = ∑ q ∈ A, g q.1 := by
    dsimp [A, ψ]
    symm
    exact Finset.sum_image hψ.injOn
  have hsumLe :
      (∑ b : OddSites9 n, g (specialWord9 m b.1)) ≤
        ∑ q : CubeVertex m × CubeVertex (n - m), g q.1 := by
    rw [hsumImage]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    intro q hq hqA
    exact hg q.1
  have hfull :
      (∑ q : CubeVertex m × CubeVertex (n - m), g q.1) =
        (Fintype.card (CubeVertex (n - m)) : ℝ) * ∑ z, g z := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ z, ∑ r : CubeVertex (n - m), g z =
          ∑ z, g z * (Fintype.card (CubeVertex (n - m)) : ℝ) := by
            apply Finset.sum_congr rfl
            intro z hz
            simp
            ring
      _ = (Fintype.card (CubeVertex (n - m)) : ℝ) * ∑ z, g z := by
            calc
              ∑ z, g z * (Fintype.card (CubeVertex (n - m)) : ℝ) =
                  (∑ z, g z) * (Fintype.card (CubeVertex (n - m)) : ℝ) := by
                    rw [Finset.sum_mul]
              _ = (Fintype.card (CubeVertex (n - m)) : ℝ) * ∑ z, g z := by ring
  have hOdd : Fintype.card (OddSites9 n) = 2 ^ (n - 1) := oddSitesCardPow9 hn
  have hSlice : Fintype.card (CubeVertex m) = 2 ^ m := by simp
  have hResidual : Fintype.card (CubeVertex (n - m)) = 2 ^ (n - m) := by simp
  have hProduct :
      (Fintype.card (CubeVertex (n - m)) : ℝ) *
        (Fintype.card (CubeVertex m) : ℝ) =
          2 * (Fintype.card (OddSites9 n) : ℝ) := by
    rw [hResidual, hSlice, hOdd]
    push_cast
    calc
      (2 : ℝ) ^ (n - m) * 2 ^ m = (2 : ℝ) ^ ((n - m) + m) := by rw [← pow_add]
      _ = (2 : ℝ) ^ n := by rw [Nat.sub_add_cancel hm]
      _ = (2 : ℝ) ^ (n - 1 + 1) := by
        have hnpow : n = n - 1 + 1 := by omega
        conv_lhs => rw [hnpow]
      _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (n - 1) := by
        ring
  have hOddPos : 0 < (Fintype.card (OddSites9 n) : ℝ) := by rw [hOdd]; positivity
  have hSlicePos : 0 < (Fintype.card (CubeVertex m) : ℝ) := by rw [hSlice]; positivity
  have hfactor :
      (Fintype.card (OddSites9 n) : ℝ)⁻¹ *
          (Fintype.card (CubeVertex (n - m)) : ℝ) =
        2 * (Fintype.card (CubeVertex m) : ℝ)⁻¹ := by
    field_simp
    nlinarith [hProduct]
  calc
    (Fintype.card (OddSites9 n) : ℝ)⁻¹ *
        ∑ b : OddSites9 n, g (specialWord9 m b.1) ≤
      (Fintype.card (OddSites9 n) : ℝ)⁻¹ *
        ((Fintype.card (CubeVertex (n - m)) : ℝ) * ∑ z, g z) :=
          mul_le_mul_of_nonneg_left (hsumLe.trans_eq hfull) (inv_nonneg.mpr hOddPos.le)
    _ = 2 * (Fintype.card (CubeVertex m) : ℝ)⁻¹ * ∑ z, g z := by
      rw [← mul_assoc, hfactor]

open Classical in
/-- The valid deep width is eventually at most one tenth of the ambient dimension. -/
theorem deepWidthSmall9 (P : Params9) (hP : Params9.Valid P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, P.Sd (n : ℝ) ≤ (n : ℝ) / 10 := by
  rcases hP with ⟨_, _, _, _, _, _, hcase⟩
  cases hc : P.case with
  | sub yS yD yM =>
      rw [hc] at hcase
      rcases hcase with ⟨_, _, _, _, hyD, _⟩
      let α : ℝ := (yD : ℝ)
      have hα : α < 1 := by
        dsimp [α]
        exact_mod_cast hyD
      have hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ (α - 1)) atTop (nhds 0) := by
        have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
        simpa [Function.comp_def, α, neg_sub] using h
      obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
        (hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10)))
      refine ⟨max 1 n₁, ?_⟩
      intro n hn
      have hn₀ : 1 ≤ n := le_trans (le_max_left _ _) hn
      have hn₁' : n₁ ≤ n := le_trans (le_max_right _ _) hn
      have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn₀)
      have hpow : (n : ℝ) ^ α = (n : ℝ) * (n : ℝ) ^ (α - 1) := by
        calc
          (n : ℝ) ^ α = (n : ℝ) ^ (1 + (α - 1)) := by congr 1 <;> ring
          _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (α - 1) := Real.rpow_add hnR 1 (α - 1)
          _ = (n : ℝ) * (n : ℝ) ^ (α - 1) := by simp
      have hsd : P.Sd (n : ℝ) = (n : ℝ) ^ α := by simp [Params9.Sd, hc, α]
      rw [hsd, hpow]
      have hsmall := hn₁ n hn₁'
      have hsmall' : (n : ℝ) * (n : ℝ) ^ (α - 1) < (n : ℝ) / 10 := by
        have hmul := mul_lt_mul_of_pos_left hsmall hnR
        nlinarith
      exact hsmall'.le
  | lin αS αD hB yB =>
      rw [hc] at hcase
      rcases hcase with ⟨_, _, hαD, _, _, _, _, _⟩
      refine ⟨1, ?_⟩
      intro n hn
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hsd : P.Sd (n : ℝ) = (αD : ℝ) * (n : ℝ) := by simp [Params9.Sd, hc]
      rw [hsd]
      have hαD' : (αD : ℝ) < 1 / 100 := by
        calc
          (αD : ℝ) < ((1 / 100 : ℚ) : ℝ) :=
            (Rat.cast_lt (K := ℝ) (p := αD) (q := (1 / 100 : ℚ))).2 hαD
          _ = 1 / 100 := by norm_num
      nlinarith

open Classical in
/-- The logarithmic dimension factor is eventually at most one hundredth of the dimension. -/
theorem natLogSmall9 :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Real.log (n : ℝ) ≤ (n : ℝ) / 100 := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)))
  refine ⟨max 1 n₁, ?_⟩
  intro n hn
  have hn₀ : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn₁' : n₁ ≤ n := le_trans (le_max_right _ _) hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn₀)
  have hratio := hn₁ n hn₁'
  have hlog : Real.log (n : ℝ) / (n : ℝ) < 1 / 100 := hratio
  have hlog' : Real.log (n : ℝ) < (1 / 100 : ℝ) * (n : ℝ) := (div_lt_iff₀ hnR).1 hlog
  nlinarith

open Classical in
/-- Any fixed positive multiple of `n` eventually dominates `log n`. -/
theorem natLogLeConst9 (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Real.log (n : ℝ) ≤ c * (n : ℝ) := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds hc))
  refine ⟨max 1 n₁, ?_⟩
  intro n hn
  have hn₀ : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn₁' : n₁ ≤ n := le_trans (le_max_right _ _) hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn₀)
  have hratio : Real.log (n : ℝ) / (n : ℝ) < c := hn₁ n hn₁'
  have hlog : Real.log (n : ℝ) < c * (n : ℝ) := by
    have hh := (div_lt_iff₀ hnR).1 hratio
    nlinarith
  exact hlog.le

open Classical in
/-- A declared near-neighborhood of an odd row has at most `(n+1)^(4r+12)` sites. -/
theorem oddNearCardBound9 (P : Params9) (n : ℕ) (b : OddSites9 n) :
    (Finset.univ.filter (fun b' : OddSites9 n => siteNear9 P n b.1 b'.1)).card ≤
      (n + 1) ^ (4 * P.radius n + 12) := by
  classical
  let C := Finset.univ.filter (fun b' : OddSites9 n => siteNear9 P n b.1 b'.1)
  let B := Finset.univ.filter (fun w : CubeVertex n =>
    _root_.hammingDist b.1 w ≤ 4 * P.radius n + 12)
  have hsubset : C.image Subtype.val ⊆ B := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨b', hb', rfl⟩
    have hnear := (Finset.mem_filter.mp hb').2
    have hsplit := hammingDistSplitBound9 (m := P.m n) b.1 b'.1
    unfold siteNear9 at hnear
    have hd : _root_.hammingDist b.1 b'.1 ≤ 4 * P.radius n + 12 := by
      calc
        _root_.hammingDist b.1 b'.1 ≤
            _root_.hammingDist (specialWord9 (P.m n) b.1) (specialWord9 (P.m n) b'.1) +
              _root_.hammingDist (residualWord9 (P.m n) b.1) (residualWord9 (P.m n) b'.1) := hsplit
        _ ≤ 4 + (4 * P.radius n + 8) := Nat.add_le_add hnear.1 hnear.2
        _ = 4 * P.radius n + 12 := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
  have himage : (C.image Subtype.val).card = C.card :=
    Finset.card_image_of_injective C Subtype.val_injective
  calc
    C.card = (C.image Subtype.val).card := himage.symm
    _ ≤ B.card := Finset.card_le_card hsubset
    _ ≤ (n + 1) ^ (4 * P.radius n + 12) :=
      hammingBallCardBound9 (r := 4 * P.radius n + 12) b.1


/-- Restricting to the special coordinates cannot increase Hamming distance. -/
theorem hammingDistSpecialLe9 {m n : ℕ} (u v : CubeVertex n) :
    _root_.hammingDist (specialWord9 m u) (specialWord9 m v) ≤ _root_.hammingDist u v := by
  classical
  let S : Finset (Fin m) :=
    Finset.univ.filter (fun i => specialWord9 m u i ≠ specialWord9 m v i)
  let D : Finset (Fin n) := Finset.univ.filter (fun i => u i ≠ v i)
  let S' := {i : Fin m // i ∈ S}
  let D' := {i : Fin n // i ∈ D}
  have hindex (j : S') : j.1.val < n := by
    by_contra hnot
    have hU : specialWord9 m u j.1 = false := by simp [specialWord9, hnot]
    have hV : specialWord9 m v j.1 = false := by simp [specialWord9, hnot]
    exact (Finset.mem_filter.mp j.2).2 (by simp [hU, hV])
  let f : S' → D' := fun j =>
    ⟨⟨j.1.val, hindex j⟩, by
      have hdiff := (Finset.mem_filter.mp j.2).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [specialWord9, hindex j] using hdiff⟩⟩
  have hinj : Function.Injective f := by
    intro j j' h
    have hval : j.1.val = j'.1.val := by
      have hh := congrArg (fun x : D' => x.1.val) h
      simpa [f] using hh
    apply Subtype.ext
    exact Fin.ext hval
  have hcard : S.card ≤ D.card := by
    have hh : Fintype.card S' ≤ Fintype.card D' := Fintype.card_le_of_injective f hinj
    simpa [S', D'] using hh
  have hS : _root_.hammingDist (specialWord9 m u) (specialWord9 m v) = S.card := by
    change (Finset.univ.filter
      (fun i : Fin m => specialWord9 m u i ≠ specialWord9 m v i)).card = S.card
    rfl
  have hD : _root_.hammingDist u v = D.card := by
    change (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = D.card
    rfl
  rw [hS, hD]
  exact hcard

/-- Restricting to the residual coordinates cannot increase Hamming distance. -/
theorem hammingDistResidualLe9 {m n : ℕ} (u v : CubeVertex n) :
    _root_.hammingDist (residualWord9 m u) (residualWord9 m v) ≤ _root_.hammingDist u v := by
  classical
  let R : Finset (Fin (n - m)) :=
    Finset.univ.filter (fun i => residualWord9 m u i ≠ residualWord9 m v i)
  let D : Finset (Fin n) := Finset.univ.filter (fun i => u i ≠ v i)
  let R' := {i : Fin (n - m) // i ∈ R}
  let D' := {i : Fin n // i ∈ D}
  let f : R' → D' := fun j =>
    ⟨⟨m + j.1.val, by omega⟩, by
      have hdiff := (Finset.mem_filter.mp j.2).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [residualWord9] using hdiff⟩⟩
  have hinj : Function.Injective f := by
    intro j j' h
    have hval : m + j.1.val = m + j'.1.val := by
      have hh := congrArg (fun x : D' => x.1.val) h
      simpa [f] using hh
    have hval' : j.1.val = j'.1.val := Nat.add_left_cancel hval
    apply Subtype.ext
    exact Fin.ext hval'
  have hcard : R.card ≤ D.card := by
    have hh : Fintype.card R' ≤ Fintype.card D' := Fintype.card_le_of_injective f hinj
    simpa [R', D'] using hh
  have hR : _root_.hammingDist (residualWord9 m u) (residualWord9 m v) = R.card := by
    change (Finset.univ.filter
      (fun i : Fin (n - m) => residualWord9 m u i ≠ residualWord9 m v i)).card = R.card
    rfl
  have hD : _root_.hammingDist u v = D.card := by
    change (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = D.card
    rfl
  rw [hR, hD]
  exact hcard

/-- An anchor in a star scope is seen at one of its neighboring odd rows. -/
theorem starScopeAnchorWitness9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {c : I.ID} (h : Sum.inl c ∈ starScope9 I v) :
    ∃ b : OddSites9 n, (cube n).Adj v.1 b.1 ∧ c ∈ I.seen b.1 := by
  classical
  unfold starScope9 at h
  rcases Finset.mem_biUnion.mp h with ⟨b, hb, hcoord⟩
  have hadj : (cube n).Adj v.1 b.1 := (Finset.mem_filter.mp hb).2
  rcases Finset.mem_union.mp hcoord with hImage | hmask
  · rcases Finset.mem_image.mp hImage with ⟨d, hd, hEq⟩
    have hdc : d = c := Sum.inl.inj hEq
    subst d
    exact ⟨b, hadj, hd⟩
  · have hne : Sum.inl c ≠ Sum.inr b := by intro hEq; cases hEq
    exact False.elim (hne (Finset.mem_singleton.mp hmask))

/-- A mask in a star scope is the mask of an adjacent odd row. -/
theorem starScopeMaskWitness9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} (h : Sum.inr b ∈ starScope9 I v) :
    (cube n).Adj v.1 b.1 := by
  classical
  unfold starScope9 at h
  rcases Finset.mem_biUnion.mp h with ⟨b', hb', hcoord⟩
  have hadj : (cube n).Adj v.1 b'.1 := (Finset.mem_filter.mp hb').2
  rcases Finset.mem_union.mp hcoord with hImage | hmask
  · rcases Finset.mem_image.mp hImage with ⟨c, hc, hEq⟩
    have hne : Sum.inl c ≠ Sum.inr b := by intro hEq'; cases hEq'
    exact False.elim (hne hEq)
  · have hEq : Sum.inr b = Sum.inr b' := Finset.mem_singleton.mp hmask
    have hbb' : b = b' := Sum.inr.inj hEq
    subst b'
    exact hadj

/-- Intersecting star scopes force the even sites into a Hamming ball of radius `2r+8`. -/
theorem starScopeOverlapRadius9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    (v v' : EvenSites9 n)
    (h : ¬ Disjoint (starScope9 I v) (starScope9 I v')) :
    _root_.hammingDist v.1 v'.1 ≤ 2 * P.radius n + 8 := by
  classical
  obtain ⟨i, hi, hi'⟩ := Finset.not_disjoint_iff.mp h
  cases i with
  | inr b =>
      have hvb := starScopeMaskWitness9 hi
      have hv'b := starScopeMaskWitness9 hi'
      have hvbDist : _root_.hammingDist v.1 b.1 = 1 := by
        change (cube n).Adj v.1 b.1 at hvb
        exact hvb
      have hv'bDist : _root_.hammingDist v'.1 b.1 = 1 := by
        change (cube n).Adj v'.1 b.1 at hv'b
        exact hv'b
      calc
        _root_.hammingDist v.1 v'.1 ≤
            _root_.hammingDist v.1 b.1 + _root_.hammingDist b.1 v'.1 :=
          _root_.hammingDist_triangle v.1 b.1 v'.1
        _ = 1 + 1 := by rw [_root_.hammingDist_comm b.1 v'.1, hvbDist, hv'bDist]
        _ ≤ 2 * P.radius n + 8 := by omega
  | inl c =>
      obtain ⟨b, hvb, hc⟩ := starScopeAnchorWitness9 hi
      obtain ⟨b', hv'b', hc'⟩ := starScopeAnchorWitness9 hi'
      have hcSeen : c ∈ I.seen b.1 := hc
      have hcSeen' : c ∈ I.seen b'.1 := hc'
      unfold IDMap9.seen seenIDs9 at hcSeen hcSeen'
      obtain ⟨u, hu, hcu⟩ := Finset.mem_image.mp hcSeen
      obtain ⟨u', hu', hcu'⟩ := Finset.mem_image.mp hcSeen'
      have hbu : (cube n).Adj b.1 u := (Finset.mem_filter.mp hu).2
      have hb'u' : (cube n).Adj b'.1 u' := (Finset.mem_filter.mp hu').2
      have hcenter : I.center u = I.center u' := hcu.trans hcu'.symm
      have hslice : specialWord9 (P.m n) u = specialWord9 (P.m n) u' := by
        calc
          specialWord9 (P.m n) u = (I.center u).slice := (I.center_slice u).symm
          _ = (I.center u').slice := congrArg (fun c : I.ID => c.slice) hcenter
          _ = specialWord9 (P.m n) u' := I.center_slice u'
      have hloc : (I.center u).location = (I.center u').location :=
        congrArg (fun c : I.ID => c.location) hcenter
      have hnearU :
          _root_.hammingDist (residualWord9 (P.m n) u) (I.center u).location ≤ P.radius n := by
        simpa [_root_.hammingDist_comm] using I.center_near u
      have hnearU' :
          _root_.hammingDist (I.center u).location (residualWord9 (P.m n) u') ≤ P.radius n := by
        simpa [hloc] using I.center_near u'
      have hresid :
          _root_.hammingDist (residualWord9 (P.m n) u) (residualWord9 (P.m n) u') ≤
            2 * P.radius n := by
        calc
          _root_.hammingDist (residualWord9 (P.m n) u) (residualWord9 (P.m n) u') ≤
              _root_.hammingDist (residualWord9 (P.m n) u) (I.center u).location +
                _root_.hammingDist (I.center u).location (residualWord9 (P.m n) u') :=
            _root_.hammingDist_triangle _ _ _
          _ ≤ P.radius n + P.radius n := Nat.add_le_add hnearU hnearU'
          _ = 2 * P.radius n := by omega
      have huu' : _root_.hammingDist u u' ≤ 2 * P.radius n := by
        have hsplit := hammingDistSplitBound9 (m := P.m n) u u'
        rw [hslice, _root_.hammingDist_self, zero_add] at hsplit
        exact hsplit.trans hresid
      have hvbDist : _root_.hammingDist v.1 b.1 = 1 := by
        change (cube n).Adj v.1 b.1 at hvb
        exact hvb
      have hbuDist : _root_.hammingDist b.1 u = 1 := by
        change (cube n).Adj b.1 u at hbu
        exact hbu
      have hvu : _root_.hammingDist v.1 u ≤ 2 := by
        calc
          _root_.hammingDist v.1 u ≤
              _root_.hammingDist v.1 b.1 + _root_.hammingDist b.1 u :=
            _root_.hammingDist_triangle v.1 b.1 u
          _ = 1 + 1 := by rw [hvbDist, hbuDist]
          _ = 2 := by norm_num
      have hb'u'Dist : _root_.hammingDist b'.1 u' = 1 := by
        change (cube n).Adj b'.1 u' at hb'u'
        exact hb'u'
      have hv'b'Dist : _root_.hammingDist v'.1 b'.1 = 1 := by
        change (cube n).Adj v'.1 b'.1 at hv'b'
        exact hv'b'
      have hu'v' : _root_.hammingDist u' v'.1 ≤ 2 := by
        calc
          _root_.hammingDist u' v'.1 ≤
              _root_.hammingDist u' b'.1 + _root_.hammingDist b'.1 v'.1 :=
            _root_.hammingDist_triangle u' b'.1 v'.1
          _ = 1 + 1 := by
            rw [_root_.hammingDist_comm u' b'.1, hb'u'Dist,
              _root_.hammingDist_comm b'.1 v'.1, hv'b'Dist]
          _ = 2 := by norm_num
      calc
        _root_.hammingDist v.1 v'.1 ≤
            _root_.hammingDist v.1 u + _root_.hammingDist u v'.1 :=
          _root_.hammingDist_triangle v.1 u v'.1
        _ ≤ _root_.hammingDist v.1 u +
              (_root_.hammingDist u u' + _root_.hammingDist u' v'.1) :=
          Nat.add_le_add_left (_root_.hammingDist_triangle u u' v'.1) _
        _ ≤ 2 + (2 * P.radius n + 2) := by omega
        _ ≤ 2 * P.radius n + 8 := by omega

/-- The coordinates consulted by one odd row: its seen anchors and its own mask. -/
noncomputable def oddRowInputs9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    (b : OddSites9 n) : Finset (I.ID ⊕ OddSites9 n) :=
  (I.seen b.1).image Sum.inl ∪ {Sum.inr b}

/-- An odd row's input scope is contained in the star scope of any adjacent even site. -/
theorem oddRowInputsSubsetStarScope9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} (hb : (cube n).Adj v.1 b.1) :
    oddRowInputs9 (I := I) b ⊆ starScope9 I v := by
  classical
  intro i hi
  cases i with
  | inl c =>
      have hc : c ∈ I.seen b.1 := by simpa [oddRowInputs9] using hi
      unfold starScope9
      apply Finset.mem_biUnion.mpr
      refine ⟨b, ?_, ?_⟩
      · simp [hb]
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  | inr b' =>
      have hbb' : b' = b := by simpa [oddRowInputs9] using hi
      subst b'
      unfold starScope9
      apply Finset.mem_biUnion.mpr
      refine ⟨b, ?_, ?_⟩
      · simp [hb]
      · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- An odd row law is fixed by its own input coordinates. -/
theorem rowLawEqOfInputs9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (b : OddSites9 n) (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ oddRowInputs9 (I := I) b, ω i = ω' i) :
    rowLaw9 S E G ω b = rowLaw9 S E G ω' b := by
  classical
  have hmask : msk9 ω b = msk9 ω' b := by
    have hm := hω (Sum.inr b) (by simp [oddRowInputs9])
    simpa [msk9, Val9] using hm
  have hanc : ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c := by
    intro c hc
    have ha := hω (Sum.inl c) (by simp [oddRowInputs9, hc])
    simpa [anc9, Val9] using ha
  have hhit : hitSet9 E G ω (I.seen b.1) = hitSet9 E G ω' (I.seen b.1) := by
    ext y
    simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall_congr'
    intro c
    apply forall_congr'
    intro hc
    rw [hanc c hc]
  simp [rowLaw9, maskedLaw9, hmask, hhit]

/-- Row-law dependence in the product experiment, with its explicit coordinate scope. -/
theorem rowLawDependsOnInputs9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour) (b : OddSites9 n) :
    FinProb.DependsOn (fun ω : Outcome9 I N => rowLaw9 S E G ω b) (oddRowInputs9 (I := I) b) := by
  intro ω ω' hω
  exact rowLawEqOfInputs9 S E G b ω ω' hω

/-- Separated odd rows have disjoint anchor-and-mask input scopes. -/
theorem oddRowInputsDisjointOfNotNear9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    (b b' : OddSites9 n) (hnot : ¬ siteNear9 P n b.1 b'.1) :
    Disjoint (oddRowInputs9 (I := I) b) (oddRowInputs9 (I := I) b') := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  cases i with
  | inr d =>
      have hdb : d = b := by simpa [oddRowInputs9] using hi
      have hdb' : d = b' := by simpa [oddRowInputs9] using hi'
      have hbb' : b = b' := hdb.symm.trans hdb'
      have hnear : siteNear9 P n b.1 b'.1 := by
        rw [hbb'.symm]
        constructor <;> simp [siteNear9]
      exact hnot hnear
  | inl c =>
      have hc : c ∈ I.seen b.1 := by simpa [oddRowInputs9] using hi
      have hc' : c ∈ I.seen b'.1 := by simpa [oddRowInputs9] using hi'
      unfold IDMap9.seen seenIDs9 at hc hc'
      obtain ⟨u, hu, hcu⟩ := Finset.mem_image.mp hc
      obtain ⟨u', hu', hcu'⟩ := Finset.mem_image.mp hc'
      have hbu : (cube n).Adj b.1 u := (Finset.mem_filter.mp hu).2
      have hb'u' : (cube n).Adj b'.1 u' := (Finset.mem_filter.mp hu').2
      have hcenter : I.center u = I.center u' := hcu.trans hcu'.symm
      have hslice : specialWord9 (P.m n) u = specialWord9 (P.m n) u' := by
        calc
          specialWord9 (P.m n) u = (I.center u).slice := (I.center_slice u).symm
          _ = (I.center u').slice := congrArg (fun x : I.ID => x.slice) hcenter
          _ = specialWord9 (P.m n) u' := I.center_slice u'
      have hloc : (I.center u).location = (I.center u').location :=
        congrArg (fun x : I.ID => x.location) hcenter
      have hnearU :
          _root_.hammingDist (residualWord9 (P.m n) u) (I.center u).location ≤ P.radius n := by
        simpa [_root_.hammingDist_comm] using I.center_near u
      have hnearU' :
          _root_.hammingDist (I.center u).location (residualWord9 (P.m n) u') ≤ P.radius n := by
        simpa [hloc] using I.center_near u'
      have hresidUU' :
          _root_.hammingDist (residualWord9 (P.m n) u) (residualWord9 (P.m n) u') ≤
            2 * P.radius n := by
        calc
          _root_.hammingDist (residualWord9 (P.m n) u) (residualWord9 (P.m n) u') ≤
              _root_.hammingDist (residualWord9 (P.m n) u) (I.center u).location +
                _root_.hammingDist (I.center u).location (residualWord9 (P.m n) u') :=
            _root_.hammingDist_triangle _ _ _
          _ ≤ P.radius n + P.radius n := Nat.add_le_add hnearU hnearU'
          _ = 2 * P.radius n := by omega
      have hspBU :
          _root_.hammingDist (specialWord9 (P.m n) b.1) (specialWord9 (P.m n) u) ≤ 1 := by
        exact (hammingDistSpecialLe9 (m := P.m n) b.1 u).trans (by
          change (cube n).Adj b.1 u at hbu
          change _root_.hammingDist b.1 u ≤ 1
          exact le_of_eq hbu)
      have hspU'B' :
          _root_.hammingDist (specialWord9 (P.m n) u') (specialWord9 (P.m n) b'.1) ≤ 1 := by
        exact (hammingDistSpecialLe9 (m := P.m n) u' b'.1).trans (by
          have hsymm := hb'u'.symm
          change _root_.hammingDist u' b'.1 = 1 at hsymm
          exact le_of_eq hsymm)
      have hspUU' :
          _root_.hammingDist (specialWord9 (P.m n) u) (specialWord9 (P.m n) u') = 0 := by
        rw [hslice]
        exact _root_.hammingDist_self _
      have hspecial :
          _root_.hammingDist (specialWord9 (P.m n) b.1)
              (specialWord9 (P.m n) b'.1) ≤ 2 := by
        calc
          _root_.hammingDist (specialWord9 (P.m n) b.1) (specialWord9 (P.m n) b'.1) ≤
              _root_.hammingDist (specialWord9 (P.m n) b.1) (specialWord9 (P.m n) u) +
                _root_.hammingDist (specialWord9 (P.m n) u) (specialWord9 (P.m n) b'.1) :=
            _root_.hammingDist_triangle _ _ _
          _ ≤ _root_.hammingDist (specialWord9 (P.m n) b.1) (specialWord9 (P.m n) u) +
                (_root_.hammingDist (specialWord9 (P.m n) u) (specialWord9 (P.m n) u') +
                  _root_.hammingDist (specialWord9 (P.m n) u') (specialWord9 (P.m n) b'.1)) := by
            gcongr
            exact _root_.hammingDist_triangle _ _ _
          _ ≤ 1 + (0 + 1) := by omega
          _ = 2 := by omega
      have hresidBU :
          _root_.hammingDist (residualWord9 (P.m n) b.1) (residualWord9 (P.m n) u) ≤ 1 := by
        exact (hammingDistResidualLe9 (m := P.m n) b.1 u).trans (by
          change (cube n).Adj b.1 u at hbu
          change _root_.hammingDist b.1 u ≤ 1
          exact le_of_eq hbu)
      have hresidU'B' :
          _root_.hammingDist (residualWord9 (P.m n) u') (residualWord9 (P.m n) b'.1) ≤ 1 := by
        exact (hammingDistResidualLe9 (m := P.m n) u' b'.1).trans (by
          have hsymm := hb'u'.symm
          change _root_.hammingDist u' b'.1 = 1 at hsymm
          exact le_of_eq hsymm)
      have hresidual :
          _root_.hammingDist (residualWord9 (P.m n) b.1) (residualWord9 (P.m n) b'.1) ≤
            2 * P.radius n + 2 := by
        calc
          _root_.hammingDist (residualWord9 (P.m n) b.1) (residualWord9 (P.m n) b'.1) ≤
              _root_.hammingDist (residualWord9 (P.m n) b.1) (residualWord9 (P.m n) u) +
                _root_.hammingDist (residualWord9 (P.m n) u) (residualWord9 (P.m n) b'.1) :=
            _root_.hammingDist_triangle _ _ _
          _ ≤ _root_.hammingDist (residualWord9 (P.m n) b.1) (residualWord9 (P.m n) u) +
                (_root_.hammingDist (residualWord9 (P.m n) u) (residualWord9 (P.m n) u') +
                  _root_.hammingDist (residualWord9 (P.m n) u') (residualWord9 (P.m n) b'.1)) := by
            gcongr
            exact _root_.hammingDist_triangle _ _ _
          _ ≤ 1 + (2 * P.radius n + 1) := by omega
          _ = 2 * P.radius n + 2 := by omega
      have hnear : siteNear9 P n b.1 b'.1 := by
        unfold siteNear9
        constructor <;> omega
      exact hnot hnear

open Classical in
/-- Star events meeting a union of odd-row neighborhoods are bounded by the local degrees. -/
theorem starEventsTouchingOddNeighborhoods9 {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (hscope : StarScopeFacts9 S I E G) {k : ℕ} (a : Fin k → EvenSites9 n) :
    (Finset.univ.filter (fun v : EvenSites9 n =>
      ¬ Disjoint (starScope9 I v)
        ((Finset.univ : Finset (Fin k)).biUnion (fun i => starScope9 I (a i))))).card ≤
      k * (lllDegree9 P n + 1) := by
  classical
  let T : Finset (EvenSites9 n) := Finset.univ.filter (fun v : EvenSites9 n =>
    ¬ Disjoint (starScope9 I v)
      ((Finset.univ : Finset (Fin k)).biUnion (fun i => starScope9 I (a i))))
  let Tᵢ : Fin k → Finset (EvenSites9 n) := fun i =>
    insert (a i) (Finset.univ.filter (fun v : EvenSites9 n =>
      v ≠ a i ∧ ¬ Disjoint (starScope9 I (a i)) (starScope9 I v)))
  have hsubset : T ⊆ (Finset.univ : Finset (Fin k)).biUnion Tᵢ := by
    intro v hv
    have hnot := (Finset.mem_filter.mp hv).2
    obtain ⟨x, hxv, hxU⟩ := Finset.not_disjoint_iff.mp hnot
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxU
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    change v ∈ insert (a i) (Finset.univ.filter (fun w : EvenSites9 n =>
      w ≠ a i ∧ ¬ Disjoint (starScope9 I (a i)) (starScope9 I w)))
    by_cases hEq : v = a i
    · simp [Tᵢ, hEq]
    · rw [Finset.mem_insert]
      right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hEq, ?_⟩
      exact Finset.not_disjoint_iff.mpr ⟨x, hxi, hxv⟩
  have hcardᵢ (i : Fin k) : (Tᵢ i).card ≤ lllDegree9 P n + 1 := by
    unfold Tᵢ
    calc
      (insert (a i) (Finset.univ.filter (fun v : EvenSites9 n =>
        v ≠ a i ∧ ¬ Disjoint (starScope9 I (a i)) (starScope9 I v)))).card ≤
          (Finset.univ.filter (fun v : EvenSites9 n =>
            v ≠ a i ∧ ¬ Disjoint (starScope9 I (a i)) (starScope9 I v))).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ lllDegree9 P n + 1 := Nat.add_le_add_right (hscope.2 (a i)) 1
  have hsum : ((Finset.univ : Finset (Fin k)).biUnion Tᵢ).card ≤
      ∑ i ∈ (Finset.univ : Finset (Fin k)), (Tᵢ i).card := Finset.card_biUnion_le
  calc
    T.card ≤ ((Finset.univ : Finset (Fin k)).biUnion Tᵢ).card := Finset.card_le_card hsubset
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)), (Tᵢ i).card := hsum
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)), (lllDegree9 P n + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hcardᵢ i
    _ = k * (lllDegree9 P n + 1) := by simp

/-- A finite product of functions with pairwise disjoint scopes factors under the raw product law. -/
theorem piExpectProdDisjoint9 {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [DecidableEq ι] {Ω : V → Type*} [∀ v, Fintype (Ω v)]
    (P : ∀ v, FinProb (Ω v)) (f : ι → (∀ v, Ω v) → ℝ) (scope : ι → Finset V)
    (hdepends : ∀ i, FinProb.DependsOn (f i) (scope i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (scope i) (scope j)) :
    ∀ T : Finset ι,
      (FinProb.pi P).expect (fun ω => ∏ i ∈ T, f i ω) =
        ∏ i ∈ T, (FinProb.pi P).expect (f i) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => simpa using (FinProb.expect_const (FinProb.pi P) (1 : ℝ))
  | @insert i T hi ih =>
      let U := T.biUnion scope
      have hdependsProd :
          FinProb.DependsOn (fun ω => ∏ j ∈ T, f j ω) U := by
        intro ω ω' hagree
        apply Finset.prod_congr rfl
        intro j hj
        apply hdepends j
        intro a ha
        exact hagree a (Finset.mem_biUnion.mpr ⟨j, hj, ha⟩)
      have hdisjointUnion : Disjoint (scope i) U := by
        apply Finset.disjoint_left.mpr
        intro a ha haU
        rcases Finset.mem_biUnion.mp haU with ⟨j, hj, haj⟩
        have hij : i ≠ j := by
          intro heq
          subst j
          exact hi hj
        exact Finset.disjoint_left.mp (hdisjoint i j hij) ha haj
      have hfactor := FinProb.pi_expect_mul_of_disjoint P (f i)
        (fun ω => ∏ j ∈ T, f j ω) (scope i) U (hdepends i) hdependsProd hdisjointUnion
      calc
        (FinProb.pi P).expect (fun ω => ∏ j ∈ insert i T, f j ω) =
            (FinProb.pi P).expect (fun ω => f i ω * ∏ j ∈ T, f j ω) := by
              congr 1
              funext ω
              rw [Finset.prod_insert hi]
        _ = (FinProb.pi P).expect (f i) *
              (FinProb.pi P).expect (fun ω => ∏ j ∈ T, f j ω) := hfactor
        _ = (FinProb.pi P).expect (f i) * ∏ j ∈ T, (FinProb.pi P).expect (f j) := by
              rw [ih]
        _ = ∏ j ∈ insert i T, (FinProb.pi P).expect (f j) := by
              rw [Finset.prod_insert hi]

open Classical in
/-- Integrating a function of the free coordinates is the corresponding marginal expectation. -/
theorem piExpectGlue9 {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : V → Type*} [∀ v, Fintype (Ω v)] (P : ∀ v, FinProb (Ω v))
    (U : Finset V) (Φ : (∀ v, Ω v) → ℝ) (ω₀ : ∀ v, Ω v)
    (hΦ : FinProb.DependsOn Φ U) :
    (∑ a : (∀ i : U, Ω i.1), (∏ i : U, (P i.1).w (a i)) *
        Φ (S07.glue U ω₀ a)) = (FinProb.pi P).expect Φ := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i : V => i ∈ U) Ω
  let b₀ : ∀ i : {i // i ∉ U}, Ω i.1 := fun i => ω₀ i.1
  have hglue (a : ∀ i : U, Ω i.1) : S07.glue U ω₀ a = e.symm (a, b₀) := by
    funext i
    by_cases hi : i ∈ U
    · simp [S07.glue, e, b₀, hi, Equiv.piEquivPiSubtypeProd_symm_apply]
    · simp [S07.glue, e, b₀, hi, Equiv.piEquivPiSubtypeProd_symm_apply]
  have hsplit := FinProb.pi_expect_depends P U Φ ω₀ hΦ
  simpa [FinProb.expect, FinProb.pi, hglue, e, b₀] using hsplit.symm

open Classical in
/-- The probability of an event determined by `U` equals the probability in the product marginal on `U`. -/
theorem piPrDependsEq9 {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : V → Type*} [∀ v, Fintype (Ω v)] (P : ∀ v, FinProb (Ω v))
    (U : Finset V) (F : (∀ v, Ω v) → Prop) (ω₀ : ∀ v, Ω v)
    (hF : FinProb.DependsOn F U) :
    (FinProb.pi P).pr F =
      (FinProb.pi (fun i : {i // i ∈ U} => P i.1)).pr (fun a => F (S07.glue U ω₀ a)) := by
  let indicator : (∀ v, Ω v) → ℝ := fun ω => if F ω then 1 else 0
  have hindicator : FinProb.DependsOn indicator U := by
    intro ω ω' hagree
    have hEq := hF ω ω' hagree
    simp [indicator, hEq]
  have hsplit := piExpectGlue9 P U indicator ω₀ hindicator
  calc
    (FinProb.pi P).pr F = (FinProb.pi P).expect indicator := by
      unfold FinProb.pr FinProb.expect indicator
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : F ω <;> simp [h]
    _ = ∑ a : (∀ i : U, Ω i.1),
          (∏ i : U, (P i.1).w (a i)) * indicator (S07.glue U ω₀ a) := hsplit.symm
    _ = (FinProb.pi (fun i : {i // i ∈ U} => P i.1)).pr
          (fun a => F (S07.glue U ω₀ a)) := by
      simp [FinProb.pr, FinProb.pi, indicator]

/-- Split a dependent product into one coordinate and all remaining coordinates. -/
def coordSplitEquiv {ι : Type*} [DecidableEq ι] {Ω : ι → Type*} (j : ι) :
    (∀ i, Ω i) ≃ Ω j × (∀ i : {i // i ≠ j}, Ω i.1) where
  toFun ω := (ω j, fun i => ω i.1)
  invFun p i := if h : i = j then h ▸ p.1 else p.2 ⟨i, h⟩
  left_inv ω := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨x, τ⟩
    apply Prod.ext
    · simp
    · funext i
      simp [i.2]

/-- Integrate a finite product law by first summing one selected coordinate. -/
theorem pi_expect_split_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (j : ι) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ x, (P j).w x *
        (FinProb.pi (fun i : {i // i ≠ j} => P i.1)).expect
          (fun τ => f ((coordSplitEquiv j).symm (x, τ))) := by
  classical
  let e : (∀ i, Ω i) ≃ Ω j × (∀ i : {i // i ≠ j}, Ω i.1) := coordSplitEquiv j
  have hweight (x : Ω j) (τ : ∀ i : {i // i ≠ j}, Ω i.1) :
      (∏ i, (P i).w ((e.symm (x, τ)) i)) =
        (P j).w x * ∏ i : {i // i ≠ j}, (P i.1).w (τ i) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => (P i).w ((e.symm (x, τ)) i)) j]
    have hj : (e.symm (x, τ)) j = x := by simp [e, coordSplitEquiv]
    rw [hj]
    congr 1
    apply Fintype.prod_congr
    intro i
    have hi : (e.symm (x, τ)) i.1 = τ i := by
      simp [e, coordSplitEquiv, i.2]
    rw [hi]
  simp only [FinProb.expect, FinProb.pi]
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ τ, (∏ i, (P i).w ((e.symm (x, τ)) i)) * f (e.symm (x, τ))) =
        ∑ τ, (P j).w x * (∏ i : {i // i ≠ j}, (P i.1).w (τ i)) *
          f (e.symm (x, τ)) := by
            apply Finset.sum_congr rfl
            intro τ hτ
            rw [hweight]
    _ = (P j).w x *
        ∑ τ, (∏ i : {i // i ≠ j}, (P i.1).w (τ i)) * f (e.symm (x, τ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ hτ
          ring

/-- Monotonicity of event probabilities on a finite law. -/
theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A B : Ω → Prop)
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB, P.nonneg ω]
  · by_cases hB : B ω
    · simp [hA, hB, P.nonneg ω]
    · simp [hA, hB]

/-- The logarithm of the dependency-degree base is little-oh of `n^u` when the radius exponent is below `u`. -/
theorem degreeLogSmall9 (P : Params9) (hexps : ScaleExps9 P) {c : ℝ} (hc : 0 < c) :
    ∃ n₀, ∀ n ≥ n₀,
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
        (c / 4) * (n : ℝ) ^ P.u := by
  rcases hexps with ⟨heps, hepsσ, hu, hσu, _⟩
  have hσ : 0 < (P.σ : ℝ) := lt_trans heps hepsσ
  let δ : ℝ := (P.u - P.σ) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδu : δ < P.u := by dsimp [δ]; linarith [hσ]
  let C : ℝ := (2 : ℝ) ^ δ / δ
  have hC : 0 < C := by dsimp [C]; positivity
  have hneg1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-δ)) atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hneg2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ - P.u)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hδu)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, neg_sub] using h
  let ratio : ℕ → ℝ := fun n => 2 * C * (n : ℝ) ^ (-δ) + 8 * C * (n : ℝ) ^ (δ - P.u)
  have hratio : Tendsto ratio atTop (nhds 0) := by
    dsimp [ratio]
    simpa using (hneg1.const_mul (2 * C)).add (hneg2.const_mul (8 * C))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hratio.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < c / 4)))
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hrad : (P.radius n : ℝ) ≤ (n : ℝ) ^ (P.σ : ℝ) := by
    dsimp [Params9.radius]
    exact Nat.floor_le (by positivity : 0 ≤ (n : ℝ) ^ (P.σ : ℝ))
  have hR : 2 * (P.radius n : ℝ) + 8 ≤ 2 * (n : ℝ) ^ (P.σ : ℝ) + 8 := by nlinarith [hrad]
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    linarith
  have hlog := Real.log_le_rpow_div (by positivity : 0 ≤ (n : ℝ) + 1) hδ
  have hnplus : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith [hnR1]
  have hpow : ((n : ℝ) + 1) ^ δ ≤ (2 : ℝ) ^ δ * (n : ℝ) ^ δ := by
    calc
      ((n : ℝ) + 1) ^ δ ≤ (2 * (n : ℝ)) ^ δ := Real.rpow_le_rpow (by positivity) hnplus hδ.le
      _ = (2 : ℝ) ^ δ * (n : ℝ) ^ δ := by
        rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hnR.le]
  have hnum :
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
        2 * C * (n : ℝ) ^ ((P.σ : ℝ) + δ) + 8 * C * (n : ℝ) ^ δ := by
    calc
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
          (2 * (n : ℝ) ^ (P.σ : ℝ) + 8) * Real.log ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hR hlog0
      _ ≤ (2 * (n : ℝ) ^ (P.σ : ℝ) + 8) * (((n : ℝ) + 1) ^ δ / δ) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (2 * (n : ℝ) ^ (P.σ : ℝ) + 8) * ((2 : ℝ) ^ δ * (n : ℝ) ^ δ / δ) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hδ.le) (by positivity)
      _ = 2 * C * (n : ℝ) ^ ((P.σ : ℝ) + δ) + 8 * C * (n : ℝ) ^ δ := by
            dsimp [C]
            rw [Real.rpow_add hnR (P.σ : ℝ) δ]
            ring
  have hpowA : (n : ℝ) ^ ((P.σ : ℝ) + δ) = (n : ℝ) ^ P.u * (n : ℝ) ^ (-δ) := by
    rw [← Real.rpow_add hnR P.u (-δ)]
    congr 1
    dsimp [δ]
    ring
  have hpowB : (n : ℝ) ^ δ = (n : ℝ) ^ P.u * (n : ℝ) ^ (δ - P.u) := by
    rw [← Real.rpow_add hnR P.u (δ - P.u)]
    congr 1
    ring
  have hsmall : ratio n < c / 4 := hn₀ n hn₀'
  have hnum' : (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
      (n : ℝ) ^ P.u * ratio n := by
    calc
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
          2 * C * (n : ℝ) ^ ((P.σ : ℝ) + δ) + 8 * C * (n : ℝ) ^ δ := hnum
      _ = (n : ℝ) ^ P.u * ratio n := by
        rw [hpowA, hpowB]
        dsimp [ratio]
        ring
  calc
    (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
        (n : ℝ) ^ P.u * ratio n := hnum'
    _ ≤ (c / 4) * (n : ℝ) ^ P.u := by
      calc
        (n : ℝ) ^ P.u * ratio n ≤ (n : ℝ) ^ P.u * (c / 4) :=
          mul_le_mul_of_nonneg_left (le_of_lt hsmall) (by positivity)
        _ = (c / 4) * (n : ℝ) ^ P.u := by ring

/-- Extract the parameter exponent margins from validity without using the eventual-scale node. -/
theorem scaleExpsOfValid9 (P : Params9) (hP : Params9.Valid P) : ScaleExps9 P := by
  rcases hP with ⟨hxs, _, _, hσ, hχ, _, hcase⟩
  rcases hxs with ⟨hxS, _, _⟩
  rcases hσ with ⟨hσpos, hσxS⟩
  rcases hχ with ⟨_, hχbound⟩
  have hxSReal : 0 < (P.xS : ℝ) := by exact_mod_cast hxS
  have hσReal : 0 < (P.σ : ℝ) := by exact_mod_cast hσpos
  have hu : 0 < P.u := by
    dsimp [Params9.u]
    positivity
  have hσu : (P.σ : ℝ) < P.u := by
    have h : (P.σ : ℝ) < (P.xS : ℝ) / 10 := by exact_mod_cast hσxS
    dsimp [Params9.u]
    linarith
  have hχu : (P.χ : ℝ) < P.u / 50 := by
    have hχ' : (P.χ : ℝ) <
        ((min P.xS (min P.hMinus (1 - P.hPlus)) : ℚ) : ℝ) / 100 := by
      exact_mod_cast hχbound
    have hmin : (min P.xS (min P.hMinus (1 - P.hPlus)) : ℚ) ≤ P.xS := min_le_left _ _
    have hmin' : ((min P.xS (min P.hMinus (1 - P.hPlus)) : ℚ) : ℝ) ≤ (P.xS : ℝ) := by
      exact_mod_cast hmin
    calc
      (P.χ : ℝ) < ((min P.xS (min P.hMinus (1 - P.hPlus)) : ℚ) : ℝ) / 100 := hχ'
      _ ≤ (P.xS : ℝ) / 100 := by gcongr
      _ = P.u / 50 := by dsimp [Params9.u]; ring
  cases hcaseP : P.case with
  | sub yS yD yM =>
      have hsub' : 0 < yS ∧ yS < yM ∧ yM < 1 - P.σ ∧ 1 - P.σ < yD ∧
          yD < 1 ∧ P.χ < P.σ / 10 := by simpa [hcaseP] using hcase
      have hsub : 1 - P.σ < yD := hsub'.2.2.2.1
      have hmargin : 0 < (yD : ℝ) - (1 - (P.σ : ℝ)) := by
        exact_mod_cast (sub_pos.mpr hsub)
      have hminpos : 0 < min (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))) :=
        lt_min hσReal hmargin
      have heps' : 0 < min (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))) / 2 :=
        div_pos hminpos (by norm_num)
      have heps : 0 < P.eps := by
        simpa [Params9.eps, hcaseP] using heps'
      have hepsσ' : min (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))) / 2 < (P.σ : ℝ) := by
        linarith [min_le_left (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))), hσReal]
      have hepsσ : P.eps < (P.σ : ℝ) := by
        simpa [Params9.eps, hcaseP] using hepsσ'
      exact ⟨heps, hepsσ, hu, hσu, hχu⟩
  | lin αS αD hB yB =>
      have heps' : 0 < (P.σ : ℝ) / 2 := by positivity
      have heps : 0 < P.eps := by simpa [Params9.eps, hcaseP] using heps'
      have hepsσ' : (P.σ : ℝ) / 2 < (P.σ : ℝ) := by linarith [hσReal]
      have hepsσ : P.eps < (P.σ : ℝ) := by
        simpa [Params9.eps, hcaseP] using hepsσ'
      exact ⟨heps, hepsσ, hu, hσu, hχu⟩

/-- A star scope contains every anchor read by each of its neighbouring odd rows. -/
theorem starScopeAnchorEq9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) :
    ∀ b : OddSites9 n, (cube n).Adj v.1 b.1 →
      ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c := by
  classical
  intro b hb c hc
  have hmem : Sum.inl c ∈ starScope9 I v := by
    unfold starScope9
    apply Finset.mem_biUnion.mpr
    refine ⟨b, ?_, ?_⟩
    · simp [hb]
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  simpa [anc9, Val9] using hω (Sum.inl c) hmem

/-- A star scope contains the mask coordinate of every neighbouring odd row. -/
theorem starScopeMaskEq9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i)
    (b : OddSites9 n) (hb : (cube n).Adj v.1 b.1) : msk9 ω b = msk9 ω' b := by
  have hmem : Sum.inr b ∈ starScope9 I v := by
    classical
    unfold starScope9
    apply Finset.mem_biUnion.mpr
    refine ⟨b, ?_, ?_⟩
    · simp [hb]
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  simpa [msk9, Val9] using hω (Sum.inr b) hmem

/-- The hit filter is unchanged when all anchors in its ID set agree. -/
theorem hitSetEqOfAnchors9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (ω ω' : Outcome9 I N)
    (ids : Finset I.ID) (hids : ∀ c ∈ ids, anc9 ω c = anc9 ω' c) :
    hitSet9 E G ω ids = hitSet9 E G ω' ids := by
  classical
  ext y
  simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro c
  apply forall_congr'
  intro hc
  rw [hids c hc]

/-- The local row and deletion laws are fixed by the coordinates in a star scope. -/
theorem starScopeRowsEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i)
    (b : OddSites9 n) (hb : (cube n).Adj v.1 b.1) :
    rowLaw9 S E G ω b = rowLaw9 S E G ω' b ∧
      ∀ t, delLaw9 S E G ω b t = delLaw9 S E G ω' b t := by
  classical
  have hanc := starScopeAnchorEq9 ω ω' hω b hb
  have hmask := starScopeMaskEq9 ω ω' hω b hb
  have hhit : hitSet9 E G ω (I.seen b.1) = hitSet9 E G ω' (I.seen b.1) :=
    hitSetEqOfAnchors9 E G ω ω' (I.seen b.1) hanc
  have hmasked : maskedLaw9 S ω b = maskedLaw9 S ω' b := by
    simp [maskedLaw9, hmask]
  constructor
  · simp [rowLaw9, hmasked, hhit]
  · intro t
    have hdelhit :
        hitSet9 E G ω ((I.seen b.1).erase t) =
          hitSet9 E G ω' ((I.seen b.1).erase t) :=
      hitSetEqOfAnchors9 E G ω ω' _ (fun c hc => hanc c (Finset.mem_of_mem_erase hc))
    simp [delLaw9, hmasked, hdelhit]

/-- The center ID of an even site is seen at every adjacent odd site. -/
theorem centerSeen9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} (hb : (cube n).Adj v.1 b.1) :
    I.center v.1 ∈ I.seen b.1 := by
  classical
  unfold IDMap9.seen seenIDs9
  apply Finset.mem_image.mpr
  refine ⟨v.1, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.symm⟩

/-- Every ID in a star row's full order is among that row's seen IDs. -/
theorem fullOrderMemSeen9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} (hb : (cube n).Adj v.1 b.1)
    {c : I.ID} (hc : c ∈ fullOrder9 I v b) : c ∈ I.seen b.1 := by
  classical
  unfold fullOrder9 at hc
  rcases List.mem_append.mp hc with houtercore | hlast
  · rcases List.mem_append.mp houtercore with houter | hcore
    · have hmem : c ∈ outerIDs9 I v b := by simpa using houter
      exact (Finset.mem_sdiff.mp hmem).1
    · have hmem : c ∈ coreIDs9 I v b := by simpa using hcore
      exact (Finset.mem_inter.mp (Finset.mem_erase.mp hmem).2).1
  · have hcenter : c = I.center v.1 := List.mem_singleton.mp hlast
    rw [hcenter]
    exact centerSeen9 hb

/-- Every ID in a star row's core order is among that row's seen IDs. -/
theorem coreOrderMemSeen9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} {c : I.ID}
    (hc : c ∈ coreOrder9 I v b) : c ∈ I.seen b.1 := by
  classical
  have hmem : c ∈ coreIDs9 I v b := by simpa [coreOrder9] using hc
  exact (Finset.mem_inter.mp (Finset.mem_erase.mp hmem).2).1

/-- The full ordered star list enumerates exactly the IDs seen at that odd row. -/
theorem fullOrderToFinsetEqSeen9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} (hb : (cube n).Adj v.1 b.1) :
    (fullOrder9 I v b).toFinset = I.seen b.1 := by
  classical
  have hcenterSeen : I.center v.1 ∈ I.seen b.1 := centerSeen9 hb
  have hcenterCore : I.center v.1 ∈ I.core v.1 := I.center_mem_core v.1 v.2
  ext c
  simp [fullOrder9, outerIDs9, coreIDs9, hcenterSeen, hcenterCore, Finset.mem_sdiff]
  tauto

/-- The full star order has no repeated IDs. -/
theorem fullOrderNodup9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} (hb : (cube n).Adj v.1 b.1) :
    (fullOrder9 I v b).Nodup := by
  classical
  have hcenterSeen : I.center v.1 ∈ I.seen b.1 := centerSeen9 hb
  have hcenterCore : I.center v.1 ∈ I.core v.1 := I.center_mem_core v.1 v.2
  have houter : (outerIDs9 I v b).toList.Nodup := Finset.nodup_toList _
  have hcore : (coreIDs9 I v b).toList.Nodup := Finset.nodup_toList _
  have hblocks : ((outerIDs9 I v b).toList ++ (coreIDs9 I v b).toList).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨houter, hcore, ?_⟩
    intro a ha c hc
    intro hac
    have ha' : a ∈ outerIDs9 I v b := by simpa using ha
    have hc' : c ∈ coreIDs9 I v b := by simpa using hc
    have hnot : a ∉ I.core v.1 := (Finset.mem_sdiff.mp ha').2
    have hin : c ∈ I.core v.1 :=
      (Finset.mem_inter.mp (Finset.mem_erase.mp hc').2).2
    have hac' : a = c := by exact hac
    rw [hac'] at hnot
    exact hnot hin
  unfold fullOrder9
  apply List.nodup_append.mpr
  refine ⟨hblocks, by simp, ?_⟩
  intro a ha c hc
  intro hac
  have hcEq : c = I.center v.1 := by simpa using hc
  have hae : a = I.center v.1 := hac.trans hcEq
  rcases List.mem_append.mp ha with ha | ha
  · have ha' : a ∈ outerIDs9 I v b := by simpa using ha
    have hnot : a ∉ I.core v.1 := (Finset.mem_sdiff.mp ha').2
    rw [hae] at hnot
    exact hnot hcenterCore
  · have ha' : a ∈ coreIDs9 I v b := by simpa using ha
    have hne : a ≠ I.center v.1 := (Finset.mem_erase.mp ha').1
    exact hne hae

/-- The full star order has one entry for each seen ID. -/
theorem fullOrderLengthEqSeenCard9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} (hb : (cube n).Adj v.1 b.1) :
    (fullOrder9 I v b).length = (I.seen b.1).card := by
  rw [← List.toFinset_card_of_nodup (fullOrderNodup9 hb)]
  rw [fullOrderToFinsetEqSeen9 hb]

noncomputable def orderHitSet9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (order : List I.ID) (k : ℕ) : Finset (Fin N) :=
  hitSet9 E G ω (order.take k).toFinset

noncomputable def orderHitMass9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N) (μ : Law N)
    (order : List I.ID) (k : ℕ) : ℝ :=
  ∑ y ∈ orderHitSet9 E G ω order k, μ.w y

open Classical in
/-- Extending a list prefix by its next ID adds exactly that anchor's hit filter. -/
theorem orderHitSetSucc9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (order : List I.ID) (k : ℕ) (hk : k < order.length) :
    orderHitSet9 E G ω order (k + 1) =
      (orderHitSet9 E G ω order k).filter (fun y => Hits E G (anc9 ω order[k]) y) := by
  classical
  change hitSet9 E G ω (order.take (k + 1)).toFinset =
    (hitSet9 E G ω (order.take k).toFinset).filter
      (fun y => Hits E G (anc9 ω order[k]) y)
  rw [List.take_succ_eq_append_getElem hk]
  rw [List.toFinset_append]
  ext y
  simp [hitSet9] <;> tauto

theorem orderHitMassSucc9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N) (μ : Law N)
    (order : List I.ID) (k : ℕ) (hk : k < order.length)
    (hpos : 0 < orderHitMass9 E G ω μ order k) :
    orderHitMass9 E G ω μ order (k + 1) =
      orderHitMass9 E G ω μ order k *
        rowDeg E G (anc9 ω order[k]) (prefixLaw9 E G ω μ order k) := by
  classical
  let A := orderHitSet9 E G ω order k
  let m := ∑ y ∈ A, μ.w y
  have hmpos : 0 < m := by
    simpa [m, A, orderHitMass9] using hpos
  have hprefix : prefixLaw9 E G ω μ order k = Law.restrict μ A hmpos := by
    unfold prefixLaw9 restrictOr9
    rw [dif_pos (by simpa [orderHitSet9, A, m, orderHitMass9] using hmpos)]
    rfl
  have hrestrictedSum :
      (∑ y, (Law.restrict μ A hmpos).w y *
        (if Hits E G (anc9 ω order[k]) y then 1 else 0)) =
        ∑ y ∈ A, μ.w y / m * (if Hits E G (anc9 ω order[k]) y then 1 else 0) := by
    change (∑ y, (if y ∈ A then μ.w y / m else 0) *
      (if Hits E G (anc9 ω order[k]) y then 1 else 0)) = _
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem_eq]
  have hfactor :
      m * (∑ y ∈ A, μ.w y / m *
        (if Hits E G (anc9 ω order[k]) y then 1 else 0)) =
      ∑ y ∈ A, if Hits E G (anc9 ω order[k]) y then μ.w y else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hh : Hits E G (anc9 ω order[k]) y
    · simp [hh]
      field_simp [ne_of_gt hmpos]
    · simp [hh]
  calc
    orderHitMass9 E G ω μ order (k + 1) =
        ∑ y ∈ A.filter (fun y => Hits E G (anc9 ω order[k]) y), μ.w y := by
          simp [orderHitMass9, A, orderHitSetSucc9 E G ω order k hk]
    _ = ∑ y ∈ A, if Hits E G (anc9 ω order[k]) y then μ.w y else 0 := by
          rw [Finset.sum_filter]
    _ = m * (∑ y ∈ A, μ.w y / m *
        (if Hits E G (anc9 ω order[k]) y then 1 else 0)) := hfactor.symm
    _ = m * rowDeg E G (anc9 ω order[k]) (prefixLaw9 E G ω μ order k) := by
          rw [← hrestrictedSum, hprefix, rowDeg]
    _ = orderHitMass9 E G ω μ order k *
        rowDeg E G (anc9 ω order[k]) (prefixLaw9 E G ω μ order k) := by
          rfl

theorem orderHitMassLower9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N) (μ : Law N)
    (order : List I.ID) (hregular : orderRegular9 E G ω μ order)
    (hb : P.bStar n ≤ 1 / 200) :
    ∀ k, k ≤ order.length → (49 / 100 : ℝ) ^ k ≤ orderHitMass9 E G ω μ order k := by
  classical
  have haux : ∀ k, k ≤ order.length →
      (49 / 100 : ℝ) ^ k ≤ orderHitMass9 E G ω μ order k ∧
        ∀ j c', j < k → order[j]? = some c' →
          (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c')
            (prefixLaw9 E G ω μ order j) := by
    intro k
    induction k with
    | zero =>
        intro hk
        constructor
        · simpa [orderHitMass9, orderHitSet9, hitSet9, μ.sum_eq_one]
        · intro j c' hj hjget
          omega
    | succ k ih =>
        intro hk
        have hklt : k < order.length := Nat.lt_of_succ_le hk
        have ih' := ih (Nat.le_of_lt hklt)
        have hprev : ∀ j c', j < k → order[j]? = some c' →
            (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c')
              (prefixLaw9 E G ω μ order j) := by
          exact ih'.2
        have hget : order[k]? = some order[k] :=
          (List.getElem?_eq_some_getElem_iff hklt).2 trivial
        have htest := hregular k order[k] hget hprev
        have hlow : (49 / 100 : ℝ) ≤
            rowDeg E G (anc9 ω order[k]) (prefixLaw9 E G ω μ order k) := by
          have habs := abs_le.mp htest
          have hb' : 2 * P.bStar n ≤ (1 / 100 : ℝ) := by linarith
          linarith
        have hpowpos : 0 < (49 / 100 : ℝ) ^ k := pow_pos (by norm_num) _
        have hmasspos : 0 < orderHitMass9 E G ω μ order k :=
          lt_of_lt_of_le hpowpos ih'.1
        have hstep := orderHitMassSucc9 E G ω μ order k hklt hmasspos
        have hmass : (49 / 100 : ℝ) ^ (k + 1) ≤
            orderHitMass9 E G ω μ order k *
              rowDeg E G (anc9 ω order[k]) (prefixLaw9 E G ω μ order k) := by
          calc
            (49 / 100 : ℝ) ^ (k + 1) = (49 / 100 : ℝ) ^ k * (49 / 100 : ℝ) := by rw [pow_succ]
            _ ≤ orderHitMass9 E G ω μ order k * (49 / 100 : ℝ) :=
              mul_le_mul_of_nonneg_right ih'.1 (by norm_num)
            _ ≤ orderHitMass9 E G ω μ order k *
                rowDeg E G (anc9 ω order[k]) (prefixLaw9 E G ω μ order k) :=
              mul_le_mul_of_nonneg_left hlow hmasspos.le
        constructor
        · rw [hstep]
          exact hmass
        · intro j c' hj hjget
          by_cases hjk : j < k
          · exact ih'.2 j c' hjk hjget
          · have hjeq : j = k := by omega
            subst j
            have hget' : order[k]? = some order[k] := hget
            have heq : some c' = some order[k] := hjget.symm.trans hget'
            have hc : c' = order[k] := Option.some.inj heq
            subst c'
            exact hlow
  intro k hk
  exact (haux k hk).1

/-- Prefix restrictions of an ordered star row are fixed by its scope anchors. -/
theorem prefixLawEqOfAnchors9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) {b : OddSites9 n}
    (ω ω' : Outcome9 I N) (base base' : Law N) (hbase : base = base')
    (order : List I.ID) (horder : ∀ c ∈ order, c ∈ I.seen b.1)
    (hanc : ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c) (k : ℕ) :
    prefixLaw9 E G ω base order k = prefixLaw9 E G ω' base' order k := by
  classical
  have hids : ∀ c ∈ (order.take k).toFinset, c ∈ I.seen b.1 := by
    intro c hc
    apply horder c
    have hc' : c ∈ order.take k := by simpa using hc
    exact (List.take_sublist k order).subset hc'
  have hhit := hitSetEqOfAnchors9 E G ω ω' (order.take k).toFinset
    (fun c hc => hanc c (hids c hc))
  unfold prefixLaw9
  rw [hbase, hhit]

/-- Sequential regularity tests are invariant when all anchors in their order agree. -/
theorem orderRegularEqOfAnchors9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) {b : OddSites9 n}
    (ω ω' : Outcome9 I N) (base base' : Law N) (hbase : base = base')
    (order : List I.ID) (horder : ∀ c ∈ order, c ∈ I.seen b.1)
    (hanc : ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c) :
    orderRegular9 E G ω base order = orderRegular9 E G ω' base' order := by
  classical
  apply propext
  constructor
  · intro h k c hkc hprev
    have hc : c ∈ order := List.mem_of_getElem? hkc
    have hcSeen := horder c hc
    have hprev' : ∀ j c', j < k → order[j]? = some c' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c')
          (prefixLaw9 E G ω base order j) := by
      intro j c' hj hjc
      have hc' : c' ∈ order := List.mem_of_getElem? hjc
      have hc'Seen := horder c' hc'
      have hpref := prefixLawEqOfAnchors9 E G ω ω' base base' hbase order horder hanc j
      have hbound := hprev j c' hj hjc
      rw [← hanc c' hc'Seen, ← hpref] at hbound
      exact hbound
    have hpref := prefixLawEqOfAnchors9 E G ω ω' base base' hbase order horder hanc k
    have hbound := h k c hkc hprev'
    rw [hanc c hcSeen, hpref] at hbound
    exact hbound
  · intro h k c hkc hprev
    have hc : c ∈ order := List.mem_of_getElem? hkc
    have hcSeen := horder c hc
    have hprev' : ∀ j c', j < k → order[j]? = some c' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω' c')
          (prefixLaw9 E G ω' base' order j) := by
      intro j c' hj hjc
      have hc' : c' ∈ order := List.mem_of_getElem? hjc
      have hc'Seen := horder c' hc'
      have hpref := prefixLawEqOfAnchors9 E G ω ω' base base' hbase order horder hanc j
      have hbound := hprev j c' hj hjc
      rw [hanc c' hc'Seen, hpref] at hbound
      exact hbound
    have hpref := prefixLawEqOfAnchors9 E G ω ω' base base' hbase order horder hanc k
    have hbound := h k c hkc hprev'
    rw [← hanc c hcSeen, ← hpref] at hbound
    exact hbound

/-- The three sequential regularity tests of a star depend only on its scope. -/
theorem starRegularEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) :
    starRegular9 S E G ω v = starRegular9 S E G ω' v := by
  classical
  have hanc (b : OddSites9 n) (hb : (cube n).Adj v.1 b.1) :
      ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c :=
    starScopeAnchorEq9 ω ω' hω b hb
  have hmask (b : OddSites9 n) (hb : (cube n).Adj v.1 b.1) :
      maskedLaw9 S ω b = maskedLaw9 S ω' b := by
    simp [maskedLaw9, starScopeMaskEq9 ω ω' hω b hb]
  have hfull (b : OddSites9 n) (hb : (cube n).Adj v.1 b.1) :
      ∀ c ∈ fullOrder9 I v b, c ∈ I.seen b.1 := fun c hc => fullOrderMemSeen9 hb hc
  have hcore (b : OddSites9 n) : ∀ c ∈ coreOrder9 I v b, c ∈ I.seen b.1 :=
    fun c hc => coreOrderMemSeen9 hc
  apply propext
  constructor
  · intro h b hb
    have he1 := orderRegularEqOfAnchors9 E G ω ω' (maskedLaw9 S ω b) (maskedLaw9 S ω' b)
      (hmask b hb) (fullOrder9 I v b) (hfull b hb) (hanc b hb)
    have he2 := orderRegularEqOfAnchors9 E G ω ω' (siteSecond9 S b.1) (siteSecond9 S b.1)
      rfl (fullOrder9 I v b) (hfull b hb) (hanc b hb)
    have he3 := orderRegularEqOfAnchors9 E G ω ω' (siteSecond9 S b.1) (siteSecond9 S b.1)
      rfl (coreOrder9 I v b) (hcore b) (hanc b hb)
    rcases h b hb with ⟨h1, h2, h3⟩
    exact ⟨he1.mp h1, he2.mp h2, he3.mp h3⟩
  · intro h b hb
    have he1 := orderRegularEqOfAnchors9 E G ω ω' (maskedLaw9 S ω b) (maskedLaw9 S ω' b)
      (hmask b hb) (fullOrder9 I v b) (hfull b hb) (hanc b hb)
    have he2 := orderRegularEqOfAnchors9 E G ω ω' (siteSecond9 S b.1) (siteSecond9 S b.1)
      rfl (fullOrder9 I v b) (hfull b hb) (hanc b hb)
    have he3 := orderRegularEqOfAnchors9 E G ω ω' (siteSecond9 S b.1) (siteSecond9 S b.1)
      rfl (coreOrder9 I v b) (hcore b) (hanc b hb)
    rcases h b hb with ⟨h1, h2, h3⟩
    exact ⟨he1.mpr h1, he2.mpr h2, he3.mpr h3⟩

/-- The log-gain and validity gate are fixed by a star scope. -/
theorem starGainEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) :
    starGain9 S E G ω v = starGain9 S E G ω' v := by
  classical
  unfold starGain9
  apply Finset.sum_congr rfl
  intro b hb
  have hcenter : anc9 ω (I.center v.1) = anc9 ω' (I.center v.1) :=
    starScopeAnchorEq9 ω ω' hω b.1 b.2 (I.center v.1) (centerSeen9 b.2)
  have hrows := starScopeRowsEq9 S E G ω ω' hω b.1 b.2
  simp [targetFrac9, hcenter, hrows.2 (I.center v.1)]

/-- The full star-validity predicate is fixed by a star scope. -/
theorem starValidEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) :
    starValid9 S E G ω v = starValid9 S E G ω' v := by
  unfold starValid9
  rw [starRegularEq9 S E G ω ω' hω, starGainEq9 S E G ω ω' hω]

/-- Replacing a star's target anchor preserves agreement on its scope. -/
theorem starScopeUpdAgree9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) (x : Fin N) :
    ∀ i ∈ starScope9 I v,
      updAnc9 ω (I.center v.1) x i = updAnc9 ω' (I.center v.1) x i := by
  classical
  intro i hi
  by_cases heq : i = Sum.inl (I.center v.1)
  · subst i
    change Function.update ω (Sum.inl (I.center v.1))
      (show Val9 I N (Sum.inl (I.center v.1)) from x) (Sum.inl (I.center v.1)) =
      Function.update ω' (Sum.inl (I.center v.1))
        (show Val9 I N (Sum.inl (I.center v.1)) from x) (Sum.inl (I.center v.1))
    rw [Function.update_self, Function.update_self]
  · change Function.update ω (Sum.inl (I.center v.1))
      (show Val9 I N (Sum.inl (I.center v.1)) from x) i =
      Function.update ω' (Sum.inl (I.center v.1))
        (show Val9 I N (Sum.inl (I.center v.1)) from x) i
    rw [Function.update_of_ne heq, Function.update_of_ne heq]
    exact hω i hi

/-- The gated row likelihoods on star data are fixed by the local scope. -/
theorem starScopeLikEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i)
    (x : Fin N) (ys : StarOdd9 v → Fin N) :
    starLik9 S E G ω v x ys = starLik9 S E G ω' v x ys := by
  classical
  let ωx := updAnc9 ω (I.center v.1) x
  let ω'x := updAnc9 ω' (I.center v.1) x
  have hupd := starScopeUpdAgree9 ω ω' hω x
  have hvalid := starValidEq9 S E G ωx ω'x hupd
  have hrow : ∀ b : StarOdd9 v, rowLaw9 S E G ωx b.1 = rowLaw9 S E G ω'x b.1 := by
    intro b
    exact (starScopeRowsEq9 S E G ωx ω'x hupd b.1 b.2).1
  simp [starLik9, ωx, ω'x, hvalid, hrow]

/-- The predictive marginal and deleted reference law on a star are fixed by its scope. -/
theorem starScopePosteriorEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) (ys : StarOdd9 v → Fin N) :
    starMarg9 S E G ω v ys = starMarg9 S E G ω' v ys ∧
      starRef9 S E G ω v ys = starRef9 S E G ω' v ys ∧
      predFail9 S E G ω v ys = predFail9 S E G ω' v ys := by
  classical
  have hMarg : starMarg9 S E G ω v ys = starMarg9 S E G ω' v ys := by
    unfold starMarg9
    apply Finset.sum_congr rfl
    intro x hx
    rw [starScopeLikEq9 S E G ω ω' hω x ys]
  have hRef : starRef9 S E G ω v ys = starRef9 S E G ω' v ys := by
    unfold starRef9
    apply Finset.prod_congr rfl
    intro b hb
    have hrows := starScopeRowsEq9 S E G ω ω' hω b.1 b.2
    exact congrArg (fun L : Law N => L.w (ys b)) (hrows.2 (I.center v.1))
  exact ⟨hMarg, hRef, by simp [predFail9, hMarg, hRef]⟩

/-- The alarm and bad-star event are fixed by a star scope. -/
theorem starScopeBadEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) :
    StarBad9 S E G ω v = StarBad9 S E G ω' v := by
  classical
  by_cases hn : n = 0
  · subst n
    haveI : IsEmpty (OddSites9 0) := ⟨fun b => b.2 (by simp [IsEvenRole])⟩
    haveI : IsEmpty (StarOdd9 v) := ⟨fun b => isEmptyElim b.1⟩
    have hvalid (η : Outcome9 I N) : starValid9 S E G η v := by
      constructor
      · intro b hb
        exact isEmptyElim b
      · simp [starGain9, gainConst9]
    have hlik (η : Outcome9 I N) (x : Fin N) (ys : StarOdd9 v → Fin N) :
        starLik9 S E G η v x ys = 1 := by
      simp [starLik9, hvalid]
    have hmarg (η : Outcome9 I N) (ys : StarOdd9 v → Fin N) :
        starMarg9 S E G η v ys = 1 := by
      unfold starMarg9
      simp_rw [hlik]
      simpa using (siteFirst9 S v.1).sum_eq_one
    have href (η : Outcome9 I N) (ys : StarOdd9 v → Fin N) :
        starRef9 S E G η v ys = 1 := by simp [starRef9]
    have hfail (η : Outcome9 I N) (ys : StarOdd9 v → Fin N) :
        ¬ predFail9 S E G η v ys := by
      simp [predFail9, hmarg, href, Params9.tail, gainConst9]
    have halarm (η : Outcome9 I N) : alarm9 S E G η v = 0 := by
      simp [alarm9, hlik, hfail]
    have hbad (η : Outcome9 I N) : ¬ StarBad9 S E G η v := by
      simp [StarBad9, hvalid, halarm, Params9.tail, gainConst9]
    apply propext
    constructor
    · intro h
      exact (hbad ω h).elim
    · intro h
      exact (hbad ω' h).elim
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let j : Fin n := ⟨0, hnpos⟩
    have hodd : ¬ IsEvenRole (cubeFlip v.1 j) := by
      intro hflip
      exact (cubeFlip_parity v.1 j).mp hflip v.2
    let b : OddSites9 n := ⟨cubeFlip v.1 j, hodd⟩
    have hb : (cube n).Adj v.1 b.1 := cubeFlip_adj v.1 j
    have hcenter : anc9 ω (I.center v.1) = anc9 ω' (I.center v.1) :=
      starScopeAnchorEq9 ω ω' hω b hb (I.center v.1) (centerSeen9 hb)
    have hvalid := starValidEq9 S E G ω ω' hω
    have halarm : alarm9 S E G ω v = alarm9 S E G ω' v := by
      unfold alarm9
      apply Finset.sum_congr rfl
      intro ys hys
      have hposterior := starScopePosteriorEq9 S E G ω ω' hω ys
      have hlik := starScopeLikEq9 S E G ω ω' hω (anc9 ω (I.center v.1)) ys
      rw [← hcenter, hlik, hposterior.2.2]
    unfold StarBad9
    rw [hvalid, halarm]

end HypercubeRamsey.Lane_q_s09_assign1
