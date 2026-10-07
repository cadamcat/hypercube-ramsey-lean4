import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Tools.ScatteredUnion

namespace HypercubeRamsey.Lane_q_s09_assign2

open HypercubeRamsey Classical OAI.HypercubeRamsey
open scoped BigOperators

private theorem scaleExps9_of_valid9 (P : Params9) (hP : P.Valid) : ScaleExps9 P := by
  rcases hP with ⟨⟨hxS, hxSxD, hxD⟩, ⟨hMinus, hMinusPlus, hPlus⟩,
    hxDPlus, ⟨hSigma, hSigmaXS⟩, ⟨hChi, hChiBound⟩, hGap, hBranch⟩
  have hxSR : (0 : ℝ) < (P.xS : ℝ) := by exact_mod_cast hxS
  have hSigmaR : (0 : ℝ) < (P.σ : ℝ) := by exact_mod_cast hSigma
  have hSigmaXS' : (P.σ : ℝ) < (P.xS : ℝ) / 10 := by exact_mod_cast hSigmaXS
  have hChiX : P.χ < P.xS / 100 := by
    have hmin : min P.xS (min P.hMinus (1 - P.hPlus)) ≤ P.xS := min_le_left _ _
    nlinarith
  have hChiXR : (P.χ : ℝ) < (P.xS : ℝ) / 100 := by exact_mod_cast hChiX
  have huPos : 0 < P.u := by
    simp [Params9.u]
    positivity
  have hSigmaU : (P.σ : ℝ) < P.u := by
    simp only [Params9.u]
    linarith
  have hChiU : (P.χ : ℝ) < P.u / 50 := by
    calc
      (P.χ : ℝ) < (P.xS : ℝ) / 100 := hChiXR
      _ = P.u / 50 := by simp [Params9.u]; ring
  refine ⟨?_, ?_, huPos, hSigmaU, hChiU⟩
  · cases hc : P.case with
    | sub yS yD yM =>
        have hsub : 0 < yS ∧ yS < yM ∧ yM < 1 - P.σ ∧
            1 - P.σ < yD ∧ yD < 1 ∧ P.χ < P.σ / 10 := by
          simpa [hc] using hBranch
        rcases hsub with ⟨hyS, hySYM, hyM, hyMYD, hyD, hyChi⟩
        have hgapR : 0 < (yD : ℝ) - (1 - (P.σ : ℝ)) := by exact_mod_cast (show 0 < yD - (1 - P.σ) by linarith)
        simpa [Params9.eps, hc] using
          (div_pos (lt_min hSigmaR hgapR) (by norm_num : (0 : ℝ) < 2))
    | lin αS αD hB yB =>
        have hlin : 0 < 100 * αS ∧ 100 * αS < αD ∧ αD < 1 / 100 ∧
            P.σ < P.χ / 10 ∧ P.hPlus < hB ∧ hB < 1 ∧ 0 < yB ∧ yB < 1 := by
          simpa [hc] using hBranch
        simpa [Params9.eps, hc] using
          (div_pos hSigmaR (by norm_num : (0 : ℝ) < 2))
  · cases hc : P.case with
    | sub yS yD yM =>
        have hsub : 0 < yS ∧ yS < yM ∧ yM < 1 - P.σ ∧
            1 - P.σ < yD ∧ yD < 1 ∧ P.χ < P.σ / 10 := by
          simpa [hc] using hBranch
        rcases hsub with ⟨hyS, hySYM, hyM, hyMYD, hyD, hyChi⟩
        have hmin : min (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))) ≤ (P.σ : ℝ) :=
          min_le_left _ _
        have hbound : min (P.σ : ℝ) ((yD : ℝ) - (1 - (P.σ : ℝ))) / 2 < (P.σ : ℝ) := by
          nlinarith [hSigmaR, hmin]
        simpa [Params9.eps, hc] using hbound
    | lin αS αD hB yB =>
        have hlin : 0 < 100 * αS ∧ 100 * αS < αD ∧ αD < 1 / 100 ∧
            P.σ < P.χ / 10 ∧ P.hPlus < hB ∧ hB < 1 ∧ 0 < yB ∧ yB < 1 := by
          simpa [hc] using hBranch
        have hbound : (P.σ : ℝ) / 2 < (P.σ : ℝ) := by linarith
        simpa [Params9.eps, hc] using hbound

private theorem hplus_log_le_pow9 (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 ≤ 4 * (n : ℝ) ^ P.u := by
  have hexps : ScaleExps9 P := scaleExps9_of_valid9 P hP
  have hu : 0 < P.u := hexps.2.2.1
  let hp : ℝ := P.hPlus
  let C : ℝ := 1 / (4 * (hp + 1))
  have hplusRat : 0 < P.hPlus := lt_trans hP.2.1.1 hP.2.1.2.1
  have hpNonneg : 0 ≤ hp := by
    change (0 : ℝ) ≤ (P.hPlus : ℝ)
    exact_mod_cast hplusRat.le
  have hpOnePos : 0 < hp + 1 := by linarith
  have hdenPos : 0 < 4 * (hp + 1) := mul_pos (by norm_num) hpOnePos
  have hC : 0 < C := by dsimp [C]; exact div_pos (by norm_num) hdenPos
  have hlogLittle := isLittleO_log_rpow_atTop hu
  have hlogEvent : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.log x‖ ≤ C * ‖x ^ P.u‖ :=
    (Asymptotics.isLittleO_iff.mp hlogLittle) hC
  have hlogNat : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Real.log (n : ℝ)‖ ≤ C * ‖(n : ℝ) ^ P.u‖ :=
    tendsto_natCast_atTop_atTop.eventually hlogEvent
  have hpowNat : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ (n : ℝ) ^ P.u := by
    have ht := (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
    exact ht.eventually (Filter.eventually_atTop.2 ⟨4, fun _ h => h⟩)
  rcases Filter.eventually_atTop.1 hlogNat with ⟨n₁, hn₁⟩
  rcases Filter.eventually_atTop.1 hpowNat with ⟨n₂, hn₂⟩
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn
  have hn₁' : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂' : n₂ ≤ n := le_trans (le_max_right _ _) hn
  have hlog := hn₁ n hn₁'
  have hpow := hn₂ n hn₂'
  have hnpos : 0 < n := by
    by_contra hnpos
    have hn0 : n = 0 := by omega
    subst n
    have hzero : (0 : ℝ) ^ P.u = 0 := Real.zero_rpow (ne_of_gt hu)
    have hpow0 : 4 ≤ (0 : ℝ) ^ P.u := by simpa using hpow
    rw [hzero] at hpow0
    norm_num at hpow0
  have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hpowNonneg : 0 ≤ (n : ℝ) ^ P.u := by positivity
  have hlogBound : Real.log (n : ℝ) ≤ C * (n : ℝ) ^ P.u := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlognonneg, abs_of_nonneg hpowNonneg] using hlog
  have hcoeff : hp * C ≤ 1 / 4 := by
    calc
      hp * C = hp / (4 * (hp + 1)) := by dsimp [C]; ring
      _ ≤ 1 / 4 := (div_le_iff₀ hdenPos).2 (by nlinarith [hpNonneg])
  have hmul := mul_le_mul_of_nonneg_left hlogBound hpNonneg
  calc
    hp * Real.log (n : ℝ) + 1 ≤ hp * (C * (n : ℝ) ^ P.u) + 1 := by
      linarith
    _ ≤ (1 / 4 : ℝ) * (n : ℝ) ^ P.u + 1 := by
      nlinarith [mul_nonneg hpowNonneg (sub_nonneg.mpr hcoeff)]
    _ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ P.u := by nlinarith
    _ ≤ 4 * (n : ℝ) ^ P.u := by nlinarith

private theorem hammingBall_card_poly {d r : ℕ} (v : CubeVertex d) :
    (hammingBall v r).card ≤ (d + 1) ^ (r + 1) := by
  classical
  let support : CubeVertex d → Finset (Fin d) := fun u =>
    Finset.univ.filter (fun i => u i ≠ v i)
  let B := hammingBall v r
  let Q := (Finset.univ : Finset (Fin d)).powerset.filter (fun s => s.card ≤ r)
  have hsupportDist (u : CubeVertex d) : (support u).card = hammingDist v u := by
    simp [support, hammingDist, ne_comm]
  have hinj : Set.InjOn support (B : Set (CubeVertex d)) := by
    intro x hx y hy hxy
    funext i
    have hiff : x i ≠ v i ↔ y i ≠ v i := by
      have h := congrArg (fun s : Finset (Fin d) => i ∈ s) hxy
      simpa [support] using h
    cases hv : v i <;> cases hxv : x i <;> cases hyv : y i <;> simp_all
  have hsubset : B.image support ⊆ Q := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    have hu' : u ∈ hammingBall v r := by simpa [B] using hu
    have hdistle : hammingDist v u ≤ r := (Finset.mem_filter.mp hu').2
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
  have hQbound : Q.card ≤ (d + 1) ^ (r + 1) := by
    rw [hQsum]
    calc
      (∑ k ∈ Finset.range (d + 1), if k ≤ r then Nat.choose d k else 0) ≤
          ∑ k ∈ Finset.range (d + 1), (d + 1) ^ r := by
            apply Finset.sum_le_sum
            intro k hk
            by_cases hkr : k ≤ r
            · simp only [if_pos hkr]
              calc
                Nat.choose d k ≤ d ^ k := Nat.choose_le_pow d k
                _ ≤ (d + 1) ^ k := by gcongr; omega
                _ ≤ (d + 1) ^ r := by gcongr
            · simp [hkr]
      _ = (d + 1) * (d + 1) ^ r := by simp
      _ = (d + 1) ^ (r + 1) := by rw [Nat.pow_succ]; ring
  exact hcard.trans hQbound

private def glueCube9 {m n : ℕ} (hm : m ≤ n)
    (p : CubeVertex m × CubeVertex (n - m)) : CubeVertex n :=
  fun i => if hi : (i : ℕ) < m then p.1 ⟨i, hi⟩ else p.2 ⟨(i : ℕ) - m, by omega⟩

private def cubeSplit9 {m n : ℕ} (hm : m ≤ n) :
    CubeVertex n ≃ CubeVertex m × CubeVertex (n - m) where
  toFun v := (specialWord9 m v, residualWord9 m v)
  invFun := glueCube9 hm
  left_inv v := by
    funext i
    by_cases hi : (i : ℕ) < m
    · simp [glueCube9, specialWord9, hi, show (i : ℕ) < n by omega]
    · simp [glueCube9, residualWord9, hi]
      congr 1
      apply Fin.ext
      exact Nat.add_sub_of_le (Nat.le_of_not_gt hi)
  right_inv p := by
    rcases p with ⟨s, r⟩
    apply Prod.ext
    · funext j
      simp [specialWord9, glueCube9, show (j : ℕ) < n by omega]
    · funext j
      simp [residualWord9, glueCube9]

private theorem sum_specialWord9 {m n : ℕ} (hm : m ≤ n) (g : CubeVertex m → ℝ) :
    (∑ v : CubeVertex n, g (specialWord9 m v)) =
      (2 : ℝ) ^ (n - m) * ∑ z : CubeVertex m, g z := by
  classical
  calc
    (∑ v : CubeVertex n, g (specialWord9 m v)) =
        ∑ p : CubeVertex m × CubeVertex (n - m), g p.1 :=
      Fintype.sum_equiv (cubeSplit9 hm) _ _ (by intro v; rfl)
    _ = ∑ z : CubeVertex m, ∑ r : CubeVertex (n - m), g z := by
      rw [Fintype.sum_prod_type]
    _ = ∑ z : CubeVertex m, (2 : ℝ) ^ (n - m) * g z := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [OAI.HypercubeRamsey.card_cubeVertex]
    _ = (2 : ℝ) ^ (n - m) * ∑ z : CubeVertex m, g z := by
      rw [← Finset.mul_sum]

private theorem siteNear_card_poly {P : Params9} {n : ℕ} (hm : P.m n ≤ n)
    (v : CubeVertex n) :
    (Finset.univ.filter (fun w : CubeVertex n => siteNear9 P n v w)).card ≤
      (n + 1) ^ (4 * P.radius n + 14) := by
  classical
  let m := P.m n
  let r := P.radius n
  let Near := Finset.univ.filter (fun w : CubeVertex n => siteNear9 P n v w)
  let A := hammingBall (specialWord9 m v) 4
  let B := hammingBall (residualWord9 m v) (4 * r + 8)
  have hA : A.card ≤ (m + 1) ^ 5 := by
    simpa [A] using hammingBall_card_poly (r := 4) (specialWord9 m v)
  have hB : B.card ≤ (n - m + 1) ^ (4 * r + 9) := by
    simpa [B, Nat.add_assoc] using
      hammingBall_card_poly (r := 4 * r + 8) (residualWord9 m v)
  let embed (w : Near) : A × B :=
    (⟨specialWord9 m w.1, by
        change specialWord9 m w.1 ∈ hammingBall (specialWord9 m v) 4
        rw [hammingBall]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp w.2).2.1⟩⟩,
      ⟨residualWord9 m w.1, by
        change residualWord9 m w.1 ∈ hammingBall (residualWord9 m v) (4 * r + 8)
        rw [hammingBall]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp w.2).2.2⟩⟩)
  have hinj : Function.Injective embed := by
    intro w w' h
    apply Subtype.ext
    apply (cubeSplit9 (m := m) (n := n) (by simpa [m] using hm)).injective
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg Prod.fst h)
    · exact congrArg Subtype.val (congrArg Prod.snd h)
  have hcount : Near.card ≤ Fintype.card (A × B) := by
    calc
      Near.card = Fintype.card Near := (Fintype.card_coe Near).symm
      _ ≤ Fintype.card (A × B) := Fintype.card_le_of_injective embed hinj
  have hprod : A.card * B.card ≤ (m + 1) ^ 5 * (n - m + 1) ^ (4 * r + 9) :=
    Nat.mul_le_mul hA hB
  have hm₁ : m + 1 ≤ n + 1 := Nat.add_le_add_right (by simpa [m] using hm) 1
  have hm₂ : n - m + 1 ≤ n + 1 := by omega
  have hpow : (m + 1) ^ 5 * (n - m + 1) ^ (4 * r + 9) ≤
      (n + 1) ^ 5 * (n + 1) ^ (4 * r + 9) := by
    exact Nat.mul_le_mul (by gcongr) (by gcongr)
  calc
    Near.card ≤ Fintype.card (A × B) := hcount
    _ = A.card * B.card := by simp
    _ ≤ (m + 1) ^ 5 * (n - m + 1) ^ (4 * r + 9) := hprod
    _ ≤ (n + 1) ^ 5 * (n + 1) ^ (4 * r + 9) := hpow
    _ = (n + 1) ^ (4 * r + 14) := by
      rw [← pow_add]
      congr 1
      omega

private theorem siteNear9_symm {P : Params9} {n : ℕ} (v w : CubeVertex n)
    (h : siteNear9 P n v w) : siteNear9 P n w v := by
  rcases h with ⟨hs, hr⟩
  exact ⟨by simpa [hammingDist_comm] using hs,
    by simpa [hammingDist_comm] using hr⟩

private theorem evenSites_card9 {n : ℕ} (hn : 0 < n) :
    Fintype.card (EvenSites9 n) = 2 ^ (n - 1) := by
  classical
  let e : EvenSites9 n ≃ {v : CubeVertex n // v ∈ evenRoleSet n} :=
    (Equiv.refl _).subtypeEquiv (by intro v; simp [evenRoleSet])
  calc
    Fintype.card (EvenSites9 n) = Fintype.card {v : CubeVertex n // v ∈ evenRoleSet n} :=
      Fintype.card_congr e
    _ = (evenRoleSet n).card := Fintype.card_coe _
    _ = 2 ^ (n - 1) := (parity_class_card hn).1

private theorem sum_even_sites_le_cube {n : ℕ} (f : CubeVertex n → ℝ)
    (hf : ∀ v, 0 ≤ f v) :
    (∑ v : EvenSites9 n, f v.1) ≤ ∑ v : CubeVertex n, f v := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype IsEvenRole f
  have hodd : 0 ≤ ∑ v : {v : CubeVertex n // ¬ IsEvenRole v}, f v.1 :=
    Finset.sum_nonneg fun v hv => hf v.1
  have hsplit' :
      (∑ v : EvenSites9 n, f v.1) +
          (∑ v : {v : CubeVertex n // ¬ IsEvenRole v}, f v.1) =
        ∑ v : CubeVertex n, f v := by
    simpa [EvenSites9] using hsplit
  linarith

private theorem evenSiteNear_card_poly {P : Params9} {n : ℕ} (hm : P.m n ≤ n)
    (v : EvenSites9 n) :
    (Finset.univ.filter (fun w : EvenSites9 n => siteNear9 P n v.1 w.1)).card ≤
      (n + 1) ^ (4 * P.radius n + 14) := by
  classical
  let A : Finset (EvenSites9 n) :=
    Finset.univ.filter (fun w => siteNear9 P n v.1 w.1)
  let B : Finset (CubeVertex n) :=
    Finset.univ.filter (fun w => siteNear9 P n v.1 w)
  have hcardMap : A.card = (A.image (fun w : EvenSites9 n => w.1)).card := by
    symm
    exact Finset.card_image_of_injective A Subtype.val_injective
  have hsubset : A.image (fun w : EvenSites9 n => w.1) ⊆ B := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
  calc
    A.card = (A.image (fun w : EvenSites9 n => w.1)).card := hcardMap
    _ ≤ B.card := Finset.card_le_card hsubset
    _ ≤ (n + 1) ^ (4 * P.radius n + 14) := siteNear_card_poly hm v.1

private theorem updAnc9_overwrite {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (ω : Outcome9 I N) (c : I.ID) (x x' : Fin N) :
    updAnc9 (updAnc9 ω c x') c x = updAnc9 ω c x := by
  funext j
  by_cases hj : j = Sum.inl c <;> simp [updAnc9, Function.update, hj]

private theorem anc9_update_ne {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (ω : Outcome9 I N) (c c' : I.ID) (x : Fin N) (h : c' ≠ c) :
    anc9 (updAnc9 ω c x) c' = anc9 ω c' := by
  have hne : (Sum.inl c' : I.ID ⊕ OddSites9 n) ≠ Sum.inl c := by
    intro heq
    cases heq
    exact h rfl
  unfold anc9 updAnc9
  rw [Function.update_of_ne hne]

private theorem center_mem_seen9 {P : Params9} {n : ℕ}
    {I : IDMap9 P n} {v : EvenSites9 n} (b : StarOdd9 v) :
    I.center v.1 ∈ I.seen b.1.1 := by
  classical
  change I.center v.1 ∈ seenIDs9 I.center b.1.1
  apply Finset.mem_image.mpr
  refine ⟨v.1, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, (cube n).adj_symm b.2⟩

private theorem hitSet9_erase_inter_target {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω : Outcome9 I N) (b : StarOdd9 v) (x : Fin N) :
    hitSet9 E G (updAnc9 ω (I.center v.1) x) (I.seen b.1.1) =
      hitSet9 E G (updAnc9 ω (I.center v.1) x) ((I.seen b.1.1).erase (I.center v.1)) ∩
        Finset.univ.filter (fun y => Hits E G x y) := by
  classical
  let c := I.center v.1
  have hc : c ∈ I.seen b.1.1 := by simpa [c] using center_mem_seen9 b
  have hanc : anc9 (updAnc9 ω c x) c = x := by simp [anc9, updAnc9, c, Function.update]
  ext y
  simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter]
  constructor
  · intro hall
    constructor
    · intro d hd
      exact hall d (Finset.mem_of_mem_erase hd)
    · have hh := hall c hc
      rw [hanc] at hh
      exact hh
  · rintro ⟨hall, hx⟩ d hd
    by_cases hdc : d = c
    · subst d
      rw [hanc]
      exact hx
    · exact hall d (Finset.mem_erase.mpr ⟨hdc, hd⟩)

private theorem orderRegular9_prefix_lower {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (base : Law N) (order : List I.ID)
    (horder : orderRegular9 E G ω base order) (hbStar : P.bStar n ≤ 1 / 200) :
    ∀ i c, order[i]? = some c →
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro c hget
      have hprev : ∀ j c', j < i → order[j]? = some c' →
          (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c') (prefixLaw9 E G ω base order j) := by
        intro j c' hji hget'
        exact ih j hji c' hget'
      have hreg := horder i c hget hprev
      have hlow := (abs_le.mp hreg).1
      nlinarith

private theorem targetFrac9_pos_of_starValid {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (hvalid : starValid9 S E G ω v)
    (hbStar : P.bStar n ≤ 1 / 200) (b : StarOdd9 v) :
    0 < targetFrac9 S E G ω v b.1 := by
  let c := I.center v.1
  let O := outerIDs9 I v b.1
  let C := coreIDs9 I v b.1
  let pre := O.toList ++ C.toList
  let order := fullOrder9 I v b.1
  let k := pre.length
  have hcCore : c ∈ I.core v.1 := by
    exact I.center_mem_core v.1 v.2
  have hcSeen : c ∈ I.seen b.1.1 := by
    simpa [c] using center_mem_seen9 b
  have hsets : O ∪ C = (I.seen b.1.1).erase c := by
    classical
    ext d
    simp only [Finset.mem_union, O, C, outerIDs9, coreIDs9,
      Finset.mem_sdiff, Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro (⟨hdseen, hdnotcore⟩ | ⟨hdc, hdseen, hdcore⟩)
      · refine ⟨?_, hdseen⟩
        intro hdc
        subst d
        exact hdnotcore hcCore
      · exact ⟨by simpa [c] using hdc, hdseen⟩
    · rintro ⟨hdc, hdseen⟩
      by_cases hdcore : d ∈ I.core v.1
      · exact Or.inr ⟨by simpa [c] using hdc, hdseen, hdcore⟩
      · exact Or.inl ⟨hdseen, hdcore⟩
  have hpreFin : pre.toFinset = O ∪ C := by
    simp [pre, List.toFinset_append]
  have horderEq : order = pre ++ [c] := by
    simp [order, pre, O, C, c, fullOrder9]
  have hget : order[k]? = some c := by simp [horderEq, k]
  have htake : order.take k = pre := by simp [horderEq, k]
  have hpreIDs : (order.take k).toFinset = (I.seen b.1.1).erase c := by
    rw [htake, hpreFin, hsets]
  have hprefix :
      prefixLaw9 E G ω (maskedLaw9 S ω b.1) order k =
        delLaw9 S E G ω b.1 c := by
    simp [prefixLaw9, delLaw9, hpreIDs]
  have hregular := hvalid.1 b.1 b.2
  have hlow := orderRegular9_prefix_lower E G ω (maskedLaw9 S ω b.1) order
    hregular.1 hbStar k c hget
  have hq : (49 / 100 : ℝ) ≤ targetFrac9 S E G ω v b.1 := by
    unfold targetFrac9
    rw [← hprefix]
    exact hlow
  linarith

private theorem rowDeg_le_one9 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (x : Fin N) : rowDeg E G x μ ≤ 1 := by
  classical
  unfold rowDeg
  calc
    (∑ y, μ.w y * (if Hits E G x y then 1 else 0)) ≤ ∑ y, μ.w y := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases h : Hits E G x y
      · simp [h]
      · simp [h, μ.nonneg y]
    _ = 1 := μ.sum_eq_one

private theorem restrictOr9_target_ratio9 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (D : Finset (Fin N)) (x : Fin N)
    (hq : 0 < rowDeg E G x (restrictOr9 μ D)) (y : Fin N) :
    (restrictOr9 μ (D.filter (fun z => Hits E G x z))).w y ≤
      (restrictOr9 μ D).w y / rowDeg E G x (restrictOr9 μ D) := by
  classical
  let A := D.filter (fun z => Hits E G x z)
  let mD := ∑ z ∈ D, μ.w z
  let mA := ∑ z ∈ A, μ.w z
  have hA_sub : A ⊆ D := by simp [A]
  have hmD_nonneg : 0 ≤ mD := by
    dsimp [mD]
    exact Finset.sum_nonneg fun z hz => μ.nonneg z
  have hmA_nonneg : 0 ≤ mA := by
    dsimp [mA]
    exact Finset.sum_nonneg fun z hz => μ.nonneg z
  have hmA_le : mA ≤ mD := by
    dsimp [mA, mD]
    exact Finset.sum_le_sum_of_subset_of_nonneg hA_sub
      (by intro z hz hnot; exact μ.nonneg z)
  by_cases hD : 0 < mD
  · have hDlaw : restrictOr9 μ D = Law.restrict μ D hD := by
      simp [restrictOr9, mD, hD]
    have hqeq : rowDeg E G x (restrictOr9 μ D) = mA / mD := by
      rw [hDlaw]
      unfold rowDeg
      simp only [Law.restrict]
      have hterm (z : Fin N) :
          (if z ∈ D then μ.w z / mD else 0) * (if Hits E G x z then 1 else 0) =
            if z ∈ A then μ.w z / mD else 0 := by
        by_cases hz : Hits E G x z <;> by_cases hDmem : z ∈ D <;>
          simp [A, hz, hDmem]
      calc
        _ = ∑ z, if z ∈ A then μ.w z / mD else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          simpa [Law.restrict, mD] using hterm z
        _ = ∑ z ∈ A, μ.w z / mD := by rw [Finset.sum_ite_mem_eq]
        _ = (∑ z ∈ A, μ.w z) / mD := by rw [Finset.sum_div]
        _ = mA / mD := by rfl
    have hApos : 0 < mA := by
      by_contra hnot
      have hzero : mA = 0 := le_antisymm (le_of_not_gt hnot) hmA_nonneg
      rw [hqeq, hzero] at hq
      simp [mD] at hq
    have hAlaw : restrictOr9 μ A = Law.restrict μ A hApos := by
      simp [restrictOr9, mA, hApos]
    rw [hAlaw, hDlaw]
    have hqeq' : rowDeg E G x (Law.restrict μ D hD) = mA / mD := by
      simpa [hDlaw] using hqeq
    rw [hqeq']
    by_cases hyA : y ∈ A
    · have hyD : y ∈ D := hA_sub hyA
      have heq : (Law.restrict μ A hApos).w y =
          (Law.restrict μ D hD).w y / (mA / mD) := by
        simp [Law.restrict, hyA, hyD]
        have hsumApos : 0 < ∑ z ∈ A, μ.w z := by simpa [mA] using hApos
        have hsumDpos : 0 < ∑ z ∈ D, μ.w z := by simpa [mD] using hD
        field_simp [ne_of_gt hsumApos, ne_of_gt hsumDpos]
        dsimp [mA, mD]
        ring
      exact heq.le
    · simp [Law.restrict, hyA, mA, mD]
      apply div_nonneg
      · exact (Law.restrict μ D hD).nonneg y
      · exact (div_pos hApos hD).le
  · have hDzero : mD = 0 := le_antisymm (le_of_not_gt hD) hmD_nonneg
    have hAzero : mA = 0 := le_antisymm (hmA_le.trans_eq hDzero) hmA_nonneg
    have hDlaw : restrictOr9 μ D = μ := by simp [restrictOr9, mD, hDzero]
    have hAlaw : restrictOr9 μ A = μ := by simp [restrictOr9, mA, hAzero]
    rw [hAlaw, hDlaw]
    have hqμ : 0 < rowDeg E G x μ := by simpa [hDlaw] using hq
    have hqle : rowDeg E G x μ ≤ 1 := rowDeg_le_one9 E G μ x
    apply (le_div_iff₀ hqμ).2
    calc
      μ.w y * rowDeg E G x μ ≤ μ.w y * 1 :=
        mul_le_mul_of_nonneg_left hqle (μ.nonneg y)
      _ = μ.w y := by ring

private theorem rowDeg_restrict9_eq_filter_mass_div {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) (μ : Law N) (D : Finset (Fin N)) (x : Fin N)
    (hD : 0 < ∑ z ∈ D, μ.w z) :
    rowDeg E G x (Law.restrict μ D hD) =
      (∑ z ∈ D.filter (fun y => Hits E G x y), μ.w z) / (∑ z ∈ D, μ.w z) := by
  classical
  let A := D.filter (fun z => Hits E G x z)
  let mD := ∑ z ∈ D, μ.w z
  have hterm (z : Fin N) :
      (if z ∈ D then μ.w z / mD else 0) * (if Hits E G x z then 1 else 0) =
        if z ∈ A then μ.w z / mD else 0 := by
    by_cases hz : Hits E G x z <;> by_cases hmem : z ∈ D <;> simp [A, hz, hmem]
  calc
    rowDeg E G x (Law.restrict μ D hD) =
        ∑ z, if z ∈ A then μ.w z / mD else 0 := by
          unfold rowDeg
          apply Finset.sum_congr rfl
          intro z hz
          simpa [Law.restrict, mD] using hterm z
    _ = ∑ z ∈ A, μ.w z / mD := by rw [Finset.sum_ite_mem_eq]
    _ = (∑ z ∈ A, μ.w z) / mD := by rw [Finset.sum_div]
    _ = _ := by rfl

private theorem restrictOr9_filter_mass_pos {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (D : Finset (Fin N)) (x : Fin N) (hD : 0 < ∑ z ∈ D, μ.w z)
    (hq : 0 < rowDeg E G x (Law.restrict μ D hD)) :
    0 < ∑ z ∈ D.filter (fun y => Hits E G x y), μ.w z := by
  classical
  let A := D.filter (fun y => Hits E G x y)
  let mA := ∑ z ∈ A, μ.w z
  have hmA_nonneg : 0 ≤ mA := by
    dsimp [mA]
    exact Finset.sum_nonneg fun z hz => μ.nonneg z
  have hratio := rowDeg_restrict9_eq_filter_mass_div E G μ D x hD
  by_contra hnot
  have hzero : mA = 0 := le_antisymm (le_of_not_gt hnot) hmA_nonneg
  have hqzero : rowDeg E G x (Law.restrict μ D hD) = 0 := by
    have hzero' : (∑ z ∈ D.filter (fun y => Hits E G x y), μ.w z) = 0 := by
      simpa [A, mA] using hzero
    rw [hratio, hzero']
    simp
  exact (ne_of_gt hq) hqzero

private theorem orderRegular9_prefix_mass_pos {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (base : Law N) (order : List I.ID)
    (horder : orderRegular9 E G ω base order) (hbStar : P.bStar n ≤ 1 / 200) :
    ∀ k, k ≤ order.length →
      0 < ∑ y ∈ hitSet9 E G ω (order.take k).toFinset, base.w y := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      cases k with
      | zero =>
          have hset : hitSet9 E G ω (order.take 0).toFinset = Finset.univ := by
            simp [hitSet9]
          rw [hset, base.sum_eq_one]
          norm_num
      | succ k =>
          have hklt : k < order.length := by omega
          have hget : order[k]? = some order[k] := by
            exact List.getElem?_eq_getElem hklt
          have htake : order.take (k + 1) = order.take k ++ [order[k]] := by
            rw [← List.take_append_getElem hklt]
          let Hk := hitSet9 E G ω (order.take k).toFinset
          let Hnext := hitSet9 E G ω (order.take (k + 1)).toFinset
          let mPrev := ∑ y ∈ Hk, base.w y
          have hprev : 0 < mPrev := by
            simpa [mPrev, Hk] using ih k (by omega) (by omega)
          have hnextSet : Hnext = Hk.filter (fun y => Hits E G (anc9 ω order[k]) y) := by
            change hitSet9 E G ω (order.take (k + 1)).toFinset =
              (hitSet9 E G ω (order.take k).toFinset).filter
                (fun y => Hits E G (anc9 ω order[k]) y)
            rw [htake]
            have hids : (order.take k ++ [order[k]]).toFinset =
                insert order[k] (order.take k).toFinset := by
              ext z
              simp only [List.mem_toFinset, List.mem_append, List.mem_singleton,
                Finset.mem_insert]
              tauto
            rw [hids]
            ext y
            simp [hitSet9, Hk] <;> tauto
          have hprefix : prefixLaw9 E G ω base order k = Law.restrict base Hk hprev := by
            simp [prefixLaw9, restrictOr9, Hk, mPrev, hprev]
          have hlow := orderRegular9_prefix_lower E G ω base order horder hbStar
            k (order[k]) hget
          rw [hprefix] at hlow
          have hratio := rowDeg_restrict9_eq_filter_mass_div E G base Hk
            (anc9 ω order[k]) hprev
          have hratio' : rowDeg E G (anc9 ω order[k]) (Law.restrict base Hk hprev) =
              (∑ y ∈ Hnext, base.w y) / mPrev := by
            rw [hratio, ← hnextSet]
          have hqpos : 0 < rowDeg E G (anc9 ω order[k]) (Law.restrict base Hk hprev) :=
            lt_of_lt_of_le (by norm_num : (0 : ℝ) < 49 / 100) hlow
          have hnextpos : 0 < ∑ y ∈ Hnext, base.w y := by
            have hprevEq :
                (∑ y ∈ Hnext, base.w y) =
                  rowDeg E G (anc9 ω order[k]) (Law.restrict base Hk hprev) * mPrev := by
              calc
                (∑ y ∈ Hnext, base.w y) =
                    ((∑ y ∈ Hnext, base.w y) / mPrev) * mPrev := by
                      field_simp [ne_of_gt hprev]
                _ = rowDeg E G (anc9 ω order[k]) (Law.restrict base Hk hprev) * mPrev := by
                      rw [← hratio']
            rw [hprevEq]
            exact mul_pos hqpos hprev
          simpa [Hnext] using hnextpos

private theorem starTargetDeletionMass_pos9 {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (hvalid : starValid9 S E G ω v)
    (hbStar : P.bStar n ≤ 1 / 200) (b : StarOdd9 v) :
    0 < ∑ y ∈ hitSet9 E G ω ((I.seen b.1.1).erase (I.center v.1)),
      (maskedLaw9 S ω b.1).w y := by
  let c := I.center v.1
  let O := outerIDs9 I v b.1
  let C := coreIDs9 I v b.1
  let pre := O.toList ++ C.toList
  let order := fullOrder9 I v b.1
  let k := pre.length
  have hcCore : c ∈ I.core v.1 := I.center_mem_core v.1 v.2
  have hcSeen : c ∈ I.seen b.1.1 := by
    simpa [c] using center_mem_seen9 b
  have hsets : O ∪ C = (I.seen b.1.1).erase c := by
    classical
    ext d
    simp only [Finset.mem_union, O, C, outerIDs9, coreIDs9,
      Finset.mem_sdiff, Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro (⟨hdseen, hdnotcore⟩ | ⟨hdc, hdseen, hdcore⟩)
      · refine ⟨?_, hdseen⟩
        intro hdc
        subst d
        exact hdnotcore hcCore
      · exact ⟨by simpa [c] using hdc, hdseen⟩
    · rintro ⟨hdc, hdseen⟩
      by_cases hdcore : d ∈ I.core v.1
      · exact Or.inr ⟨by simpa [c] using hdc, hdseen, hdcore⟩
      · exact Or.inl ⟨hdseen, hdcore⟩
  have hpreFin : pre.toFinset = O ∪ C := by
    simp [pre, List.toFinset_append]
  have horderEq : order = pre ++ [c] := by
    simp [order, pre, O, C, c, fullOrder9]
  have htake : order.take k = pre := by simp [horderEq, k]
  have hpreIDs : (order.take k).toFinset = (I.seen b.1.1).erase c := by
    rw [htake, hpreFin, hsets]
  have hregular := hvalid.1 b.1 b.2
  have hmass := orderRegular9_prefix_mass_pos E G ω (maskedLaw9 S ω b.1) order
    hregular.1 hbStar k (by simp [horderEq, k])
  rw [hpreIDs] at hmass
  exact hmass

theorem rowLaw9_hit_of_nonzero9 {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) (b : StarOdd9 v) (y : Fin N)
    (hvalid : starValid9 S E G (updAnc9 ω (I.center v.1) x) v)
    (hbStar : P.bStar n ≤ 1 / 200)
    (hy : (rowLaw9 S E G (updAnc9 ω (I.center v.1) x) b.1).w y ≠ 0) :
    Hits E G x y := by
  classical
  let c := I.center v.1
  let ω' := updAnc9 ω c x
  let ids := I.seen b.1.1
  let D := hitSet9 E G ω' (ids.erase c)
  let A := D.filter (fun z => Hits E G x z)
  let μ := maskedLaw9 S ω' b.1
  have hDpos := starTargetDeletionMass_pos9 S E G ω' v hvalid hbStar b
  have hq : 0 < targetFrac9 S E G ω' v b.1 :=
    targetFrac9_pos_of_starValid S E G ω' v hvalid hbStar b
  have hrowSet : hitSet9 E G ω' ids = A := by
    rw [hitSet9_erase_inter_target (M := M) E G ω b x]
    ext z
    simp [D, A, ω', ids, c]
  have hDpos' : 0 < ∑ z ∈ D, μ.w z := by
    simpa [D, μ, ω', ids, c] using hDpos
  have hDlaw : delLaw9 S E G ω' b.1 c = Law.restrict μ D hDpos' := by
    change restrictOr9 μ D = Law.restrict μ D hDpos'
    simp [restrictOr9, hDpos']
  have hden : rowDeg E G x (delLaw9 S E G ω' b.1 c) = targetFrac9 S E G ω' v b.1 := by
    simp [targetFrac9, ω', c, anc9, updAnc9, Function.update]
  rw [hDlaw] at hden
  have hq' : 0 < rowDeg E G x (Law.restrict μ D hDpos') := by
    rw [hden]
    exact hq
  have hApos : 0 < ∑ z ∈ A, μ.w z := by
    simpa [A] using restrictOr9_filter_mass_pos E G μ D x hDpos' hq'
  have hrowlaw : rowLaw9 S E G ω' b.1 = Law.restrict μ A hApos := by
    change restrictOr9 μ (hitSet9 E G ω' ids) = Law.restrict μ A hApos
    rw [hrowSet]
    change restrictOr9 μ A = Law.restrict μ A hApos
    simp [restrictOr9, hApos]
  have hyA : y ∈ A := by
    by_contra hyA
    have hzero : (Law.restrict μ A hApos).w y = 0 := by simp [Law.restrict, hyA]
    rw [hrowlaw] at hy
    exact hy hzero
  exact (Finset.mem_filter.mp hyA).2

private theorem rowLaw9_le_delLaw9_div_target {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) (b : StarOdd9 v) (y : Fin N)
    (hvalid : starValid9 S E G (updAnc9 ω (I.center v.1) x) v)
    (hbStar : P.bStar n ≤ 1 / 200) :
    (rowLaw9 S E G (updAnc9 ω (I.center v.1) x) b.1).w y ≤
      (delLaw9 S E G ω b.1 (I.center v.1)).w y /
        targetFrac9 S E G (updAnc9 ω (I.center v.1) x) v b.1 := by
  let c := I.center v.1
  let ω' := updAnc9 ω c x
  let ids := I.seen b.1.1
  let D := hitSet9 E G ω' (ids.erase c)
  let μ := maskedLaw9 S ω' b.1
  have hq : 0 < targetFrac9 S E G ω' v b.1 :=
    targetFrac9_pos_of_starValid S E G ω' v hvalid hbStar b
  have hrowSet : hitSet9 E G ω' ids = D.filter (fun z => Hits E G x z) := by
    rw [hitSet9_erase_inter_target (M := M) E G ω b x]
    ext z
    simp [D, ω', ids, c]
  have hrow : rowLaw9 S E G ω' b.1 = restrictOr9 μ (D.filter (fun z => Hits E G x z)) := by
    simp [rowLaw9, μ, ids, hrowSet]
  have hden : rowDeg E G x (restrictOr9 μ D) = targetFrac9 S E G ω' v b.1 := by
    simp [targetFrac9, delLaw9, maskedLaw9, μ, D, ids, ω', c, anc9, updAnc9,
      Function.update]
  have hq' : 0 < rowDeg E G x (restrictOr9 μ D) := by rw [hden]; exact hq
  have hratio := restrictOr9_target_ratio9 E G μ D x hq' y
  rw [hden, ← hrow] at hratio
  have hdel : delLaw9 S E G ω' b.1 c = delLaw9 S E G ω b.1 c := by
    classical
    have hmask : maskedLaw9 S ω' b.1 = maskedLaw9 S ω b.1 := by
      simp [maskedLaw9, msk9, ω', c, updAnc9, Function.update]
    have hhit : hitSet9 E G ω' (ids.erase c) = hitSet9 E G ω (ids.erase c) := by
      ext z
      simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h c' hc'
        rcases Finset.mem_erase.mp hc' with ⟨hne, hmem⟩
        have h' := h c' hc'
        rw [anc9_update_ne ω c c' x hne] at h'
        exact h'
      · intro h c' hc'
        rcases Finset.mem_erase.mp hc' with ⟨hne, hmem⟩
        have h' := h c' hc'
        rw [anc9_update_ne ω c c' x hne]
        exact h'
    change restrictOr9 (maskedLaw9 S ω' b.1)
        (hitSet9 E G ω' ((I.seen b.1.1).erase c)) =
      restrictOr9 (maskedLaw9 S ω b.1)
        (hitSet9 E G ω ((I.seen b.1.1).erase c))
    rw [hmask, hhit]
  have hratio' :
      (rowLaw9 S E G ω' b.1).w y ≤
        (delLaw9 S E G ω' b.1 c).w y / targetFrac9 S E G ω' v b.1 := by
    simpa [delLaw9, maskedLaw9, μ, D, ids] using hratio
  rw [hdel] at hratio'
  simpa [ω', c] using hratio'

private theorem targetFrac9_product_inverse_bound {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (hvalid : starValid9 S E G ω v)
    (hbStar : P.bStar n ≤ 1 / 200) :
    (∏ b : StarOdd9 v, targetFrac9 S E G ω v b.1)⁻¹ ≤
      (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n)) := by
  classical
  have hqpos (b : StarOdd9 v) : 0 < targetFrac9 S E G ω v b.1 :=
    targetFrac9_pos_of_starValid S E G ω v hvalid hbStar b
  have hprod :
      (∏ b : StarOdd9 v, targetFrac9 S E G ω v b.1) =
        Real.exp (starGain9 S E G ω v) := by
    calc
      (∏ b : StarOdd9 v, targetFrac9 S E G ω v b.1) =
          ∏ b : StarOdd9 v, Real.exp (Real.log (targetFrac9 S E G ω v b.1)) := by
            apply Finset.prod_congr rfl
            intro b hb
            exact (Real.exp_log (hqpos b)).symm
      _ = Real.exp (∑ b : StarOdd9 v,
            Real.log (targetFrac9 S E G ω v b.1)) := by rw [Real.exp_sum]
      _ = Real.exp (starGain9 S E G ω v) := by rfl
  have hlog : -starGain9 S E G ω v ≤
      (n : ℝ) * Real.log 2 - gainConst9 * (n : ℝ) * P.aStar n := by
    linarith [hvalid.2]
  have hexp : Real.exp (-starGain9 S E G ω v) ≤
      Real.exp ((n : ℝ) * Real.log 2 - gainConst9 * (n : ℝ) * P.aStar n) :=
    Real.exp_le_exp.mpr hlog
  have hpow : Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    have hlogpow : Real.log ((2 : ℝ) ^ n) = (n : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    rw [← hlogpow, Real.exp_log (by positivity)]
  have hexpEq :
      Real.exp ((n : ℝ) * Real.log 2 - gainConst9 * (n : ℝ) * P.aStar n) =
        (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n)) := by
    rw [Real.exp_sub, hpow, div_eq_mul_inv, ← Real.exp_neg]
  calc
    (∏ b : StarOdd9 v, targetFrac9 S E G ω v b.1)⁻¹ =
        Real.exp (-starGain9 S E G ω v) := by
          rw [hprod, Real.exp_neg]
    _ ≤ Real.exp ((n : ℝ) * Real.log 2 - gainConst9 * (n : ℝ) * P.aStar n) := hexp
    _ = (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n)) := hexpEq

set_option maxHeartbeats 10000000 in
theorem p92_star_lik_bound_core (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
      {κ : ℝ} {G : Colour} {M : TagMix N} (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → StarLikBound9 S I E G := by
  classical
  refine ⟨0, ?_⟩
  intro n hn N E X Y κ G M S I hCore
  rcases hCore with ⟨hN, hprep, hdeep, htag, hmask, htools, hexps, hscales⟩
  rcases hscales with ⟨hn1, hmn, hradius, hss, hbudget, hfirst, hbStar, hlast⟩
  intro ω v x ys
  let c := I.center v.1
  let ω' := updAnc9 ω c x
  by_cases hvalid : starValid9 S E G ω' v
  · have hrowProd :
        (∏ b : StarOdd9 v, (rowLaw9 S E G ω' b.1).w (ys b)) ≤
          ∏ b : StarOdd9 v,
            ((delLaw9 S E G ω b.1 c).w (ys b) /
              targetFrac9 S E G ω' v b.1) := by
      apply Finset.prod_le_prod₀
      · intro b hb
        exact (rowLaw9 S E G ω' b.1).nonneg (ys b)
      · intro b hb
        exact rowLaw9_le_delLaw9_div_target S E G ω v x b (ys b) hvalid hbStar
    have hdelProd :
        0 ≤ ∏ b : StarOdd9 v, (delLaw9 S E G ω b.1 c).w (ys b) :=
      Finset.prod_nonneg fun b hb => (delLaw9 S E G ω b.1 c).nonneg (ys b)
    have hfactor := targetFrac9_product_inverse_bound S E G ω' v hvalid hbStar
    have hweighted :
        (∏ b : StarOdd9 v, (rowLaw9 S E G ω' b.1).w (ys b)) ≤
          (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n)) *
            starRef9 S E G ω v ys := by
      calc
        (∏ b : StarOdd9 v, (rowLaw9 S E G ω' b.1).w (ys b)) ≤
            ∏ b : StarOdd9 v,
              ((delLaw9 S E G ω b.1 c).w (ys b) /
                targetFrac9 S E G ω' v b.1) := hrowProd
        _ = (∏ b : StarOdd9 v, (delLaw9 S E G ω b.1 c).w (ys b)) /
              (∏ b : StarOdd9 v, targetFrac9 S E G ω' v b.1) := by
              rw [Finset.prod_div_distrib]
        _ = (∏ b : StarOdd9 v, (delLaw9 S E G ω b.1 c).w (ys b)) *
              (∏ b : StarOdd9 v, targetFrac9 S E G ω' v b.1)⁻¹ := by
              rw [div_eq_mul_inv]
        _ ≤ (∏ b : StarOdd9 v, (delLaw9 S E G ω b.1 c).w (ys b)) *
              ((2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n))) :=
              mul_le_mul_of_nonneg_left hfactor hdelProd
        _ = (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n)) *
              starRef9 S E G ω v ys := by
              unfold starRef9
              ring
    simpa [starLik9, ω', c, hvalid] using hweighted
  · have hright :
        0 ≤ (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n)) *
          starRef9 S E G ω v ys := by
      apply mul_nonneg
      · positivity
      · unfold starRef9
        exact Finset.prod_nonneg fun b hb =>
          (delLaw9 S E G ω b.1 (I.center v.1)).nonneg (ys b)
    simpa [starLik9, ω', c, hvalid] using hright

private theorem hitSet9_erase_updAnc {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (c : I.ID) (x : Fin N) (ids : Finset I.ID) :
    hitSet9 E G (updAnc9 ω c x) (ids.erase c) = hitSet9 E G ω (ids.erase c) := by
  classical
  ext y
  simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hy c' hc'
    rcases Finset.mem_erase.mp hc' with ⟨hne, hmem⟩
    have hh := hy c' hc'
    rw [anc9_update_ne ω c c' x hne] at hh
    exact hh
  · intro hy c' hc'
    rcases Finset.mem_erase.mp hc' with ⟨hne, hmem⟩
    rw [anc9_update_ne ω c c' x hne]
    exact hy c' hc'

private theorem maskedLaw9_updAnc {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (b : OddSites9 n)
    (ω : Outcome9 I N) (c : I.ID) (x : Fin N) :
    maskedLaw9 S (updAnc9 ω c x) b = maskedLaw9 S ω b := by
  have hne : (Sum.inr b : I.ID ⊕ OddSites9 n) ≠ Sum.inl c := by simp
  unfold maskedLaw9 msk9
  unfold updAnc9
  rw [Function.update_of_ne hne]

private theorem delLaw9_updAnc {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (b : OddSites9 n) (ω : Outcome9 I N) (c : I.ID) (x : Fin N) :
    delLaw9 S E G (updAnc9 ω c x) b c = delLaw9 S E G ω b c := by
  unfold delLaw9
  rw [maskedLaw9_updAnc S b ω c x]
  rw [hitSet9_erase_updAnc E G ω c x (I.seen b.1)]

private theorem starRef9_updAnc {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) (ys : StarOdd9 v → Fin N) :
    starRef9 S E G (updAnc9 ω (I.center v.1) x) v ys =
      starRef9 S E G ω v ys := by
  unfold starRef9
  apply Finset.prod_congr rfl
  intro b hb
  rw [delLaw9_updAnc S E G b.1 ω (I.center v.1) x]

private theorem starLik9_base_update {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x' y : Fin N) (ys : StarOdd9 v → Fin N) :
    starLik9 S E G (updAnc9 ω (I.center v.1) x') v y ys =
      starLik9 S E G ω v y ys := by
  unfold starLik9
  rw [updAnc9_overwrite]

private theorem starMarg9_updAnc {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x' : Fin N)
    (ys : StarOdd9 v → Fin N) :
    starMarg9 S E G (updAnc9 ω (I.center v.1) x') v ys =
      starMarg9 S E G ω v ys := by
  unfold starMarg9
  apply Finset.sum_congr rfl
  intro y hy
  rw [starLik9_base_update]

private theorem starLik9_outcome_updAnc {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) (ys : StarOdd9 v → Fin N) :
  starLik9 S E G ω v x ys =
      starLik9 S E G (updAnc9 ω (I.center v.1) x) v x ys := by
  exact (starLik9_base_update S E G ω v x x ys).symm

private theorem predFail9_updAnc {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) (ys : StarOdd9 v → Fin N) :
    predFail9 S E G (updAnc9 ω (I.center v.1) x) v ys =
      predFail9 S E G ω v ys := by
  unfold predFail9
  rw [starMarg9_updAnc S E G ω v x ys, starRef9_updAnc S E G ω v x ys]

private theorem evenRowAt9_updAnc {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x' x : Fin N)
    (ys : StarOdd9 v → Fin N) :
    evenRowAt9 S E G (updAnc9 ω (I.center v.1) x') v ys x =
      evenRowAt9 S E G ω v ys x := by
  unfold evenRowAt9
  rw [starLik9_base_update, starMarg9_updAnc S E G ω v x' ys]

private theorem starLik9_nonneg_core {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) (ys : StarOdd9 v → Fin N) :
    0 ≤ starLik9 S E G ω v x ys := by
  unfold starLik9
  apply mul_nonneg
  · split_ifs <;> norm_num
  · exact Finset.prod_nonneg fun b hb =>
      (rowLaw9 S E G (updAnc9 ω (I.center v.1) x) b.1).nonneg (ys b)

set_option maxHeartbeats 1000000 in
theorem starCancel9_core {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour) :
    StarCancel9 S I E G := by
  classical
  intro ω v x
  let c := I.center v.1
  let μ := siteFirst9 S v.1
  let F : Fin N → (StarOdd9 v → Fin N) → ℝ :=
    fun x' ys => starLik9 S E G (updAnc9 ω c x') v x' ys
  let m : (StarOdd9 v → Fin N) → ℝ := fun ys => starMarg9 S E G ω v ys
  let H : (StarOdd9 v → Fin N) → ℝ := fun ys =>
    (if predFail9 S E G ω v ys then 0 else 1) *
      ((N : ℝ) * evenRowAt9 S E G ω v ys x)
  have hmargin (x' : Fin N) (ys : StarOdd9 v → Fin N) :
      starMarg9 S E G (updAnc9 ω c x') v ys = m ys := by
    simpa [m, c] using starMarg9_updAnc S E G ω v x' ys
  have hfail (x' : Fin N) (ys : StarOdd9 v → Fin N) :
      predFail9 S E G (updAnc9 ω c x') v ys = predFail9 S E G ω v ys := by
    simpa [c] using predFail9_updAnc S E G ω v x' ys
  have hrow (x' : Fin N) (ys : StarOdd9 v → Fin N) :
      evenRowAt9 S E G (updAnc9 ω c x') v ys x =
        evenRowAt9 S E G ω v ys x := by
    simpa [c] using evenRowAt9_updAnc S E G ω v x' x ys
  have hstar (x' : Fin N) :
      evenStar9 S E G (updAnc9 ω c x') v x =
        ∑ ys, F x' ys * H ys := by
    unfold evenStar9
    apply Finset.sum_congr rfl
    intro ys hys
    have hanc : anc9 (updAnc9 ω c x') c = x' := by
      simp [anc9, updAnc9, Function.update]
    rw [hanc]
    change starLik9 S E G (updAnc9 ω c x') v x' ys *
        ((if predFail9 S E G (updAnc9 ω c x') v ys then 0 else 1) *
          ((N : ℝ) * evenRowAt9 S E G (updAnc9 ω c x') v ys x)) =
      F x' ys * H ys
    rw [hfail x' ys, hrow x' ys]
  have hm_nonneg (ys : StarOdd9 v → Fin N) : 0 ≤ m ys := by
    unfold m starMarg9
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (μ.nonneg y) (starLik9_nonneg_core S E G ω v y ys)
  have hF_nonneg (x' : Fin N) (ys : StarOdd9 v → Fin N) : 0 ≤ F x' ys :=
    starLik9_nonneg_core S E G (updAnc9 ω c x') v x' ys
  have hterm (ys : StarOdd9 v → Fin N) :
      H ys * m ys ≤ (N : ℝ) * μ.w x * F x ys := by
    by_cases hm0 : m ys = 0
    · simp [H, hm0]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (μ.nonneg x)) (hF_nonneg x ys)
    · have hmpos : 0 < m ys := lt_of_le_of_ne (hm_nonneg ys) (Ne.symm hm0)
      by_cases hf : predFail9 S E G ω v ys
      · simp [H, hf]
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (μ.nonneg x)) (hF_nonneg x ys)
      · simp only [H, hf, if_false, one_mul]
        unfold evenRowAt9 F m
        dsimp [c, μ]
        rw [starLik9_outcome_updAnc]
        have hmne : starMarg9 S E G ω v ys ≠ 0 := by simpa [m] using hm0
        field_simp [hmne]
        exact le_rfl
  have hFsum : ∑ ys, F x ys ≤ 1 := by
    unfold F
    unfold starLik9
    simp only [c, updAnc9_overwrite]
    split_ifs with hvalid
    · simp only [one_mul]
      have hpi :=
        (FinProb.pi (fun b : StarOdd9 v =>
          rowLaw9 S E G (updAnc9 ω c x) b.1)).sum_eq_one
      simpa [c, FinProb.pi] using hpi.le
    · norm_num
  have hsumF_eq_m (ys : StarOdd9 v → Fin N) :
      ∑ y, μ.w y * F y ys = m ys := by
    unfold m starMarg9
    apply Finset.sum_congr rfl
    intro y hy
    simp only [μ, F]
    rw [starLik9_base_update]
  calc
    ∑ x', μ.w x' * evenStar9 S E G (updAnc9 ω c x') v x =
        ∑ x', μ.w x' * ∑ ys, F x' ys * H ys := by
          apply Finset.sum_congr rfl
          intro x' hx'
          rw [hstar x']
    _ = ∑ ys, H ys * m ys := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro ys hys
          calc
            ∑ x', μ.w x' * (F x' ys * H ys) =
                ∑ x', (μ.w x' * F x' ys) * H ys := by
                  apply Finset.sum_congr rfl
                  intro x' hx'
                  ring
            _ = (∑ x', μ.w x' * F x' ys) * H ys := by rw [← Finset.sum_mul]
            _ = H ys * m ys := by rw [hsumF_eq_m ys]; ring
    _ ≤ ∑ ys, (N : ℝ) * μ.w x * F x ys :=
          Finset.sum_le_sum fun ys hys => hterm ys
    _ = (N : ℝ) * μ.w x * ∑ ys, F x ys := by rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * μ.w x := by
          simpa using mul_le_mul_of_nonneg_left hFsum
            (mul_nonneg (Nat.cast_nonneg N) (μ.nonneg x))

theorem starLik9_nonneg {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) (ys : StarOdd9 v → Fin N) :
    0 ≤ starLik9 S E G ω v x ys := by
  unfold starLik9
  apply mul_nonneg
  · split_ifs <;> norm_num
  · exact Finset.prod_nonneg fun b hb =>
      (rowLaw9 S E G (updAnc9 ω (I.center v.1) x) b.1).nonneg (ys b)

theorem evenRowAt9_nonneg {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (ys : StarOdd9 v → Fin N) (x : Fin N) :
    0 ≤ evenRowAt9 S E G ω v ys x := by
  have hmargin : 0 ≤ starMarg9 S E G ω v ys := by
    unfold starMarg9
    apply Finset.sum_nonneg
    intro x' hx'
    exact mul_nonneg ((siteFirst9 S v.1).nonneg x') (starLik9_nonneg S E G ω v x' ys)
  unfold evenRowAt9
  exact div_nonneg
    (mul_nonneg (starLik9_nonneg S E G ω v x ys) ((siteFirst9 S v.1).nonneg x))
    hmargin

theorem evenRowLaw9_core {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (hbStar : P.bStar n ≤ 1 / 200) : EvenRowLaw9 S I E G := by
  classical
  intro ω f v hfail
  let ys : StarOdd9 v → Fin N := nbrLabels9 (v := v) f
  have hMne : starMarg9 S E G ω v ys ≠ 0 := by
    intro hz
    exact hfail (Or.inl hz)
  have hMnonneg : 0 ≤ starMarg9 S E G ω v ys := by
    unfold starMarg9
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg ((siteFirst9 S v.1).nonneg x)
      (starLik9_nonneg S E G ω v x ys)
  constructor
  · intro x
    exact evenRowAt9_nonneg S E G ω v ys x
  constructor
  · change (∑ x, evenRowAt9 S E G ω v ys x) = 1
    unfold evenRowAt9
    rw [← Finset.sum_div]
    have hnum :
        (∑ x, starLik9 S E G ω v x ys * (siteFirst9 S v.1).w x) =
          starMarg9 S E G ω v ys := by
      unfold starMarg9
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hnum]
    exact div_self hMne
  · intro x hx b hb
    let b' : StarOdd9 v := ⟨b, hb⟩
    have hrowAtNe : evenRowAt9 S E G ω v ys x ≠ 0 := by
      simpa [evenRow9, ys] using hx
    have hnumNe : starLik9 S E G ω v x ys * (siteFirst9 S v.1).w x ≠ 0 := by
      intro hzero
      apply hrowAtNe
      simp [evenRowAt9, hzero]
    have hlik : starLik9 S E G ω v x ys ≠ 0 := by
      intro hzero
      apply hnumNe
      simp [hzero]
    have hvalid : starValid9 S E G (updAnc9 ω (I.center v.1) x) v := by
      by_contra hbad
      apply hlik
      simp [starLik9, hbad]
    have hprod :
        (∏ b : StarOdd9 v,
          (rowLaw9 S E G (updAnc9 ω (I.center v.1) x) b.1).w (ys b)) ≠ 0 := by
      intro hzero
      apply hlik
      simp [starLik9, hvalid, hzero]
    have hrowNe (q : StarOdd9 v) :
        (rowLaw9 S E G (updAnc9 ω (I.center v.1) x) q.1).w (ys q) ≠ 0 := by
      intro hzero
      apply hprod
      exact Finset.prod_eq_zero (Finset.mem_univ q) hzero
    have hhit := rowLaw9_hit_of_nonzero9 S E G ω v x b' (ys b') hvalid hbStar
      (hrowNe b')
    simpa [ys, nbrLabels9, b'] using hhit

set_option maxHeartbeats 1000000 in
theorem p92_even_row_cap_core (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} {κ : ℝ} {G : Colour} {M : TagMix N}
      (S : Setup9 P n N M) (I : IDMap9 P n),
      CoreInput9 P κ E X Y G M S I → StarLikBound9 S I E G → EvenRowCap9 S I E G := by
  classical
  obtain ⟨nlog, hlog⟩ := hplus_log_le_pow9 P hP
  refine ⟨nlog, ?_⟩
  intro n hn N E X Y κ G M S I hCore hSLB
  rcases hCore with ⟨hN, hprep, hdeep, htagWeight, hmask, htools, hexps, hscales⟩
  rcases hprep with ⟨hbalanced, hprepLaw⟩
  rcases hscales with ⟨hn1, hmn, hradius, hss, hbudget, hfirst, hbStar, hlast⟩
  let width : ℝ := (n : ℝ) ^ (P.xS : ℝ) +
    (P.hPlus : ℝ) * Real.log (n : ℝ) + 1
  have hlogWidth := hlog n hn
  have hlogRadius : 0 ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hradTerm :
      0 ≤ ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) :=
    mul_nonneg (by positivity) hlogRadius
  have hwidthBudget : width ≤ gainConst9 * (n : ℝ) * P.aStar n / 4 := by
    have hwidthStep : width ≤
        (n : ℝ) ^ (P.xS : ℝ) + 4 * (n : ℝ) ^ P.u := by
      dsimp [width]
      linarith [hlogWidth]
    have hscaleStep : (n : ℝ) ^ (P.xS : ℝ) + 4 * (n : ℝ) ^ P.u ≤
        gainConst9 * (n : ℝ) * P.aStar n / 100 := by
      nlinarith [hlast, hradTerm]
    have hnRealPos : 0 < (n : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hn1)
    have haStarPos : 0 < P.aStar n := by
      dsimp [Params9.aStar]
      exact div_pos (Real.rpow_pos_of_pos hnRealPos _) (by norm_num)
    have hgain : 0 ≤ gainConst9 * (n : ℝ) * P.aStar n :=
      mul_nonneg (mul_nonneg (by norm_num [gainConst9]) (by positivity)) haStarPos.le
    calc
      width ≤ (n : ℝ) ^ (P.xS : ℝ) + 4 * (n : ℝ) ^ P.u := hwidthStep
      _ ≤ gainConst9 * (n : ℝ) * P.aStar n / 100 := hscaleStep
      _ ≤ gainConst9 * (n : ℝ) * P.aStar n / 4 := by nlinarith
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hAtom (v : EvenSites9 n) (x : Fin N) :
      (N : ℝ) * (siteFirst9 S v.1).w x ≤
        Real.exp ((n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) := by
    have htag := htagWeight (specialWord9 (P.m n) v.1)
    have hw := (hprepLaw (S.tag (specialWord9 (P.m n) v.1)) htag).2.2.1 x
    have hw' := (le_div_iff₀ hNreal).1 hw
    dsimp [siteFirst9]
    calc
      (N : ℝ) * (M.μ (S.tag (specialWord9 (P.m n) v.1))).w x =
          (M.μ (S.tag (specialWord9 (P.m n) v.1))).w x * (N : ℝ) := by ring
      _ ≤ Real.exp ((n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) := hw'
  intro ω v ys hfail x
  let μ := (siteFirst9 S v.1).w x
  let F := starLik9 S E G ω v x ys
  let m := starMarg9 S E G ω v ys
  let pref := starRef9 S E G ω v ys
  let ε := Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 4))
  let L := (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n))
  have hmnonneg : 0 ≤ m := by
    dsimp [m, starMarg9]
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg ((siteFirst9 S v.1).nonneg z) (starLik9_nonneg S E G ω v z ys)
  have hmne : m ≠ 0 := by
    intro hz
    exact hfail (Or.inl (by simpa [m] using hz))
  have hmpos : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hmne)
  have hprefNonneg : 0 ≤ pref := by
    dsimp [pref, starRef9]
    exact Finset.prod_nonneg fun b hb => (delLaw9 S E G ω b.1 (I.center v.1)).nonneg (ys b)
  have hfail' : ¬ (m = 0 ∨ m < ε * pref) := by
    simpa [predFail9, m, ε, pref] using hfail
  have hMargin : ε * pref ≤ m := by
    by_contra h
    exact hfail' (Or.inr (lt_of_not_ge h))
  have heps : 0 < ε := by positivity
  have hFnonneg : 0 ≤ F := by simpa [F] using starLik9_nonneg S E G ω v x ys
  have hFbound : F ≤ L * pref := by
    simpa [F, L, pref] using hSLB ω v x ys
  by_cases hpref : pref = 0
  · have hFle : F ≤ 0 := by simpa [hpref] using hFbound
    have hFzero : F = 0 := le_antisymm hFle hFnonneg
    have hrowzero : evenRowAt9 S E G ω v ys x = 0 := by
      simp [evenRowAt9, F, hFzero]
    simpa [hrowzero] using (show
      0 ≤ (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 2)) by positivity)
  · have hprefPos : 0 < pref := lt_of_le_of_ne hprefNonneg (Ne.symm hpref)
    have hDenPos : 0 < ε * pref := mul_pos heps hprefPos
    have hFμ : F * μ ≤ (L * pref) * μ :=
      mul_le_mul_of_nonneg_right hFbound ((siteFirst9 S v.1).nonneg x)
    have hNum : (N : ℝ) * (F * μ) ≤ (N : ℝ) * ((L * pref) * μ) :=
      mul_le_mul_of_nonneg_left hFμ (by positivity)
    have hLnonneg : 0 ≤ L := by positivity
    have hμnonneg : 0 ≤ μ := (siteFirst9 S v.1).nonneg x
    have hNumNonneg : 0 ≤ (N : ℝ) * ((L * pref) * μ) :=
      mul_nonneg (by positivity)
        (mul_nonneg (mul_nonneg hLnonneg hprefNonneg) hμnonneg)
    have hrowBound :
        (N : ℝ) * evenRowAt9 S E G ω v ys x ≤ (N : ℝ) * μ * (L / ε) := by
      change (N : ℝ) * (F * μ / m) ≤ (N : ℝ) * μ * (L / ε)
      let A := (N : ℝ) * (F * μ)
      let A' := (N : ℝ) * ((L * pref) * μ)
      calc
        (N : ℝ) * (F * μ / m) = A / m := by dsimp [A]; ring
        _ ≤ A' / m := div_le_div_of_nonneg_right (by simpa [A, A'] using hNum) hmpos.le
        _ = A' * (1 / m) := by simp [div_eq_mul_inv]
        _ ≤ A' * (1 / (ε * pref)) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hDenPos hMargin) hNumNonneg
        _ = (N : ℝ) * μ * (L / ε) := by
          dsimp [A']
          field_simp [ne_of_gt heps, ne_of_gt hprefPos]
          <;> ring_nf
    let t := gainConst9 * (n : ℝ) * P.aStar n
    have hLdiv : L / ε = (2 : ℝ) ^ n * Real.exp (-(t * 3 / 4)) := by
      dsimp [L, ε, t]
      calc
        _ = (2 : ℝ) ^ n * (Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n)) /
              Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 4))) := by ring
        _ = (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n) -
              (-(gainConst9 * (n : ℝ) * P.aStar n / 4))) := by rw [← Real.exp_sub]
        _ = (2 : ℝ) ^ n * Real.exp (-(t * 3 / 4)) := by congr 1; congr 1; ring
    have hAtomExp : (N : ℝ) * μ ≤ Real.exp (t / 4) := by
      have h := hAtom v x
      exact le_trans h (Real.exp_le_exp.mpr (by simpa [t, width] using hwidthBudget))
    have hscaleFinal : (N : ℝ) * μ * (L / ε) ≤
        (2 : ℝ) ^ n * Real.exp (-t / 2) := by
      calc
        (N : ℝ) * μ * (L / ε) ≤ Real.exp (t / 4) * (L / ε) :=
          mul_le_mul_of_nonneg_right hAtomExp (by positivity)
        _ = Real.exp (t / 4) * ((2 : ℝ) ^ n * Real.exp (-(t * 3 / 4))) := by rw [hLdiv]
        _ = (2 : ℝ) ^ n * Real.exp (-t / 2) := by
          calc
            _ = (2 : ℝ) ^ n * (Real.exp (t / 4) * Real.exp (-(t * 3 / 4))) := by ring
            _ = (2 : ℝ) ^ n * Real.exp (t / 4 + (-(t * 3 / 4))) := by rw [← Real.exp_add]
            _ = (2 : ℝ) ^ n * Real.exp (-t / 2) := by congr 1; congr 1; ring
    calc
      (N : ℝ) * evenRowAt9 S E G ω v ys x ≤ (N : ℝ) * μ * (L / ε) := hrowBound
      _ ≤ (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n) / 2) := by
        simpa [t] using hscaleFinal
      _ = (2 : ℝ) ^ n * Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 2)) :=
        congrArg (fun z : ℝ => (2 : ℝ) ^ n * Real.exp z)
          (show -(gainConst9 * (n : ℝ) * P.aStar n) / 2 =
            -(gainConst9 * (n : ℝ) * P.aStar n / 2) by ring)

private def flipStar9 {n : ℕ} (v : EvenSites9 n) (i : Fin n) : StarOdd9 v :=
  ⟨⟨cubeFlip v.1 i, by
      intro he
      have hnot : ¬ IsEvenRole v.1 := (cubeFlip_parity v.1 i).mp he
      exact hnot v.2⟩,
    cubeFlip_adj v.1 i⟩

private theorem exists_flipStar9 {n : ℕ} {v : EvenSites9 n} (b : StarOdd9 v) :
    ∃ i : Fin n, cubeFlip v.1 i = b.1.1 := by
  classical
  let D : Finset (Fin n) := Finset.univ.filter (fun i => v.1 i ≠ b.1.1 i)
  have hcard : D.card = 1 := by
    have hb := b.2
    change _root_.hammingDist v.1 b.1.1 = 1 at hb
    simpa [D, _root_.hammingDist] using hb
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  refine ⟨i, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j
    have hmem : i ∈ D := by simp [hi]
    have hneq : v.1 i ≠ b.1.1 i := (Finset.mem_filter.mp hmem).2
    cases hv : v.1 i <;> cases hb : b.1.1 i <;> simp_all [cubeFlip]
  · have hnot : j ∉ D := by simp [hi, hji]
    have heq : v.1 j = b.1.1 j := by
      by_contra hne
      have hj : j ∈ D := by simp [D, hne]
      exact hnot hj
    simp [cubeFlip, hji, heq]

private noncomputable def starCoord9 {n : ℕ} {v : EvenSites9 n} (b : StarOdd9 v) : Fin n :=
  Classical.choose (exists_flipStar9 b)

private theorem starCoord9_spec {n : ℕ} {v : EvenSites9 n} (b : StarOdd9 v) :
    cubeFlip v.1 (starCoord9 b) = b.1.1 :=
  Classical.choose_spec (exists_flipStar9 b)

private theorem starCoord9_injective {n : ℕ} {v : EvenSites9 n} :
    Function.Injective (starCoord9 (v := v)) := by
  intro b b' h
  apply Subtype.ext
  apply Subtype.ext
  calc
    b.1.1 = cubeFlip v.1 (starCoord9 b) := (starCoord9_spec b).symm
    _ = cubeFlip v.1 (starCoord9 b') := by rw [h]
    _ = b'.1.1 := starCoord9_spec b'

private theorem starOdd_card_le9 {n : ℕ} (v : EvenSites9 n) :
    Fintype.card (StarOdd9 v) ≤ n := by
  simpa using Fintype.card_le_of_injective (starCoord9 (v := v)) starCoord9_injective

private theorem special_hamming_le_full9 {m n : ℕ} (u v : CubeVertex n) :
    _root_.hammingDist (specialWord9 m u) (specialWord9 m v) ≤ _root_.hammingDist u v := by
  classical
  let A : Finset (Fin m) := Finset.univ.filter
    (fun i => specialWord9 m u i ≠ specialWord9 m v i)
  let B : Finset (Fin n) := Finset.univ.filter (fun i => u i ≠ v i)
  have hsmall (i : Fin m) (hi : i ∈ A) : (i : ℕ) < n := by
    by_contra hn
    have hu : specialWord9 m u i = false := by simp [specialWord9, not_lt.mp hn]
    have hv : specialWord9 m v i = false := by simp [specialWord9, not_lt.mp hn]
    exact (Finset.mem_filter.mp hi).2 (hu.trans hv.symm)
  let e : A → Fin n := fun i => ⟨i.1.val, hsmall i.1 i.2⟩
  have hinj : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    apply Fin.ext
    simpa [e] using congrArg Fin.val h
  have hsubset : A.attach.image e ⊆ B := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hu : specialWord9 m u i.1 = u (e i) := by
      simp [specialWord9, e, hsmall i.1 i.2]
    have hv : specialWord9 m v i.1 = v (e i) := by
      simp [specialWord9, e, hsmall i.1 i.2]
    have hdiff := (Finset.mem_filter.mp i.2).2
    rw [← hu, ← hv]
    exact hdiff
  have hA : _root_.hammingDist (specialWord9 m u) (specialWord9 m v) = A.card := by
    simp [A, _root_.hammingDist]
  have hB : _root_.hammingDist u v = B.card := by
    simp [B, _root_.hammingDist]
  calc
    _ = A.card := hA
    _ = A.attach.card := by simp
    _ = (A.attach.image e).card := (Finset.card_image_of_injective A.attach hinj).symm
    _ ≤ B.card := Finset.card_le_card hsubset
    _ = _ := hB.symm

private theorem residual_hamming_le_full9 {m n : ℕ} (u v : CubeVertex n) :
    _root_.hammingDist (residualWord9 m u) (residualWord9 m v) ≤ _root_.hammingDist u v := by
  classical
  by_cases hm : m ≤ n
  · let A : Finset (Fin (n - m)) := Finset.univ.filter
      (fun i => residualWord9 m u i ≠ residualWord9 m v i)
    let B : Finset (Fin n) := Finset.univ.filter (fun i => u i ≠ v i)
    let e : A → Fin n := fun i => ⟨m + i.1.val, by omega⟩
    have hinj : Function.Injective e := by
      intro i j h
      apply Subtype.ext
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [e] at hv
      omega
    have hsubset : A.attach.image e ⊆ B := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hu : residualWord9 m u i.1 = u (e i) := by
        simp [residualWord9, e]
      have hv : residualWord9 m v i.1 = v (e i) := by
        simp [residualWord9, e]
      have hdiff := (Finset.mem_filter.mp i.2).2
      rw [← hu, ← hv]
      exact hdiff
    have hA : _root_.hammingDist (residualWord9 m u) (residualWord9 m v) = A.card := by
      simp [A, _root_.hammingDist]
    have hB : _root_.hammingDist u v = B.card := by
      simp [B, _root_.hammingDist]
    calc
      _ = A.card := hA
      _ = A.attach.card := by simp
      _ = (A.attach.image e).card := (Finset.card_image_of_injective A.attach hinj).symm
      _ ≤ B.card := Finset.card_le_card hsubset
      _ = _ := hB.symm
  · have hdim : n - m = 0 := by omega
    simp [_root_.hammingDist, hdim]

private theorem sameCenter_siteNear9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    (u v : CubeVertex n) (hc : I.center u = I.center v) : siteNear9 P n u v := by
  constructor
  · have hs : specialWord9 (P.m n) u = specialWord9 (P.m n) v := by
      calc
        specialWord9 (P.m n) u = (I.center u).slice := (I.center_slice u).symm
        _ = (I.center v).slice := congrArg CenterID9.slice hc
        _ = specialWord9 (P.m n) v := I.center_slice v
    simp [hs]
  · have hloc : (I.center u).location = (I.center v).location := congrArg CenterID9.location hc
    have hu : _root_.hammingDist (residualWord9 (P.m n) u) (I.center u).location ≤ P.radius n := by
      rw [_root_.hammingDist_comm]
      exact I.center_near u
    have hv : _root_.hammingDist (I.center u).location (residualWord9 (P.m n) v) ≤ P.radius n := by
      simpa [hloc.symm] using I.center_near v
    calc
      _ ≤ _root_.hammingDist (residualWord9 (P.m n) u) (I.center u).location +
          _root_.hammingDist (I.center u).location (residualWord9 (P.m n) v) :=
            _root_.hammingDist_triangle _ _ _
      _ ≤ P.radius n + P.radius n := Nat.add_le_add hu hv
      _ ≤ 4 * P.radius n + 8 := by omega

private theorem targetCenters_injective9 {P : Params9} {n k : ℕ} {I : IDMap9 P n}
    (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1) :
    Function.Injective (fun i : Fin k => I.center (a i).1) := by
  intro i j hij
  by_contra hne
  have hnear := sameCenter_siteNear9 (P := P) (a i).1 (a j).1 hij
  by_cases hji : j < i
  · exact hsep i j hji hnear
  · have hij' : i < j := by omega
    exact hsep j i hij' (siteNear9_symm (P := P) (n := n) (a i).1 (a j).1 hnear)

private theorem siteNear9_of_common_neighbor {P : Params9} {n : ℕ}
    (u v : EvenSites9 n) (b : OddSites9 n)
    (hu : (cube n).Adj u.1 b.1) (hv : (cube n).Adj v.1 b.1) :
    siteNear9 P n u.1 v.1 := by
  have hu' : _root_.hammingDist u.1 b.1 = 1 := by change _; exact hu
  have hv' : _root_.hammingDist v.1 b.1 = 1 := by change _; exact hv
  have hb' : _root_.hammingDist b.1 v.1 = 1 := by
    rw [_root_.hammingDist_comm]
    exact hv'
  have huv : _root_.hammingDist u.1 v.1 ≤ 2 := by
    calc
      _ ≤ _root_.hammingDist u.1 b.1 + _root_.hammingDist b.1 v.1 :=
        _root_.hammingDist_triangle _ _ _
      _ = 2 := by rw [hu', hb']
  constructor
  · exact (special_hamming_le_full9 (m := P.m n) u.1 v.1).trans (by omega)
  · have h := (residual_hamming_le_full9 (m := P.m n) u.1 v.1).trans (by omega)
    exact h.trans (by omega)

private noncomputable def starNbrSet9 {n : ℕ} (v : EvenSites9 n) : Finset (OddSites9 n) :=
  Finset.univ.filter (fun b => (cube n).Adj v.1 b.1)

private def starNbrEquiv9 {n : ℕ} (v : EvenSites9 n) :
    StarOdd9 v ≃ {b : OddSites9 n // b ∈ starNbrSet9 v} where
  toFun b := ⟨b.1, by simp [starNbrSet9, b.2]⟩
  invFun b := ⟨b.1, by simpa [starNbrSet9] using (Finset.mem_filter.mp b.2).2⟩
  left_inv b := by apply Subtype.ext; rfl
  right_inv b := by apply Subtype.ext; rfl

private theorem starNbrSet9_card_le {n : ℕ} (v : EvenSites9 n) :
    (starNbrSet9 v).card ≤ n := by
  calc
    (starNbrSet9 v).card = Fintype.card {b : OddSites9 n // b ∈ starNbrSet9 v} :=
      (Fintype.card_coe (starNbrSet9 v)).symm
    _ = Fintype.card (StarOdd9 v) := Fintype.card_congr (starNbrEquiv9 v).symm
    _ ≤ n := starOdd_card_le9 v

private theorem starNbrUnion9_card_le {k n : ℕ} (a : Fin k → EvenSites9 n) :
    (Finset.univ.biUnion (fun i : Fin k => starNbrSet9 (a i))).card ≤ k * n := by
  classical
  calc
    (Finset.univ.biUnion (fun i : Fin k => starNbrSet9 (a i))).card ≤
        ∑ i : Fin k, (starNbrSet9 (a i)).card := by
          simpa using (Finset.card_biUnion_le (s := Finset.univ)
            (t := fun i : Fin k => starNbrSet9 (a i)))
    _ ≤ ∑ i : Fin k, n := Finset.sum_le_sum fun i hi => starNbrSet9_card_le (a i)
    _ = k * n := by simp

private theorem starNbrUnion9_pairwise_disjoint {P : Params9} {n k : ℕ}
    (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1) :
    Pairwise fun i j : Fin k => Disjoint (starNbrSet9 (a i)) (starNbrSet9 (a j)) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro b hbi hbj
  have hnear := siteNear9_of_common_neighbor (P := P) (a i) (a j) b
    (Finset.mem_filter.mp hbi).2 (Finset.mem_filter.mp hbj).2
  by_cases hji : j < i
  · exact hsep i j hji hnear
  · have hij' : i < j := by omega
    exact hsep j i hij' (siteNear9_symm (P := P) (n := n) (a i).1 (a j).1 hnear)

private theorem sigmaStarSite_injective9 {P : Params9} {n k : ℕ}
    (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1) :
    Function.Injective (fun p : Σ i : Fin k, StarOdd9 (a i) => p.2.1) := by
  classical
  intro p q hpq
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, c⟩
  change b.1 = c.1 at hpq
  by_cases hij : i = j
  · subst j
    have hbc : b = c := Subtype.ext hpq
    subst c
    rfl
  · have hadj : (cube n).Adj (a j).1 b.1.1 := by simpa [hpq] using c.2
    have hnear := siteNear9_of_common_neighbor (P := P) (a i) (a j) b.1 b.2 hadj
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (hsep j i hlt (siteNear9_symm (P := P) (n := n) (a i).1 (a j).1 hnear)).elim
    · exact (hij heq).elim
    · exact (hsep i j hgt hnear).elim

private abbrev StarIndex9 {n k : ℕ} (a : Fin k → EvenSites9 n) :=
  Σ i : Fin k, StarOdd9 (a i)

private def starSite9 {n k : ℕ} (a : Fin k → EvenSites9 n) (p : StarIndex9 a) :
    OddSites9 n := p.2.1

private noncomputable def starNbrUnionSet9 {n k : ℕ} (a : Fin k → EvenSites9 n) :
    Finset (OddSites9 n) := Finset.univ.biUnion (fun i : Fin k => starNbrSet9 (a i))

private noncomputable def starDataEquiv9 {P : Params9} {n k : ℕ}
    (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1) :
    StarIndex9 a ≃ {b : OddSites9 n // b ∈ starNbrUnionSet9 a} := by
  classical
  let f : StarIndex9 a → {b : OddSites9 n // b ∈ starNbrUnionSet9 a} := fun p =>
    ⟨starSite9 a p, Finset.mem_biUnion.mpr
      ⟨p.1, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2.2⟩⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    apply sigmaStarSite_injective9 a hsep
    exact congrArg Subtype.val hpq
  · intro b
    rcases Finset.mem_biUnion.mp b.2 with ⟨i, hi, hmem⟩
    have hadj := (Finset.mem_filter.mp hmem).2
    refine ⟨⟨i, ⟨b.1, hadj⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

private theorem starDataEquiv9_val {P : Params9} {n k : ℕ}
    (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1)
    (p : StarIndex9 a) : (starDataEquiv9 a hsep p).1 = starSite9 a p := rfl

private theorem starNbrUnion9_card_cube {n k : ℕ} (a : Fin k → EvenSites9 n)
    (hk : k ≤ n) (hn : 1 ≤ n) :
    (starNbrUnionSet9 a).card ≤ n ^ 3 := by
  have hcard : (starNbrUnionSet9 a).card ≤ k * n := by
    simpa [starNbrUnionSet9] using starNbrUnion9_card_le a
  calc
    (starNbrUnionSet9 a).card ≤ k * n := hcard
    _ ≤ n * n := Nat.mul_le_mul_right n hk
    _ ≤ n * n * n := by
      calc
        n * n = (n * n) * 1 := by simp
        _ ≤ (n * n) * n := Nat.mul_le_mul_left (n * n) hn
    _ = n ^ 3 := by simp [pow_succ, Nat.mul_assoc]

private theorem map_expect_le_of_weight_bound9 {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    [DecidableEq Γ] (P : FinProb Ω) (proj : Ω → Γ) (W g : Γ → ℝ)
    (hW : ∀ γ, (FinProb.map P proj).w γ ≤ W γ) (hg : ∀ γ, 0 ≤ g γ) :
    P.expect (fun ω => g (proj ω)) ≤ ∑ γ, W γ * g γ := by
  classical
  calc
    P.expect (fun ω => g (proj ω)) = (FinProb.map P proj).expect g :=
      (FinProb.map_expect P proj g).symm
    _ = ∑ γ, (FinProb.map P proj).w γ * g γ := rfl
    _ ≤ ∑ γ, W γ * g γ :=
      Finset.sum_le_sum fun γ hγ => mul_le_mul_of_nonneg_right (hW γ) (hg γ)

private theorem map_weight_eq_pr9 {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [DecidableEq Γ]
    (P : FinProb Ω) (proj : Ω → Γ) (γ : Γ) :
    (FinProb.map P proj).w γ = P.pr (fun ω => proj ω = γ) := by
  classical
  simp [FinProb.map, FinProb.pr, eq_comm]

private theorem updAnc9_self9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (ω : Outcome9 I N) (c : I.ID) :
    updAnc9 ω c (anc9 ω c) = ω := by
  funext z
  by_cases hz : z = Sum.inl c
  · subst z
    simp [updAnc9, anc9]
  · change Function.update ω (Sum.inl c) (anc9 ω c) z = ω z
    exact Function.update_of_ne (v := anc9 ω c) (f := ω) hz

private theorem goodPre_starValid9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {ω : Outcome9 I N} (hg : GoodPre9 S E G ω) (v : EvenSites9 n) :
    starValid9 S E G ω v := by
  have hnot := hg.2.1 v
  have hh : starValid9 S E G ω v ∧
      alarm9 S E G ω v ≤ Real.exp (-(gainConst9 * n * P.aStar n / 8)) := by
    simpa [StarBad9] using hnot
  exact hh.1

private theorem sum_prod_stars9 {n N k : ℕ} (a : Fin k → EvenSites9 n)
    (F : ∀ i : Fin k, (StarOdd9 (a i) → Fin N) → ℝ) :
    (∑ y : ∀ i : Fin k, StarOdd9 (a i) → Fin N, ∏ i, F i (y i)) =
      ∏ i, ∑ y : StarOdd9 (a i) → Fin N, F i y := by
  classical
  rw [← Fintype.prod_sum]

private theorem starLik9_actual_eq_rows9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (ys : StarOdd9 v → Fin N)
    (hvalid : starValid9 S E G ω v) :
    starLik9 S E G ω v (anc9 ω (I.center v.1)) ys =
      ∏ b : StarOdd9 v, (rowLaw9 S E G ω b.1).w (ys b) := by
  have hu := updAnc9_self9 ω (I.center v.1)
  simp [starLik9, hu, hvalid]

set_option maxHeartbeats 10000000 in
theorem p92_clock_factor_core {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (J : Outcome9 I N → FinProb (OddSites9 n → Fin N))
    (hJ : ∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) :
    ClockFactor9 S I E G J := by
  classical
  intro ω hg x k hk a hsep
  by_cases hk0 : k = 0
  · subst k
    calc
      (∑ f, (J ω).w f * ∏ i : Fin 0, (N : ℝ) * evenRow9 S E G ω f (a i) x) = 1 := by
        simp [(J ω).sum_eq_one]
      _ ≤ 2 * ∏ i : Fin 0, evenStar9 S E G ω (a i) x := by norm_num
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      have hkz : k = 0 := Nat.eq_zero_of_le_zero hk
      exact hk0 hkz
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    let T : Finset (OddSites9 n) := starNbrUnionSet9 a
    let Γ := {b : OddSites9 n // b ∈ T}
    let e : StarIndex9 a ≃ Γ := starDataEquiv9 a hsep
    have hTcardNat : T.card ≤ n ^ 3 := by
      exact starNbrUnion9_card_cube a hk hn
    have hTcard : (T.card : ℝ) ≤ (n : ℝ) ^ 3 := by
      exact_mod_cast hTcardNat
    let proj : (OddSites9 n → Fin N) → Γ → Fin N := fun f b => f b.1
    let ys : (Γ → Fin N) → (i : Fin k) → StarOdd9 (a i) → Fin N :=
      fun γ i b => γ (e ⟨i, b⟩)
    let W : (Γ → Fin N) → ℝ := fun γ =>
      2 * ∏ b : Γ, (rowLaw9 S E G ω b.1).w (γ b)
    let g : (Γ → Fin N) → ℝ := fun γ =>
      ∏ i : Fin k,
        (if predFail9 S E G ω (a i) (ys γ i) then 0 else 1) *
          ((N : ℝ) * evenRowAt9 S E G ω (a i) (ys γ i) x)
    have hgNonneg (γ : Γ → Fin N) : 0 ≤ g γ := by
      apply Finset.prod_nonneg
      intro i hi
      by_cases hfail : predFail9 S E G ω (a i) (ys γ i)
      · simp [g, hfail]
      · simp only [g, if_neg hfail]
        exact mul_nonneg (by positivity)
          (mul_nonneg (by positivity) (evenRowAt9_nonneg S E G ω (a i) (ys γ i) x))
    have hclock := hJ ω hg
    have hweight (γ : Γ → Fin N) : (FinProb.map (J ω) proj).w γ ≤ W γ := by
      rw [map_weight_eq_pr9]
      let base : Fin N := anc9 ω (I.center (a ⟨0, hkpos⟩).1)
      let o : OddSites9 n → Fin N := fun b =>
        if hb : b ∈ T then γ ⟨b, hb⟩ else base
      have hrows :
          (∏ b : Γ, (rowLaw9 S E G ω b.1).w (γ b)) =
            ∏ b ∈ T, (rowLaw9 S E G ω b).w (o b) := by
        simpa [Γ, o, Finset.univ_eq_attach] using
          (Finset.prod_attach T (fun b : OddSites9 n => (rowLaw9 S E G ω b).w (o b)))
      have hfiber (f : OddSites9 n → Fin N) :
          (proj f = γ) ↔ ∀ b ∈ T, f b = o b := by
        constructor
        · intro hp b hb
          have hval := congrFun hp ⟨b, hb⟩
          simpa [proj, o, hb] using hval
        · intro hp
          funext b
          change f b.1 = γ b
          calc
            f b.1 = o b.1 := hp b.1 b.2
            _ = γ b := by simp [o, b.2]
      have hfiberFun : (fun f : OddSites9 n → Fin N => proj f = γ) =
          (fun f => ∀ b ∈ T, f b = o b) := by
        funext f
        exact propext (hfiber f)
      rw [hfiberFun]
      calc
        (J ω).pr (fun f => ∀ b ∈ T, f b = o b) ≤
            2 * ∏ b ∈ T, (rowLaw9 S E G ω b).w (o b) := hclock.2 T o hTcard
        _ = W γ := by rw [← hrows]
    have hleft :
        (∑ f, (J ω).w f * ∏ i : Fin k,
          (N : ℝ) * evenRow9 S E G ω f (a i) x) =
        (J ω).expect (fun f => g (proj f)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hw : (J ω).w f = 0
      · simp [g, hw]
      ·
        have hfail (i : Fin k) :
            ¬ predFail9 S E G ω (a i) (nbrLabels9 (v := a i) f) :=
          (hclock.1 f hw).2 (a i)
        have hys (i : Fin k) : ys (proj f) i = nbrLabels9 (v := a i) f := by
          funext b
          change f (starDataEquiv9 a hsep ⟨i, b⟩).1 = f b.1
          rw [starDataEquiv9_val a hsep ⟨i, b⟩]
          simp [starSite9]
        simp [g, hys, evenRow9, hfail]
    let Efun : (Γ → Fin N) ≃ (∀ i : Fin k, StarOdd9 (a i) → Fin N) := {
      toFun := fun γ i b => γ (e ⟨i, b⟩)
      invFun := fun z b => z (e.symm b).1 (e.symm b).2
      left_inv := by
        intro γ
        funext b
        change γ (e (e.symm b)) = γ b
        rw [Equiv.apply_symm_apply e b]
      right_inv := by
        intro z
        funext i b
        change z (e.symm (e ⟨i, b⟩)).1 (e.symm (e ⟨i, b⟩)).2 = z i b
        rw [Equiv.symm_apply_apply e ⟨i, b⟩]
    }
    let localF : ∀ i : Fin k, (StarOdd9 (a i) → Fin N) → ℝ := fun i z =>
      (∏ b : StarOdd9 (a i), (rowLaw9 S E G ω b.1).w (z b)) *
        (if predFail9 S E G ω (a i) z then 0 else 1) *
          ((N : ℝ) * evenRowAt9 S E G ω (a i) z x)
    have hlocal (i : Fin k) :
        (∑ z : StarOdd9 (a i) → Fin N, localF i z) = evenStar9 S E G ω (a i) x := by
      have hstar (z : StarOdd9 (a i) → Fin N) :=
        starLik9_actual_eq_rows9 S E G ω (a i) z
          (goodPre_starValid9 S E G hg (a i))
      unfold localF evenStar9
      simp_rw [← hstar]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    let H : (Γ → Fin N) → ℝ := fun γ =>
      (∏ b : Γ, (rowLaw9 S E G ω b.1).w (γ b)) *
        (∏ i : Fin k,
          (if predFail9 S E G ω (a i) (ys γ i) then 0 else 1) *
            ((N : ℝ) * evenRowAt9 S E G ω (a i) (ys γ i) x))
    have hrow (z : ∀ i : Fin k, StarOdd9 (a i) → Fin N) :
        (∏ b : Γ, (rowLaw9 S E G ω b.1).w ((Efun.symm z) b)) =
          ∏ i : Fin k, ∏ b : StarOdd9 (a i),
            (rowLaw9 S E G ω b.1).w (z i b) := by
      calc
        _ = ∏ p : StarIndex9 a,
            (rowLaw9 S E G ω (e p).1).w ((Efun.symm z) (e p)) := by
              symm
              exact Fintype.prod_equiv e _ _ (by intro p; rfl)
        _ = ∏ p : StarIndex9 a, (rowLaw9 S E G ω (e p).1).w (z p.1 p.2) := by
              apply Finset.prod_congr rfl
              intro p hp
              change (rowLaw9 S E G ω (e p).1).w
                (z (e.symm (e p)).1 (e.symm (e p)).2) = _
              rw [Equiv.symm_apply_apply e p]
        _ = ∏ i : Fin k, ∏ b : StarOdd9 (a i),
              (rowLaw9 S E G ω b.1).w (z i b) := by
              rw [Fintype.prod_sigma]
              apply Finset.prod_congr rfl
              intro i hi
              apply Finset.prod_congr rfl
              intro b hb
              rw [starDataEquiv9_val a hsep ⟨i, b⟩]
              simp [starSite9]
    have hH (z : ∀ i : Fin k, StarOdd9 (a i) → Fin N) :
        H (Efun.symm z) = ∏ i : Fin k, localF i (z i) := by
      dsimp [H]
      have hy (i : Fin k) : ys (Efun.symm z) i = z i := by
        funext b
        change z (e.symm (e ⟨i, b⟩)).1 (e.symm (e ⟨i, b⟩)).2 = z i b
        rw [Equiv.symm_apply_apply e ⟨i, b⟩]
      rw [hrow z]
      simp_rw [hy]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      dsimp [localF]
      ring
    have hfactor :
        (∑ γ : Γ → Fin N, W γ * g γ) =
          2 * ∏ i : Fin k, evenStar9 S E G ω (a i) x := by
      calc
        _ = ∑ γ : Γ → Fin N, 2 * H γ := by
              apply Finset.sum_congr rfl
              intro γ hγ
              simp [W, g, H]
              ring
        _ = 2 * ∑ γ : Γ → Fin N, H γ := by rw [← Finset.mul_sum]
        _ = 2 * ∑ z : ∀ i : Fin k, StarOdd9 (a i) → Fin N,
              ∏ i : Fin k, localF i (z i) := by
              congr 1
              calc
                (∑ γ : Γ → Fin N, H γ) =
                    ∑ z : ∀ i : Fin k, StarOdd9 (a i) → Fin N, H (Efun.symm z) :=
                      (Equiv.sum_comp Efun.symm H).symm
                _ = ∑ z : ∀ i : Fin k, StarOdd9 (a i) → Fin N,
                      ∏ i : Fin k, localF i (z i) := by
                      apply Finset.sum_congr rfl
                      intro z hz
                      exact hH z
        _ = 2 * ∏ i : Fin k, evenStar9 S E G ω (a i) x := by
              congr 1
              calc
                (∑ z : ∀ i : Fin k, StarOdd9 (a i) → Fin N,
                    ∏ i : Fin k, localF i (z i)) =
                      ∏ i : Fin k, ∑ z : StarOdd9 (a i) → Fin N, localF i z :=
                        sum_prod_stars9 a localF
                _ = ∏ i : Fin k, evenStar9 S E G ω (a i) x := by
                      apply Finset.prod_congr rfl
                      intro i hi
                      exact hlocal i
    calc
      _ = (J ω).expect (fun f => g (proj f)) := hleft
      _ ≤ ∑ γ, W γ * g γ := map_expect_le_of_weight_bound9 (J ω) proj W g hweight hgNonneg
      _ = 2 * ∏ i : Fin k, evenStar9 S E G ω (a i) x := hfactor

theorem evenStar9_nonneg {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (x : Fin N) :
    0 ≤ evenStar9 S E G ω v x := by
  classical
  unfold evenStar9
  apply Finset.sum_nonneg
  intro ys hys
  by_cases hfail : predFail9 S E G ω v ys
  · simp [hfail]
  · have hmargin : starMarg9 S E G ω v ys ≠ 0 := by
      intro hz
      exact hfail (Or.inl hz)
    have hmargin_nonneg : 0 ≤ starMarg9 S E G ω v ys := by
      unfold starMarg9
      apply Finset.sum_nonneg
      intro x' hx'
      exact mul_nonneg ((siteFirst9 S v.1).nonneg x') (starLik9_nonneg S E G ω v x' ys)
    have hmargin_pos : 0 < starMarg9 S E G ω v ys :=
      lt_of_le_of_ne hmargin_nonneg (Ne.symm hmargin)
    have hrow : 0 ≤ evenRowAt9 S E G ω v ys x := by
      unfold evenRowAt9
      apply div_nonneg
      · exact mul_nonneg (starLik9_nonneg S E G ω v x ys) ((siteFirst9 S v.1).nonneg x)
      · exact hmargin_pos.le
    have hactual : 0 ≤ starLik9 S E G ω v (anc9 ω (I.center v.1)) ys :=
      starLik9_nonneg S E G ω v (anc9 ω (I.center v.1)) ys
    simp only [if_neg hfail, one_mul]
    exact mul_nonneg hactual (mul_nonneg (by positivity) hrow)

set_option maxHeartbeats 1000000 in
theorem p92_even_moment_helper {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (J : Outcome9 I N → FinProb (OddSites9 n → Fin N))
    (hfac : ClockFactor9 S I E G J) (hint : EvenAnchorIntegral9 S I E G) :
    EvenMoment9 S I E G J := by
  classical
  intro x k hk a hsep
  by_cases hk0 : k = 0
  · subst k
    have hterm (ω : Outcome9 I N) :
        (anchorLaw9 S I E G).w ω *
          (if GoodPre9 S E G ω then
            ∑ f, (J ω).w f * ∏ i : Fin 0, (N : ℝ) * evenRow9 S E G ω f (a i) x
           else 0) ≤ (anchorLaw9 S I E G).w ω := by
      have hsum := (J ω).sum_eq_one
      by_cases hg : GoodPre9 S E G ω
      · simp [hg, hsum]
      · simp [hg, (anchorLaw9 S I E G).nonneg ω]
    calc
      _ ≤ ∑ ω, (anchorLaw9 S I E G).w ω := Finset.sum_le_sum fun ω hω => hterm ω
      _ = 1 := (anchorLaw9 S I E G).sum_eq_one
      _ = 4 ^ (0 : ℕ) * ∏ i : Fin 0, (N : ℝ) * (siteFirst9 S (a i).1).w x := by simp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hpow : 2 * (2 : ℝ) ^ k ≤ (4 : ℝ) ^ k := by
      have htwoNat : 2 ≤ 2 ^ k := by
        cases k with
        | zero => omega
        | succ k =>
            have hbase : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
            calc
              2 = 1 * 2 := by norm_num
              _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 hbase
              _ = 2 ^ (k + 1) := by simp [Nat.pow_succ]
      have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast htwoNat
      calc
        2 * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right htwo (by positivity)
        _ = (4 : ℝ) ^ k := by rw [← mul_pow]; norm_num
    have hprod_nonneg : 0 ≤ ∏ i : Fin k, (N : ℝ) * (siteFirst9 S (a i).1).w x :=
      Finset.prod_nonneg fun i hi => mul_nonneg (by positivity) ((siteFirst9 S (a i).1).nonneg x)
    have hstar_nonneg (ω : Outcome9 I N) :
        0 ≤ ∏ i : Fin k, evenStar9 S E G ω (a i) x :=
      Finset.prod_nonneg fun i hi => evenStar9_nonneg S E G ω (a i) x
    have hpoint (ω : Outcome9 I N) :
        (anchorLaw9 S I E G).w ω *
          (if GoodPre9 S E G ω then
            ∑ f, (J ω).w f * ∏ i : Fin k, (N : ℝ) * evenRow9 S E G ω f (a i) x
           else 0) ≤
        (anchorLaw9 S I E G).w ω *
          (2 * (if GoodPre9 S E G ω then ∏ i : Fin k, evenStar9 S E G ω (a i) x else 0)) := by
      have hw : 0 ≤ (anchorLaw9 S I E G).w ω := (anchorLaw9 S I E G).nonneg ω
      by_cases hg : GoodPre9 S E G ω
      · simp only [hg, if_pos]
        exact mul_le_mul_of_nonneg_left (hfac ω hg x k hk a hsep) hw
      · simp [hg]
    calc
      _ ≤ ∑ ω, (anchorLaw9 S I E G).w ω *
            (2 * (if GoodPre9 S E G ω then ∏ i : Fin k, evenStar9 S E G ω (a i) x else 0)) :=
          Finset.sum_le_sum fun ω hω => hpoint ω
      _ = 2 * ∑ ω, (anchorLaw9 S I E G).w ω *
            (if GoodPre9 S E G ω then ∏ i : Fin k, evenStar9 S E G ω (a i) x else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω hω
          ring
      _ ≤ 2 * ∑ ω, (anchorLaw9 S I E G).w ω *
            (∏ i : Fin k, evenStar9 S E G ω (a i) x) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro ω hω
          by_cases hg : GoodPre9 S E G ω
          · simp [hg]
          · simp [hg]
            exact mul_nonneg ((anchorLaw9 S I E G).nonneg ω) (hstar_nonneg ω)
      _ = 2 * (anchorLaw9 S I E G).expect
            (fun ω => ∏ i : Fin k, evenStar9 S E G ω (a i) x) := by rfl
      _ ≤ 2 * ((2 : ℝ) ^ k * ∏ i : Fin k, (N : ℝ) * (siteFirst9 S (a i).1).w x) :=
          mul_le_mul_of_nonneg_left (hint x k hk a hsep) (by norm_num)
      _ ≤ (4 : ℝ) ^ k * ∏ i : Fin k, (N : ℝ) * (siteFirst9 S (a i).1).w x := by
          nlinarith [mul_le_mul_of_nonneg_right hpow hprod_nonneg]

theorem p92_delta_lt_half {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n < 1 / 2 := by
  have hnat : n * 2 < 2 ^ n := by
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hbase : n = 2
        · subst n
          norm_num
        · have hn3 : 3 ≤ n := by omega
          have hprev := ih hn3
          have hprev' : 2 * n < 2 ^ n := by simpa [Nat.mul_comm] using hprev
          have hle : n + 1 ≤ 2 * n := by omega
          calc
            (n + 1) * 2 ≤ (2 * n) * 2 := Nat.mul_le_mul_right 2 hle
            _ < (2 ^ n) * 2 := Nat.mul_lt_mul_of_pos_right hprev' (by decide)
            _ = 2 ^ (n + 1) := by simp [Nat.pow_succ, Nat.mul_comm]
  have hnatR : (n : ℝ) * 2 < (2 : ℝ) ^ n := by exact_mod_cast hnat
  have hden : 0 < (2 : ℝ) ^ n := pow_pos (show (0 : ℝ) < 2 by norm_num) n
  have hfrac : (n : ℝ) / (2 : ℝ) ^ n < 1 / 2 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hpow : (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  calc
    (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n =
        (n : ℝ) * (2 ^ n * (1 / 4 : ℝ) ^ n) := by ring
    _ = (n : ℝ) * (1 / 2 : ℝ) ^ n := by rw [hpow]
    _ = (n : ℝ) / (2 : ℝ) ^ n := by
          have hpow' : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by
            rw [div_pow]
            simp
          rw [hpow']
          simp [div_eq_mul_inv]
    _ < 1 / 2 := hfrac

private theorem finProb_pr_compl {Ω : Type*} [Fintype Ω]
    (Q : FinProb Ω) (A : Ω → Prop) :
    Q.pr A + Q.pr (fun ω => ¬ A ω) = 1 := by
  classical
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ ω, Q.w ω := by
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases hA : A ω <;> simp [hA]
    _ = 1 := Q.sum_eq_one

private theorem finProb_bind_pr {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (A : α → Prop) (B : α → β → Prop) :
    (∑ a, P.w a * (if A a then (K a).pr (B a) else 0)) =
      (FinProb.bind P K).pr (fun ab => A ab.1 ∧ B ab.1 ab.2) := by
  classical
  unfold FinProb.pr FinProb.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hA : A a
  · simp only [hA, if_pos]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hB : B a b <;> simp [hA, hB]
  · simp [hA]

set_option maxHeartbeats 1000000 in
theorem p92_realization_core {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    {E : Fin N → Fin N → Prop} {G : Colour}
    (S : Setup9 P n N M) (hN : 0 < N)
    (havoid : 0 < (rawLaw9 S I).pr (fun ω => ∀ v, ¬ StarBad9 S E G ω v))
    (hodd :
      (anchorLaw9 S I E G).pr
        (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn9 S E G ω y) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n)
    (hsampler : ∀ ω : Outcome9 I N, GoodPre9 S E G ω → ∃ J, ClockOK9 S E G ω J)
    (heven :
      ∀ J : Outcome9 I N → FinProb (OddSites9 n → Fin N),
        (∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) →
        ∑ ω, (anchorLaw9 S I E G).w ω *
            (if GoodPre9 S E G ω then
              (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n)
    (hδ : 2 * ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) < 1) :
    ∃ (ω : Outcome9 I N) (f : OddSites9 n → Fin N),
      (∀ v, ¬ StarBad9 S E G ω v) ∧
      Function.Injective f ∧ (∀ v, ¬ predFail9 S E G ω v (nbrLabels9 f)) ∧
      ∀ x, evenColumn9 S E G ω f x ≤ 1 := by
  classical
  let Aw : Outcome9 I N → Prop := fun ω => ∀ v, ¬ StarBad9 S E G ω v
  let Good : Outcome9 I N → Prop := fun ω => GoodPre9 S E G ω
  have hanchorFormula (ω : Outcome9 I N) :
      (anchorLaw9 S I E G).w ω =
        (if Aw ω then (rawLaw9 S I).w ω else 0) / (rawLaw9 S I).pr Aw := by
    have hA : 0 < (rawLaw9 S I).pr Aw := by simpa [Aw] using havoid
    unfold anchorLaw9 S07.condOr
    rw [dif_pos hA]
    simp [FinProb.cond, Aw]
  have hsupport (ω : Outcome9 I N) (hw : (anchorLaw9 S I E G).w ω ≠ 0) :
      (rawLaw9 S I).w ω ≠ 0 ∧ Aw ω := by
    constructor
    · intro hr
      rw [hanchorFormula] at hw
      by_cases ha : Aw ω <;> simp [ha, hr] at hw
    · by_contra ha
      have hz : (anchorLaw9 S I E G).w ω = 0 := by
        rw [hanchorFormula]
        simp [ha]
      exact hw hz
  have hgood_of_no_odd (ω : Outcome9 I N) (hw : (anchorLaw9 S I E G).w ω ≠ 0)
      (hno : ¬ ∃ y, (1e-8 : ℝ) < oddColumn9 S E G ω y) : Good ω := by
    rcases hsupport ω hw with ⟨hr, ha⟩
    refine ⟨hr, ha, ?_⟩
    intro y
    exact le_of_not_gt (fun h => hno ⟨y, h⟩)
  have hnotgood_odd (ω : Outcome9 I N) (hg : ¬ Good ω)
      (hw : (anchorLaw9 S I E G).w ω ≠ 0) :
      ∃ y, (1e-8 : ℝ) < oddColumn9 S E G ω y := by
    by_contra hno
    exact hg (hgood_of_no_odd ω hw hno)
  have hnotgood_mass :
      (anchorLaw9 S I E G).pr (fun ω => ¬ Good ω) ≤
        (anchorLaw9 S I E G).pr
          (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn9 S E G ω y) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro ω hω
    by_cases hng : ¬ Good ω
    · by_cases hw : (anchorLaw9 S I E G).w ω = 0
      · simp [hng, hw]
      · have hb := hnotgood_odd ω hng hw
        simp [hng, hb]
    · by_cases hb : ∃ y, (1e-8 : ℝ) < oddColumn9 S E G ω y
      · simp [hng, hb, (anchorLaw9 S I E G).nonneg ω]
      · simp [hng, hb]
  have hbadmass :
      (anchorLaw9 S I E G).pr (fun ω => ¬ Good ω) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n :=
    hnotgood_mass.trans hodd
  have hprsum :
      (anchorLaw9 S I E G).pr Good +
        (anchorLaw9 S I E G).pr (fun ω => ¬ Good ω) = 1 := by
    exact finProb_pr_compl (anchorLaw9 S I E G) Good
  have hgood_lower :
      1 - ((n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n) ≤
        (anchorLaw9 S I E G).pr Good := by
    linarith
  let y₀ : Fin N := ⟨0, by omega⟩
  let f₀ : OddSites9 n → Fin N := fun _ => y₀
  let J₀ : FinProb (OddSites9 n → Fin N) :=
    FinProb.uniform Finset.univ ⟨f₀, Finset.mem_univ _⟩
  let J : Outcome9 I N → FinProb (OddSites9 n → Fin N) := fun ω =>
    if hg : Good ω then Classical.choose (hsampler ω hg) else J₀
  have hJ (ω : Outcome9 I N) (hg : Good ω) : ClockOK9 S E G ω (J ω) := by
    dsimp [J]
    simp only [dif_pos hg]
    exact Classical.choose_spec (hsampler ω hg)
  have hEven := heven J (by intro ω hg; exact hJ ω hg)
  by_contra hno
  have hbad_support (ω : Outcome9 I N) (hg : Good ω)
      (hw : (anchorLaw9 S I E G).w ω ≠ 0) (f : OddSites9 n → Fin N)
      (hf : (J ω).w f ≠ 0) :
      ∃ x, 1 < evenColumn9 S E G ω f x := by
    by_contra hbad
    have hcol : ∀ x, evenColumn9 S E G ω f x ≤ 1 := by
      intro x
      exact le_of_not_gt (fun hx => hbad ⟨x, hx⟩)
    rcases (hJ ω hg).1 f hf with ⟨hinj, hpred⟩
    exact hno ⟨ω, f, hg.2.1, hinj, hpred, hcol⟩
  have hbadprob (ω : Outcome9 I N) (hg : Good ω)
      (hw : (anchorLaw9 S I E G).w ω ≠ 0) :
      (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) = 1 := by
    let Bad : (OddSites9 n → Fin N) → Prop :=
      fun f => ∃ x, 1 < evenColumn9 S E G ω f x
    change (J ω).pr Bad = 1
    have hsum :
        (∑ f, if Bad f then (J ω).w f else 0) =
          ∑ f, (J ω).w f := by
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hb : Bad f
      · simp [hb]
      · have hf0 : (J ω).w f = 0 := by
          by_contra hfne
          exact hb (hbad_support ω hg hw f hfne)
        simp [hb, hf0]
    have hpr : (J ω).pr Bad =
        ∑ f, if Bad f then (J ω).w f else 0 := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hb : Bad f <;> simp [hb]
    rw [hpr, hsum, (J ω).sum_eq_one]
  have hgood_equal :
      ∑ ω, (anchorLaw9 S I E G).w ω *
          (if Good ω then
            (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) else 0) =
        (anchorLaw9 S I E G).pr Good := by
    have hsum :
        ∑ ω, (anchorLaw9 S I E G).w ω *
            (if Good ω then
              (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) else 0) =
          ∑ ω, (if Good ω then (anchorLaw9 S I E G).w ω else 0) := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hg : Good ω
      · by_cases hw : (anchorLaw9 S I E G).w ω = 0
        · simp [hg, hw]
        · simp only [if_pos hg]
          rw [hbadprob ω hg hw]
          ring
      · simp [hg]
    have hprGood :
        (anchorLaw9 S I E G).pr Good =
          ∑ ω, if Good ω then (anchorLaw9 S I E G).w ω else 0 := by
      rfl
    exact hsum.trans hprGood.symm
  have hgood_upper :
      (anchorLaw9 S I E G).pr Good ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    rw [← hgood_equal]
    exact hEven
  linarith

set_option maxHeartbeats 1000000 in
theorem p92_even_loads_core (P : Params9) (hP : P.Valid) (κ : ℝ) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
        (S : Setup9 P n N M) (I : IDMap9 P n) (cT : ℝ)
        (J : Outcome9 I N → FinProb (OddSites9 n → Fin N)),
        CoreInput9 P κ E X Y G M S I → TagsOK9 κ E G cT S.tag → EvenRowCap9 S I E G →
        (∀ ω, GoodPre9 S E G ω → ClockOK9 S E G ω (J ω)) → EvenMoment9 S I E G J →
        ∑ ω, (anchorLaw9 S I E G).w ω *
            (if GoodPre9 S E G ω then (J ω).pr (fun f => ∃ x, 1 < evenColumn9 S E G ω f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  classical
  let D := tagLoadConst9 κ
  let D₀ := 2 * D
  let C₀ : ℝ := 16 * (D₀ + 1)
  let threshold : ℝ := 4 * 4 * (D₀ + 1)
  refine ⟨3, C₀, ?_⟩
  intro n N hLarge E X Y G M S I cT J hCore hTags hCap hClock hMoment
  let L : ℝ := (2 : ℝ) ^ n *
    Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 2))
  rcases hCore with ⟨hN, hprep, hdeep, htagweight, hmask, hdeepTools, hexps, hscale⟩
  rcases hscale with ⟨hn1, hmn, hradius, hss, hbudget, hfirst, hbStar, hlast⟩
  have hn3 : 3 ≤ n := hLarge.1
  have hnpos : 0 < n := by omega
  have hcardEven : Fintype.card (EvenSites9 n) = 2 ^ (n - 1) :=
    evenSites_card9 hnpos
  have hcardEvenR : (Fintype.card (EvenSites9 n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast hcardEven
  have hcardCube : Fintype.card (CubeVertex n) = 2 ^ n := by
    simp [OAI.HypercubeRamsey.card_cubeVertex]
  have hcardCubeR : (Fintype.card (CubeVertex n) : ℝ) = (2 : ℝ) ^ n := by
    exact_mod_cast hcardCube
  have hpower : (2 : ℝ) ^ n = (2 : ℝ) * (2 : ℝ) ^ (n - 1) := by
    have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1 + 1) := by
        exact congrArg (fun k : ℕ => (2 : ℝ) ^ k) hnsub.symm
      _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (n - 1) := by ring
  have hU : Nonempty (EvenSites9 n) := by
    let z : CubeVertex n := fun _ => false
    have hz : IsEvenRole z := by simp [z, IsEvenRole]
    exact ⟨⟨z, hz⟩⟩
  let U := EvenSites9 n
  haveI : Nonempty U := hU
  let Joint := Outcome9 I N × (OddSites9 n → Fin N)
  let Q : FinProb Joint := FinProb.bind (anchorLaw9 S I E G) J
  let Z : U → Fin N → Joint → ℝ := fun v y q =>
    if GoodPre9 S E G q.1 ∧ (J q.1).w q.2 ≠ 0 then
      (N : ℝ) * evenRowAt9 S E G q.1 v (nbrLabels9 q.2) y else 0
  let d : U → Fin N → ℝ := fun v y => (N : ℝ) * (siteFirst9 S v.1).w y
  let near : U → Finset U := fun v =>
    Finset.univ.filter (fun v' => siteNear9 P n v.1 v'.1)
  let fNear : ℝ :=
    ((n + 1 : ℝ) ^ (4 * P.radius n + 14)) / (2 : ℝ) ^ (n - 1)
  have hDpos : 0 < D := by
    dsimp [D, tagLoadConst9]
    positivity
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hC0pos : 0 < C₀ := by dsimp [C₀, D₀]; positivity
  have hthreshold : threshold = C₀ := by
    dsimp [threshold, C₀, D₀]
    ring
  have hDtag (y : Fin N) : ((2 : ℝ) ^ (P.m n))⁻¹ *
      ∑ z : CubeVertex (P.m n), (N : ℝ) * (M.μ (S.tag z)).w y ≤ D := by
    simpa [D] using hTags.2.1.1 y
  have hCubeLoad (y : Fin N) :
      (Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ v : CubeVertex n,
        (N : ℝ) * (siteFirst9 S v).w y ≤ D := by
    rw [hcardCubeR]
    have hm : P.m n ≤ n := hmn
    have hsum := sum_specialWord9 hm
      (fun z : CubeVertex (P.m n) => (N : ℝ) * (M.μ (S.tag z)).w y)
    have hpowm : (2 : ℝ) ^ n =
        (2 : ℝ) ^ (P.m n) * (2 : ℝ) ^ (n - P.m n) := by
      have hmEq : P.m n + (n - P.m n) = n := Nat.add_sub_of_le hmn
      calc
        (2 : ℝ) ^ n = (2 : ℝ) ^ (P.m n + (n - P.m n)) :=
          congrArg (fun k : ℕ => (2 : ℝ) ^ k) hmEq.symm
        _ = (2 : ℝ) ^ (P.m n) * (2 : ℝ) ^ (n - P.m n) := by rw [pow_add]
    calc
      ((2 : ℝ) ^ n)⁻¹ * ∑ v : CubeVertex n, (N : ℝ) * (siteFirst9 S v).w y =
          ((2 : ℝ) ^ n)⁻¹ *
            ((2 : ℝ) ^ (n - P.m n) *
              ∑ z : CubeVertex (P.m n), (N : ℝ) * (M.μ (S.tag z)).w y) := by
                congr 1
      _ = ((2 : ℝ) ^ (P.m n))⁻¹ *
            ∑ z : CubeVertex (P.m n), (N : ℝ) * (M.μ (S.tag z)).w y := by
                rw [hpowm]
                field_simp
      _ ≤ D := hDtag y
  have hfull_nonneg (v : CubeVertex n) (y : Fin N) :
      0 ≤ (N : ℝ) * (siteFirst9 S v).w y :=
    mul_nonneg (by positivity) ((siteFirst9 S v).nonneg y)
  have hsumEven (y : Fin N) :
      (∑ v : U, d v y) ≤
        ∑ v : CubeVertex n, (N : ℝ) * (siteFirst9 S v).w y := by
    simpa [U, d] using sum_even_sites_le_cube
      (fun v => (N : ℝ) * (siteFirst9 S v).w y) (hfull_nonneg · y)
  have hmean (y : Fin N) :
      (Fintype.card U : ℝ)⁻¹ * ∑ v : U, d v y ≤ D₀ := by
    have hcardPos : 0 < (Fintype.card U : ℝ) := by positivity
    have hmeanStep :
        (Fintype.card U : ℝ)⁻¹ * ∑ v : U, d v y ≤
          (Fintype.card U : ℝ)⁻¹ *
            ∑ v : CubeVertex n, (N : ℝ) * (siteFirst9 S v).w y :=
      mul_le_mul_of_nonneg_left (hsumEven y) (inv_nonneg.mpr hcardPos.le)
    have hratio :
        (Fintype.card U : ℝ)⁻¹ *
            ∑ v : CubeVertex n, (N : ℝ) * (siteFirst9 S v).w y =
          2 * ((Fintype.card (CubeVertex n) : ℝ)⁻¹ *
            ∑ v : CubeVertex n, (N : ℝ) * (siteFirst9 S v).w y) := by
      rw [hcardEvenR, hcardCubeR]
      rw [hpower]
      field_simp
    calc
      (Fintype.card U : ℝ)⁻¹ * ∑ v : U, d v y ≤
          (Fintype.card U : ℝ)⁻¹ *
            ∑ v : CubeVertex n, (N : ℝ) * (siteFirst9 S v).w y := hmeanStep
      _ = 2 * ((Fintype.card (CubeVertex n) : ℝ)⁻¹ *
            ∑ v : CubeVertex n, (N : ℝ) * (siteFirst9 S v).w y) := hratio
      _ ≤ D₀ := by dsimp [D₀]; nlinarith [hCubeLoad y]
  have hnear_self (v : U) : v ∈ near v := by
    unfold near
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold siteNear9
    rw [hammingDist_self, hammingDist_self]
    constructor <;> omega
  have hnear_count (v : U) :
      ((near v).card : ℝ) ≤ fNear * Fintype.card U := by
    have hnat := evenSiteNear_card_poly hmn v
    have hcast : ((near v).card : ℝ) ≤
        (n + 1 : ℝ) ^ (4 * P.radius n + 14) := by exact_mod_cast hnat
    have hcardEvenR : (Fintype.card U : ℝ) = (2 : ℝ) ^ (n - 1) := by
      exact_mod_cast hcardEven
    calc
      ((near v).card : ℝ) ≤ (n + 1 : ℝ) ^ (4 * P.radius n + 14) := hcast
      _ = fNear * Fintype.card U := by
        dsimp [fNear]
        rw [hcardEvenR]
        field_simp
  have hZnonneg (v : U) (yy : Fin N) (q : Joint) : 0 ≤ Z v yy q := by
    by_cases hg : GoodPre9 S E G q.1
    · by_cases hs : (J q.1).w q.2 ≠ 0
      · simp [Z, hg, hs]
        exact mul_nonneg (by positivity)
          (evenRowAt9_nonneg S E G q.1 v (nbrLabels9 q.2) yy)
      · simp [Z, hg, hs]
    · simp [Z, hg]
  have hZcap (v : U) (yy : Fin N) (q : Joint) (hq : q ∈ Finset.univ) :
      Z v yy q ≤ L := by
    rcases q with ⟨ω, f⟩
    by_cases hg : GoodPre9 S E G ω
    · by_cases hs : (J ω).w f ≠ 0
      · have hpred : ¬ predFail9 S E G ω v (nbrLabels9 f) :=
          ((hClock ω hg).1 f hs).2 v
        have hcap := hCap ω v (nbrLabels9 f) hpred yy
        simpa [Z, hg, hs, L] using hcap
      · simp [Z, hg, hs]
        positivity
    · simp [Z, hg]
      positivity
  have hZmoment :
      ∀ yy (k : ℕ), k ≤ n → ∀ s : Fin k → U,
        (∀ i j, j < i → s i ∉ near (s j)) →
        ∑ q, Q.w q * ∏ i, Z (s i) yy q ≤
          (4 : ℝ) ^ k * ∏ i, d (s i) yy := by
    intro yy k hk s hsep
    by_cases hk0 : k = 0
    · subst k
      simp only [Fin.prod_univ_zero, mul_one, pow_zero]
      rw [Q.sum_eq_one]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hprod (q : Joint) :
          ∏ i : Fin k, Z (s i) yy q =
            if GoodPre9 S E G q.1 ∧ (J q.1).w q.2 ≠ 0 then
              ∏ i : Fin k, (N : ℝ) *
                evenRowAt9 S E G q.1 (s i) (nbrLabels9 q.2) yy else 0 := by
        by_cases hgood : GoodPre9 S E G q.1 ∧ (J q.1).w q.2 ≠ 0
        · simp [Z, hgood]
        · have i0 : Fin k := ⟨0, hkpos⟩
          have hz : Z (s i0) yy q = 0 := by simp [Z, hgood]
          rw [if_neg hgood]
          rw [Finset.prod_eq_zero (Finset.mem_univ i0) hz]
      have hsum :
          ∑ q : Joint, Q.w q * ∏ i : Fin k, Z (s i) yy q =
            ∑ ω, (anchorLaw9 S I E G).w ω *
              (if GoodPre9 S E G ω then
                ∑ f, (J ω).w f *
                  ∏ i : Fin k, (N : ℝ) *
                    evenRowAt9 S E G ω (s i) (nbrLabels9 f) yy else 0) := by
        rw [Fintype.sum_prod_type]
        simp_rw [Q, FinProb.bind, hprod]
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hg : GoodPre9 S E G ω
        · simp only [hg, if_pos]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro f hf
          by_cases hs : (J ω).w f ≠ 0
          · simp [hs, hg] <;> ring_nf
          · have hzero : (J ω).w f = 0 := not_ne_iff.mp hs
            simp [hzero]
        · simp [hg]
      calc
        ∑ q : Joint, Q.w q * ∏ i : Fin k, Z (s i) yy q =
            ∑ ω, (anchorLaw9 S I E G).w ω *
              (if GoodPre9 S E G ω then
                ∑ f, (J ω).w f *
                  ∏ i : Fin k, (N : ℝ) *
                    evenRowAt9 S E G ω (s i) (nbrLabels9 f) yy else 0) := hsum
        _ ≤ (4 : ℝ) ^ k * ∏ i : Fin k, d (s i) yy := by
          simpa [evenRow9] using hMoment yy k hk s (by
            intro i j hji hne
            apply hsep i j hji
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ _,
              siteNear9_symm (P := P) (n := n) (s i).1 (s j).1 hne⟩)
  have hLpos : 0 < L := by positivity
  have hD0nonneg : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hK : (1 : ℝ) ≤ 4 := by norm_num
  have hsmall : (n : ℝ) * fNear * L ≤ 1 := by
    -- The final scale inequality leaves enough exponential room for the near-site count and row cap.
    have hrn : 0 ≤ (P.radius n : ℝ) := by positivity
    have hlogn : 0 ≤ Real.log ((n : ℝ) + 1) := by
      exact Real.log_nonneg (by
        exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega))
    have hlogBound :
        Real.log (2 * (n : ℝ)) +
            (4 * (P.radius n : ℝ) + 14) * Real.log ((n : ℝ) + 1) ≤
          4 * ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) := by
      have hln : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by positivity) (by linarith)
      have hltwo : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by norm_num) (by
          exact_mod_cast (show (2 : ℕ) ≤ n + 1 by omega))
      rw [Real.log_mul (by norm_num) (by positivity)]
      nlinarith
    have hgain : 0 < gainConst9 * (n : ℝ) * P.aStar n := by
      dsimp [gainConst9, Params9.aStar]
      positivity
    have hlogSmall :
        Real.log (2 * (n : ℝ)) +
            (4 * (P.radius n : ℝ) + 14) * Real.log ((n : ℝ) + 1) ≤
          gainConst9 * (n : ℝ) * P.aStar n / 2 := by
      have hlast' : 4 * ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
          gainConst9 * (n : ℝ) * P.aStar n / 25 := by
        have hnxs : 0 ≤ (n : ℝ) ^ (P.xS : ℝ) := by positivity
        have hnu : 0 ≤ (n : ℝ) ^ P.u := by positivity
        have hq :
            ((P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
              gainConst9 * (n : ℝ) * P.aStar n / 100 := by
          linarith
        nlinarith
      linarith
    have hApos : 0 < (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ (4 * P.radius n + 14) :=
      by positivity
    have hAlog :
        Real.log ((2 * (n : ℝ)) * ((n : ℝ) + 1) ^ (4 * P.radius n + 14)) =
          Real.log (2 * (n : ℝ)) +
            (4 * (P.radius n : ℝ) + 14) * Real.log ((n : ℝ) + 1) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      norm_num [Nat.cast_add, Nat.cast_mul]
    have hlogA :
        Real.log ((2 * (n : ℝ)) * ((n : ℝ) + 1) ^ (4 * P.radius n + 14)) ≤
          gainConst9 * (n : ℝ) * P.aStar n / 2 := by
      rw [hAlog]
      exact hlogSmall
    have hAexp :
        (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ (4 * P.radius n + 14) ≤
          Real.exp (gainConst9 * (n : ℝ) * P.aStar n / 2) :=
      (Real.log_le_iff_le_exp hApos).mp hlogA
    have hbasic :
        (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ (4 * P.radius n + 14) *
            Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 2)) ≤ 1 := by
      calc
        _ ≤ Real.exp (gainConst9 * (n : ℝ) * P.aStar n / 2) *
            Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 2)) :=
          mul_le_mul_of_nonneg_right hAexp (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have heq :
        (n : ℝ) * fNear * L =
          (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ (4 * P.radius n + 14) *
            Real.exp (-(gainConst9 * (n : ℝ) * P.aStar n / 2)) := by
      dsimp [fNear, L]
      rw [hpower]
      field_simp [pow_ne_zero (n - 1) (by norm_num : (2 : ℝ) ≠ 0)]
    rw [heq]
    exact hbasic
  have hlabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
    have hup := hLarge.2.2
    simpa [Fintype.card_fin] using
      (show (N : ℝ) ≤ (n : ℝ) * 2 ^ n by exact_mod_cast hup)
  have hfNear : 0 ≤ fNear := by positivity
  have hscatter := scatteredMoments_union_labels
    Q Finset.univ Z hZnonneg L (by positivity) hZcap near hnear_self
    fNear hfNear hnear_count n hnpos 4 D₀ (by norm_num) hD0nonneg d
    (by intro v yy; exact mul_nonneg (Nat.cast_nonneg N) ((siteFirst9 S v.1).nonneg yy))
    hmean hZmoment hsmall hlabels
  let hbadEvent : Joint → Prop := fun q =>
    GoodPre9 S E G q.1 ∧ ∃ yy, 1 < evenColumn9 S E G q.1 q.2 yy
  have hbig_of_bad (q : Joint) (hg : GoodPre9 S E G q.1)
      (hs : (J q.1).w q.2 ≠ 0) (yy : Fin N)
      (hbad : 1 < evenColumn9 S E G q.1 q.2 yy) :
      threshold <
        (Fintype.card U : ℝ)⁻¹ * ∑ v : U, Z v yy q := by
    have havg :
        (Fintype.card U : ℝ)⁻¹ * ∑ v : U, Z v yy q =
          ((N : ℝ) / (Fintype.card U : ℝ)) *
            evenColumn9 S E G q.1 q.2 yy := by
      simp [Z, hg, hs, evenColumn9, evenRow9]
      rw [← Finset.mul_sum]
      ring
    have hratio :
        threshold ≤ (N : ℝ) / (Fintype.card U : ℝ) := by
      have hC := hLarge.2.1
      have hC' : C₀ * (2 : ℝ) ^ n ≤ (N : ℝ) := by exact_mod_cast hC
      have hdenPos : 0 < (Fintype.card U : ℝ) := by positivity
      have hden : (Fintype.card U : ℝ) = (2 : ℝ) ^ (n - 1) := by
        exact_mod_cast hcardEven
      apply (le_div_iff₀ hdenPos).2
      rw [hden, hthreshold]
      calc
        C₀ * (2 : ℝ) ^ (n - 1) ≤ C₀ * (2 * (2 : ℝ) ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (n - 1)])
            hC0pos.le
        _ = C₀ * (2 : ℝ) ^ n := by rw [hpower]
        _ ≤ (N : ℝ) := hC'
    have hratioPos : 0 < (N : ℝ) / (Fintype.card U : ℝ) := by
      apply div_pos
      · exact_mod_cast hN
      · positivity
    rw [havg]
    calc
      threshold ≤ (N : ℝ) / (Fintype.card U : ℝ) := hratio
      _ < ((N : ℝ) / (Fintype.card U : ℝ)) * evenColumn9 S E G q.1 q.2 yy := by
        simpa using mul_lt_mul_of_pos_left hbad hratioPos
  have hTargetEq :=
    finProb_bind_pr (anchorLaw9 S I E G) J
      (fun ω => GoodPre9 S E G ω)
      (fun ω f => ∃ yy, 1 < evenColumn9 S E G ω f yy)
  have hTargetEq' :
      (∑ ω, (anchorLaw9 S I E G).w ω *
          (if GoodPre9 S E G ω then
            (J ω).pr (fun f => ∃ yy, 1 < evenColumn9 S E G ω f yy) else 0)) =
        Q.pr hbadEvent := by
    simpa [hbadEvent, Q] using hTargetEq
  have hTargetLe :
      (∑ ω, (anchorLaw9 S I E G).w ω *
          (if GoodPre9 S E G ω then
            (J ω).pr (fun f => ∃ yy, 1 < evenColumn9 S E G ω f yy) else 0)) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    rw [hTargetEq']
    calc
      (FinProb.bind (anchorLaw9 S I E G) J).pr hbadEvent ≤
          ∑ q, if ∃ yy, threshold <
              (Fintype.card U : ℝ)⁻¹ * ∑ v : U, Z v yy q then
                (FinProb.bind (anchorLaw9 S I E G) J).w q else 0 := by
            unfold FinProb.pr
            apply Finset.sum_le_sum
            intro q hq
            by_cases hb : hbadEvent q
            · change GoodPre9 S E G q.1 ∧
                (∃ yy, 1 < evenColumn9 S E G q.1 q.2 yy) at hb
              rcases hb with ⟨hg, yy, hcol⟩
              have hbadq : hbadEvent q := ⟨hg, ⟨yy, hcol⟩⟩
              by_cases hs : (J q.1).w q.2 ≠ 0
              · have hbig := hbig_of_bad q hg hs yy hcol
                have hbigExists : ∃ yy, threshold <
                    (Fintype.card U : ℝ)⁻¹ * ∑ v : U, Z v yy q := ⟨yy, hbig⟩
                simp [hbadq, hbigExists]
              · have hzero : (J q.1).w q.2 = 0 := not_ne_iff.mp hs
                by_cases hbig : ∃ yy,
                    threshold <
                      (Fintype.card U : ℝ)⁻¹ * ∑ v : U, Z v yy q
                · simp [hbadq, hbig]
                · simp [hbadq, hbig, FinProb.bind, hzero]
            · by_cases hbig : ∃ yy,
                threshold <
                  (Fintype.card U : ℝ)⁻¹ * ∑ v : U, Z v yy q
              · simp [hbadEvent, hb, hbig,
                  (FinProb.bind (anchorLaw9 S I E G) J).nonneg q]
              · simp [hbadEvent, hb, hbig]
      _ ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
        simpa [threshold, U, Q, FinProb.pr] using hscatter
  exact hTargetLe

private theorem hitSet9_updAnc_away {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (ids : Finset I.ID) (c : I.ID) (x : Fin N)
    (hc : c ∉ ids) :
    hitSet9 E G (updAnc9 ω c x) ids = hitSet9 E G ω ids := by
  classical
  ext y
  simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hy d hd
    have hne : d ≠ c := by
      intro heq
      subst d
      exact hc hd
    have hdy := hy d hd
    rw [anc9_update_ne ω c d x hne] at hdy
    exact hdy
  · intro hy d hd
    have hne : d ≠ c := by
      intro heq
      subst d
      exact hc hd
    have hdy := hy d hd
    rw [anc9_update_ne ω c d x hne]
    exact hdy

private theorem rowLaw9_updAnc_away {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (b : OddSites9 n) (c : I.ID) (x : Fin N)
    (hc : c ∉ I.seen b.1) :
  rowLaw9 S E G (updAnc9 ω c x) b = rowLaw9 S E G ω b := by
  unfold rowLaw9
  rw [maskedLaw9_updAnc (S := S) (b := b) (ω := ω) (c := c) (x := x)]
  rw [hitSet9_updAnc_away E G ω (I.seen b.1) c x hc]

private theorem delLaw9_updAnc_away {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (b : OddSites9 n) (t c : I.ID) (x : Fin N)
    (hc : c ∉ I.seen b.1) :
  delLaw9 S E G (updAnc9 ω c x) b t = delLaw9 S E G ω b t := by
  unfold delLaw9
  rw [maskedLaw9_updAnc (S := S) (b := b) (ω := ω) (c := c) (x := x)]
  apply congrArg (restrictOr9 (maskedLaw9 S ω b))
  apply hitSet9_updAnc_away E G ω ((I.seen b.1).erase t) c x
  intro hmem
  exact hc (Finset.mem_of_mem_erase hmem)

private theorem fullOrder9_mem_seen {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} {d : I.ID}
    (hb : (cube n).Adj v.1 b.1) (hd : d ∈ fullOrder9 I v b) : d ∈ I.seen b.1 := by
  classical
  unfold fullOrder9 at hd
  rcases List.mem_append.mp hd with houtcore | htarget
  · rcases List.mem_append.mp houtcore with hout | hcore
    · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hout)).1
    · have hcore' : d ∈ coreIDs9 I v b := Finset.mem_toList.mp hcore
      exact (Finset.mem_inter.mp (Finset.mem_erase.mp hcore').2).1
  · have h : d = I.center v.1 := by simpa using htarget
    rw [h]
    exact center_mem_seen9 ⟨b, hb⟩

private theorem prefixLaw9_updAnc_away {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base : Law N) (order : List I.ID) (k : ℕ)
    (c : I.ID) (x : Fin N) (haway : ∀ d ∈ order, d ≠ c) :
    prefixLaw9 E G (updAnc9 ω c x) base order k = prefixLaw9 E G ω base order k := by
  unfold prefixLaw9
  congr 1
  apply hitSet9_updAnc_away E G ω (order.take k).toFinset c x
  intro hc
  have hmem : c ∈ order :=
    List.Sublist.subset (List.take_sublist k order) (List.mem_toFinset.mp hc)
  exact haway c hmem rfl

private theorem orderRegular9_updAnc_away {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (base₁ base₂ : Law N) (order : List I.ID)
    (c : I.ID) (x : Fin N) (hbase : base₁ = base₂)
    (haway : ∀ d ∈ order, d ≠ c) :
    orderRegular9 E G (updAnc9 ω c x) base₁ order ↔ orderRegular9 E G ω base₂ order := by
  have hprefix (k : ℕ) :
      prefixLaw9 E G (updAnc9 ω c x) base₁ order k = prefixLaw9 E G ω base₂ order k := by
    rw [hbase]
    exact prefixLaw9_updAnc_away E G ω base₂ order k c x haway
  have hanc (d : I.ID) (hd : d ∈ order) :
      anc9 (updAnc9 ω c x) d = anc9 ω d := by
    exact anc9_update_ne ω c d x (haway d hd)
  constructor
  · intro h k d hk hprev
    have hd : d ∈ order := List.mem_of_getElem? hk
    have hprev' : ∀ j d', j < k → order[j]? = some d' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 (updAnc9 ω c x) d')
          (prefixLaw9 E G (updAnc9 ω c x) base₁ order j) := by
      intro j d' hj hj'
      have hd' : d' ∈ order := List.mem_of_getElem? hj'
      simpa [hanc d' hd', hprefix j] using hprev j d' hj hj'
    have hval := h k d hk hprev'
    simpa [hanc d hd, hprefix k] using hval
  · intro h k d hk hprev
    have hd : d ∈ order := List.mem_of_getElem? hk
    have hprev' : ∀ j d', j < k → order[j]? = some d' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω d')
          (prefixLaw9 E G ω base₂ order j) := by
      intro j d' hj hj'
      have hd' : d' ∈ order := List.mem_of_getElem? hj'
      simpa [hanc d' hd', hprefix j] using hprev j d' hj hj'
    have hval := h k d hk hprev'
    simpa [hanc d hd, hprefix k] using hval

private theorem coreOrder9_mem_seen {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} {d : I.ID}
    (hd : d ∈ coreOrder9 I v b) : d ∈ I.seen b.1 := by
  have hcore : d ∈ coreIDs9 I v b := Finset.mem_toList.mp hd
  exact (Finset.mem_inter.mp (Finset.mem_erase.mp hcore).2).1

private theorem targetFrac9_updAnc_away {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (b : StarOdd9 v) (c : I.ID) (x : Fin N)
    (hc : c ∉ I.seen b.1.1) :
    targetFrac9 S E G (updAnc9 ω c x) v b.1 = targetFrac9 S E G ω v b.1 := by
  have hcenter : c ≠ I.center v.1 := by
    intro heq
    subst c
    exact hc (center_mem_seen9 b)
  unfold targetFrac9
  rw [anc9_update_ne ω c (I.center v.1) x hcenter.symm]
  rw [delLaw9_updAnc_away S E G ω b.1 (I.center v.1) c x hc]

set_option maxHeartbeats 1000000 in
private theorem starValid9_updAnc_away {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (c : I.ID) (x : Fin N)
    (haway : ∀ b : StarOdd9 v, c ∉ I.seen b.1.1) :
    starValid9 S E G (updAnc9 ω c x) v ↔ starValid9 S E G ω v := by
  have hreg :
      starRegular9 S E G (updAnc9 ω c x) v ↔ starRegular9 S E G ω v := by
    unfold starRegular9
    constructor
    · intro h b hb
      let hb' : StarOdd9 v := ⟨b, hb⟩
      have horder : ∀ d ∈ fullOrder9 I v b, d ≠ c := by
        intro d hd heq
        subst d
        exact haway hb' (fullOrder9_mem_seen hb hd)
      have hcore : ∀ d ∈ coreOrder9 I v b, d ≠ c := by
        intro d hd heq
        subst d
        exact haway hb' (coreOrder9_mem_seen hd)
      rcases h b hb with ⟨h₁, h₂, h₃⟩
      refine ⟨?_, ?_, ?_⟩
      · exact (orderRegular9_updAnc_away E G ω
          (maskedLaw9 S (updAnc9 ω c x) b) (maskedLaw9 S ω b)
          (fullOrder9 I v b) c x (maskedLaw9_updAnc S b ω c x) horder).mp h₁
      · exact (orderRegular9_updAnc_away E G ω (siteSecond9 S b.1) (siteSecond9 S b.1)
          (fullOrder9 I v b) c x rfl horder).mp h₂
      · exact (orderRegular9_updAnc_away E G ω (siteSecond9 S b.1) (siteSecond9 S b.1)
          (coreOrder9 I v b) c x rfl hcore).mp h₃
    · intro h b hb
      let hb' : StarOdd9 v := ⟨b, hb⟩
      have horder : ∀ d ∈ fullOrder9 I v b, d ≠ c := by
        intro d hd heq
        subst d
        exact haway hb' (fullOrder9_mem_seen hb hd)
      have hcore : ∀ d ∈ coreOrder9 I v b, d ≠ c := by
        intro d hd heq
        subst d
        exact haway hb' (coreOrder9_mem_seen hd)
      rcases h b hb with ⟨h₁, h₂, h₃⟩
      refine ⟨?_, ?_, ?_⟩
      · exact (orderRegular9_updAnc_away E G ω
          (maskedLaw9 S (updAnc9 ω c x) b) (maskedLaw9 S ω b)
          (fullOrder9 I v b) c x (maskedLaw9_updAnc S b ω c x) horder).mpr h₁
      · exact (orderRegular9_updAnc_away E G ω (siteSecond9 S b.1) (siteSecond9 S b.1)
          (fullOrder9 I v b) c x rfl horder).mpr h₂
      · exact (orderRegular9_updAnc_away E G ω (siteSecond9 S b.1) (siteSecond9 S b.1)
          (coreOrder9 I v b) c x rfl hcore).mpr h₃
  have hgain :
      starGain9 S E G (updAnc9 ω c x) v = starGain9 S E G ω v := by
    unfold starGain9
    apply Finset.sum_congr rfl
    intro b hb
    exact congrArg Real.log (targetFrac9_updAnc_away S E G ω v b c x (haway b))
  unfold starValid9
  exact and_congr hreg (by rw [hgain])

private theorem updAnc9_commute {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (ω : Outcome9 I N) (c d : I.ID) (x y : Fin N) (hcd : c ≠ d) :
    updAnc9 (updAnc9 ω c x) d y = updAnc9 (updAnc9 ω d y) c x := by
  funext z
  by_cases hzc : z = Sum.inl c
  · subst z
    simp [updAnc9, Function.update, hcd]
    rfl
  · by_cases hzd : z = Sum.inl d
    · subst z
      simp [updAnc9, Function.update, hcd, hcd.symm]
      rfl
    · simp [updAnc9, Function.update, hzc, hzd]
  all_goals rfl

set_option maxHeartbeats 1000000 in
private theorem starLik9_updAnc_away {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (c : I.ID) (z y : Fin N)
    (hcz : c ≠ I.center v.1) (haway : ∀ b : StarOdd9 v, c ∉ I.seen b.1.1)
    (ys : StarOdd9 v → Fin N) :
    starLik9 S E G (updAnc9 ω c z) v y ys = starLik9 S E G ω v y ys := by
  have hcommute := updAnc9_commute ω c (I.center v.1) z y hcz
  unfold starLik9
  rw [hcommute]
  have hvalid := starValid9_updAnc_away S E G
    (updAnc9 ω (I.center v.1) y) v c z haway
  have hvalidEq :
      starValid9 S E G (updAnc9 (updAnc9 ω (I.center v.1) y) c z) v =
        starValid9 S E G (updAnc9 ω (I.center v.1) y) v := propext hvalid
  rw [hvalidEq]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  exact congrArg (fun μ : Law N => μ.w (ys b))
    (rowLaw9_updAnc_away S E G (updAnc9 ω (I.center v.1) y) b.1 c z (haway b))

set_option maxHeartbeats 1000000 in
private theorem starMarg9_updAnc_away {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (c : I.ID) (z : Fin N)
    (hcz : c ≠ I.center v.1) (haway : ∀ b : StarOdd9 v, c ∉ I.seen b.1.1)
    (ys : StarOdd9 v → Fin N) :
    starMarg9 S E G (updAnc9 ω c z) v ys = starMarg9 S E G ω v ys := by
  unfold starMarg9
  apply Finset.sum_congr rfl
  intro y hy
  exact congrArg (fun z : ℝ => (siteFirst9 S v.1).w y * z)
    (starLik9_updAnc_away S E G ω v c z y hcz haway ys)

private theorem starRef9_updAnc_away {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (c : I.ID) (z : Fin N)
    (haway : ∀ b : StarOdd9 v, c ∉ I.seen b.1.1)
    (ys : StarOdd9 v → Fin N) :
    starRef9 S E G (updAnc9 ω c z) v ys = starRef9 S E G ω v ys := by
  unfold starRef9
  apply Finset.prod_congr rfl
  intro b hb
  exact congrArg (fun μ : Law N => μ.w (ys b))
    (delLaw9_updAnc_away S E G ω b.1 (I.center v.1) c z (haway b))

private theorem predFail9_updAnc_away {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (c : I.ID) (z : Fin N)
    (hcz : c ≠ I.center v.1) (haway : ∀ b : StarOdd9 v, c ∉ I.seen b.1.1)
    (ys : StarOdd9 v → Fin N) :
    predFail9 S E G (updAnc9 ω c z) v ys = predFail9 S E G ω v ys := by
  unfold predFail9
  rw [starMarg9_updAnc_away S E G ω v c z hcz haway ys,
    starRef9_updAnc_away S E G ω v c z haway ys]

private theorem evenRowAt9_updAnc_away {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (c : I.ID) (z : Fin N)
    (hcz : c ≠ I.center v.1) (haway : ∀ b : StarOdd9 v, c ∉ I.seen b.1.1)
    (ys : StarOdd9 v → Fin N) (y : Fin N) :
    evenRowAt9 S E G (updAnc9 ω c z) v ys y = evenRowAt9 S E G ω v ys y := by
  unfold evenRowAt9
  rw [starLik9_updAnc_away S E G ω v c z y hcz haway ys,
    starMarg9_updAnc_away S E G ω v c z hcz haway ys]

set_option maxHeartbeats 1000000 in
private theorem evenStar9_updAnc_away {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (c : I.ID) (z y : Fin N)
    (hcz : c ≠ I.center v.1) (haway : ∀ b : StarOdd9 v, c ∉ I.seen b.1.1) :
    evenStar9 S E G (updAnc9 ω c z) v y = evenStar9 S E G ω v y := by
  unfold evenStar9
  apply Finset.sum_congr rfl
  intro ys hys
  have hactual : anc9 (updAnc9 ω c z) (I.center v.1) = anc9 ω (I.center v.1) :=
    anc9_update_ne ω c (I.center v.1) z hcz.symm
  rw [hactual]
  rw [starLik9_updAnc_away S E G ω v c z (anc9 ω (I.center v.1)) hcz haway ys]
  rw [predFail9_updAnc_away S E G ω v c z hcz haway ys]
  rw [evenRowAt9_updAnc_away S E G ω v c z hcz haway ys y]

private theorem siteNear9_of_seen_center9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {u v : EvenSites9 n} {b : OddSites9 n}
    (hbv : (cube n).Adj v.1 b.1) (hseen : I.center u.1 ∈ I.seen b.1) :
    siteNear9 P n u.1 v.1 := by
  classical
  change I.center u.1 ∈ seenIDs9 I.center b.1 at hseen
  rcases Finset.mem_image.mp hseen with ⟨w, hw, hcenter⟩
  have hbw : (cube n).Adj b.1 w := (Finset.mem_filter.mp hw).2
  have hwb : _root_.hammingDist w b.1 = 1 := by
    rw [_root_.hammingDist_comm]
    change _
    exact hbw
  have hbv' : _root_.hammingDist b.1 v.1 = 1 := by
    rw [_root_.hammingDist_comm]
    change _
    exact hbv
  have hvw : _root_.hammingDist v.1 w ≤ 2 := by
    calc
      _ ≤ _root_.hammingDist v.1 b.1 + _root_.hammingDist b.1 w :=
        _root_.hammingDist_triangle _ _ _
      _ = _root_.hammingDist b.1 v.1 + _root_.hammingDist w b.1 := by
        rw [_root_.hammingDist_comm v.1 b.1, _root_.hammingDist_comm b.1 w]
      _ = 2 := by rw [hbv', hwb]
  constructor
  · have hslice : specialWord9 (P.m n) u.1 = specialWord9 (P.m n) w := by
      calc
        specialWord9 (P.m n) u.1 = (I.center u.1).slice := (I.center_slice u.1).symm
        _ = (I.center w).slice := by rw [hcenter]
        _ = specialWord9 (P.m n) w := I.center_slice w
    calc
      _ = _root_.hammingDist (specialWord9 (P.m n) w) (specialWord9 (P.m n) v.1) := by
        rw [hslice]
      _ = _root_.hammingDist (specialWord9 (P.m n) v.1) (specialWord9 (P.m n) w) :=
        _root_.hammingDist_comm _ _
      _ ≤ _root_.hammingDist v.1 w :=
        special_hamming_le_full9 (m := P.m n) v.1 w
      _ ≤ 2 := hvw
      _ ≤ 4 := by omega
  · have hloc : (I.center u.1).location = (I.center w).location :=
      congrArg CenterID9.location hcenter.symm
    have hu : _root_.hammingDist (residualWord9 (P.m n) u.1) (I.center u.1).location ≤
        P.radius n := by
      rw [_root_.hammingDist_comm]
      exact I.center_near u.1
    have hw : _root_.hammingDist (I.center u.1).location (residualWord9 (P.m n) w) ≤
        P.radius n := by
      simpa [hloc] using I.center_near w
    have hresuw : _root_.hammingDist (residualWord9 (P.m n) u.1)
        (residualWord9 (P.m n) w) ≤ P.radius n + P.radius n := by
      calc
        _ ≤ _root_.hammingDist (residualWord9 (P.m n) u.1) (I.center u.1).location +
            _root_.hammingDist (I.center u.1).location (residualWord9 (P.m n) w) :=
              _root_.hammingDist_triangle _ _ _
        _ ≤ P.radius n + P.radius n := Nat.add_le_add hu hw
    have hresvw : _root_.hammingDist (residualWord9 (P.m n) v.1)
        (residualWord9 (P.m n) w) ≤ 2 :=
      (residual_hamming_le_full9 (m := P.m n) v.1 w).trans hvw
    have hreswv : _root_.hammingDist (residualWord9 (P.m n) w)
        (residualWord9 (P.m n) v.1) ≤ 2 := by
      rw [_root_.hammingDist_comm]
      exact hresvw
    calc
      _ ≤ _root_.hammingDist (residualWord9 (P.m n) u.1) (residualWord9 (P.m n) w) +
          _root_.hammingDist (residualWord9 (P.m n) w) (residualWord9 (P.m n) v.1) :=
            _root_.hammingDist_triangle _ _ _
      _ ≤ (P.radius n + P.radius n) + 2 := Nat.add_le_add hresuw hreswv
      _ ≤ 4 * P.radius n + 8 := by omega

private theorem targetCenter9_not_seen_of_not_near {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {u v : EvenSites9 n} {b : OddSites9 n}
    (hnot : ¬ siteNear9 P n u.1 v.1) (hbv : (cube n).Adj v.1 b.1) :
    I.center u.1 ∉ I.seen b.1 := by
  intro hseen
  exact hnot (siteNear9_of_seen_center9 hbv hseen)

private theorem center_mem_starScope9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    (v : EvenSites9 n) (hn : 0 < n) :
    Sum.inl (I.center v.1) ∈ starScope9 I v := by
  classical
  let i : Fin n := ⟨0, hn⟩
  let w := cubeFlip v.1 i
  have hwodd : ¬ IsEvenRole w := by
    dsimp [w]
    rw [cubeFlip_parity]
    exact not_not.mpr v.2
  let b : OddSites9 n := ⟨w, hwodd⟩
  have hadj : (cube n).Adj v.1 b.1 := by
    dsimp [b, w]
    exact cubeFlip_adj v.1 i
  unfold starScope9
  apply Finset.mem_biUnion.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, ?_⟩
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨I.center v.1, center_mem_seen9 ⟨b, hadj⟩, rfl⟩

private theorem separated_pair_not_near9 {P : Params9} {n k : ℕ}
    (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1)
    {i j : Fin k} (hne : i ≠ j) : ¬ siteNear9 P n (a i).1 (a j).1 := by
  by_cases hji : j < i
  · exact hsep i j hji
  · have hij : i < j := by omega
    intro hnear
    exact hsep j i hij (siteNear9_symm (P := P) (n := n) (a i).1 (a j).1 hnear)

private theorem otherTarget9_not_seen {P : Params9} {n k : ℕ}
    {I : IDMap9 P n} (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1)
    {i j : Fin k} (hne : i ≠ j) (b : StarOdd9 (a i)) :
    I.center (a j).1 ∉ I.seen b.1.1 :=
  targetCenter9_not_seen_of_not_near (u := a j) (v := a i)
    (separated_pair_not_near9 a hsep (i := j) (j := i) hne.symm) b.2

private noncomputable def targetAnchorVars9 {P : Params9} {n k : ℕ} {I : IDMap9 P n}
    (a : Fin k → EvenSites9 n) : Finset (I.ID ⊕ OddSites9 n) :=
  Finset.univ.image (fun i : Fin k => Sum.inl (I.center (a i).1))

private noncomputable def targetAnchorEquiv9 {P : Params9} {n k : ℕ} {I : IDMap9 P n}
    (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1) :
    Fin k ≃ targetAnchorVars9 (I := I) a := by
  classical
  let f : Fin k → targetAnchorVars9 (I := I) a := fun i =>
    ⟨Sum.inl (I.center (a i).1), Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply targetCenters_injective9 a hsep
    exact Sum.inl.inj (congrArg Subtype.val hij)
  have hsurj : Function.Surjective f := by
    intro q
    rcases Finset.mem_image.mp q.2 with ⟨i, hi, hqi⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hqi
  exact Equiv.ofBijective f ⟨hf, hsurj⟩

private theorem targetAnchorEquiv9_apply {P : Params9} {n k : ℕ} {I : IDMap9 P n}
    (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1)
    (i : Fin k) (hq : (Sum.inl (I.center (a i).1) : I.ID ⊕ OddSites9 n) ∈
      targetAnchorVars9 a) :
    targetAnchorEquiv9 (I := I) a hsep i =
      ⟨Sum.inl (I.center (a i).1), hq⟩ := by
  apply Subtype.ext
  rfl

private noncomputable def targetAssignmentEquiv9 {P : Params9} {n k N : ℕ}
    {I : IDMap9 P n} (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1) :
    (∀ q : targetAnchorVars9 (I := I) a, Val9 I N q.1) ≃ (Fin k → Fin N) := by
  classical
  let e : Fin k ≃ targetAnchorVars9 (I := I) a := targetAnchorEquiv9 (I := I) a hsep
  exact (Equiv.piCongrLeft (fun q : targetAnchorVars9 (I := I) a => Val9 I N q.1) e).symm.trans
    (Equiv.piCongrRight fun _ => Equiv.refl (Fin N))

private theorem targetAssignmentEquiv9_apply {P : Params9} {n k N : ℕ}
    {I : IDMap9 P n} (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1)
    (s : ∀ q : targetAnchorVars9 a, Val9 I N q.1) (i : Fin k) :
    targetAssignmentEquiv9 a hsep s i = s (targetAnchorEquiv9 a hsep i) := by
  simp [targetAssignmentEquiv9, Equiv.piCongrRight, Equiv.piCongrLeft,
    Equiv.piCongrLeft']
  rfl

private theorem targetAssignmentEquiv9_center {P : Params9} {n k N : ℕ}
    {I : IDMap9 P n} (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1)
    (s : ∀ q : targetAnchorVars9 (I := I) a, Val9 I N q.1) (i : Fin k)
    (hq : (Sum.inl (I.center (a i).1) : I.ID ⊕ OddSites9 n) ∈ targetAnchorVars9 a) :
    targetAssignmentEquiv9 a hsep s i =
      s ⟨Sum.inl (I.center (a i).1), hq⟩ := by
  rw [targetAssignmentEquiv9_apply (I := I) a hsep s i]
  have heq : targetAnchorEquiv9 (I := I) a hsep i =
      ⟨Sum.inl (I.center (a i).1), hq⟩ := by
    apply Subtype.ext
    rfl
  change (s (targetAnchorEquiv9 (I := I) a hsep i) : Fin N) =
    (s ⟨Sum.inl (I.center (a i).1), hq⟩ : Fin N)
  cases heq
  rfl

private theorem targetAnchor_badCount9 {P : Params9} {n k N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (a : Fin k → EvenSites9 n) (hn : 0 < n)
    (hscope : StarScopeFacts9 S I E G) :
    (Finset.univ.filter fun v : EvenSites9 n =>
      ¬ Disjoint (starScope9 I v) (targetAnchorVars9 a)).card ≤
        k * (lllDegree9 P n + 1) := by
  classical
  let D : Fin k → Finset (EvenSites9 n) := fun i =>
    insert (a i) (Finset.univ.filter fun v' : EvenSites9 n =>
      v' ≠ a i ∧ ¬ Disjoint (starScope9 I (a i)) (starScope9 I v'))
  let T : Finset (EvenSites9 n) := Finset.univ.filter fun v =>
      ¬ Disjoint (starScope9 I v) (targetAnchorVars9 a)
  have hsubset : T ⊆ Finset.univ.biUnion D := by
    intro v hv
    have hnot : ¬ Disjoint (starScope9 I v) (targetAnchorVars9 a) :=
      (Finset.mem_filter.mp hv).2
    rcases Finset.not_disjoint_iff.mp hnot with ⟨q, hqv, hqU⟩
    rcases Finset.mem_image.mp hqU with ⟨i, hi, hqi⟩
    have hqiScope : Sum.inl (I.center (a i).1) ∈ starScope9 I v := by
      rw [hqi]
      exact hqv
    have hcenterScope : Sum.inl (I.center (a i).1) ∈ starScope9 I (a i) :=
      center_mem_starScope9 (a i) hn
    have hvD : v ∈ D i := by
      by_cases hsame : v = a i
      · simp [D, hsame]
      · have hnot' : ¬ Disjoint (starScope9 I (a i)) (starScope9 I v) :=
          Finset.not_disjoint_iff.mpr ⟨Sum.inl (I.center (a i).1), hcenterScope, hqiScope⟩
        simp [D, hsame, hnot']
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hvD⟩
  have hcardD (i : Fin k) : (D i).card ≤ lllDegree9 P n + 1 := by
    have hdegree := hscope.2 (a i)
    have hnot : (a i) ∉ Finset.univ.filter (fun v' : EvenSites9 n =>
        v' ≠ a i ∧ ¬ Disjoint (starScope9 I (a i)) (starScope9 I v')) := by
      simp
    change (insert (a i) (Finset.univ.filter (fun v' : EvenSites9 n =>
      v' ≠ a i ∧ ¬ Disjoint (starScope9 I (a i)) (starScope9 I v')))).card ≤
        lllDegree9 P n + 1
    rw [Finset.card_insert_of_notMem hnot]
    exact Nat.add_le_add_right hdegree 1
  calc
    T.card ≤ (Finset.univ.biUnion D).card := Finset.card_le_card hsubset
    _ ≤ ∑ i : Fin k, (D i).card := by
      simpa using (Finset.card_biUnion_le (s := Finset.univ) (t := D))
    _ ≤ ∑ i : Fin k, (lllDegree9 P n + 1) :=
      Finset.sum_le_sum fun i hi => hcardD i
    _ = k * (lllDegree9 P n + 1) := by simp

set_option maxHeartbeats 1000000 in
private theorem tail_degree_small9 (P : Params9) (hP : P.Valid) (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      P.tail c n * ((lllDegree9 P n : ℝ) + 1) ≤ 1 / 4 := by
  classical
  have hexps : ScaleExps9 P := scaleExps9_of_valid9 P hP
  rcases hexps with ⟨heps, hepsσ, hu, hσu, _⟩
  let σ : ℝ := P.σ
  let gap : ℝ := P.u - σ
  have hσpos : 0 < σ := by dsimp [σ]; linarith [heps, hepsσ]
  have hσle : 0 ≤ σ := hσpos.le
  have hgap : 0 < gap := by dsimp [gap, σ]; linarith
  have huOne : P.u < 1 := by
    have hxSxd : P.xS < P.xD := hP.1.2.1
    have hxd : P.xD < 1 / 10 := hP.1.2.2
    have hxSReal : (P.xS : ℝ) < 1 / 10 := by
      have hxSxdR : (P.xS : ℝ) < (P.xD : ℝ) := by exact_mod_cast hxSxd
      have hxdR : (P.xD : ℝ) < (1 / 10 : ℝ) := by
        simpa using (Rat.cast_lt (K := ℝ)).2 hxd
      linarith
    simp [Params9.u]
    linarith
  let C : ℝ := c / 100
  have hC : 0 < C := by dsimp [C]; positivity
  have hlogLittle := isLittleO_log_rpow_atTop hgap
  have hlogEvent : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.log x‖ ≤ C * ‖x ^ gap‖ :=
    (Asymptotics.isLittleO_iff.mp hlogLittle) hC
  have hlogNat : ∀ᶠ m : ℕ in Filter.atTop,
      ‖Real.log (m : ℝ)‖ ≤ C * ‖(m : ℝ) ^ gap‖ :=
    tendsto_natCast_atTop_atTop.eventually hlogEvent
  rcases Filter.eventually_atTop.1 hlogNat with ⟨n₁, hn₁⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let Q : ℝ := max (10 * Real.log 2 / c) (2 * Real.log 4 / c)
  have hQ : 0 < Q := by
    dsimp [Q]
    exact lt_of_lt_of_le (div_pos (mul_pos (by norm_num) hlog2) hc)
      (le_max_left _ _)
  have hrpow := (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  have hpowEvent : ∀ᶠ n : ℕ in Filter.atTop, Q ≤ (n : ℝ) ^ P.u :=
    hrpow.eventually (Filter.eventually_atTop.2 ⟨Q, fun _ h => h⟩)
  rcases Filter.eventually_atTop.1 hpowEvent with ⟨n₂, hn₂⟩
  refine ⟨max n₁ (max n₂ 1), ?_⟩
  intro n hn
  have hn₁' : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hinner : max n₂ 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : n₂ ≤ n := le_trans (le_max_left _ _) hinner
  have hnOne : 1 ≤ n := le_trans (le_max_right _ _) hinner
  have hncast : 1 ≤ (n : ℝ) := by exact_mod_cast hnOne
  have hpower : Q ≤ (n : ℝ) ^ P.u := hn₂ n hn2
  have hlogNat' := hn₁ (n + 1) (by omega)
  have hlognonneg : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by nlinarith [hncast])
  have hpowgapNonneg : 0 ≤ ((n : ℝ) + 1) ^ gap := by positivity
  have hlog : Real.log ((n : ℝ) + 1) ≤ C * ((n : ℝ) + 1) ^ gap := by
    have hlog' : ‖Real.log ((n : ℝ) + 1)‖ ≤ C * ‖((n : ℝ) + 1) ^ gap‖ := by
      simpa using hlogNat'
    simpa [Real.norm_eq_abs, abs_of_nonneg hlognonneg, abs_of_nonneg hpowgapNonneg] using hlog'
  have hradius : (P.radius n : ℝ) ≤ (n : ℝ) ^ σ := by
    dsimp [Params9.radius]
    exact Nat.floor_le (by positivity)
  have hnplus : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by nlinarith [hncast]
  have hradius' : (P.radius n : ℝ) ≤ ((n : ℝ) + 1) ^ σ :=
    hradius.trans (Real.rpow_le_rpow (by positivity) (by linarith) hσle)
  have hpowσOne : 1 ≤ ((n : ℝ) + 1) ^ σ :=
    Real.one_le_rpow (by linarith) hσle
  have hcoeff : 2 * (P.radius n : ℝ) + 8 ≤ 10 * ((n : ℝ) + 1) ^ σ := by
    nlinarith [hradius', hpowσOne]
  have hterm : (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
      (c / 5) * (n : ℝ) ^ P.u := by
    have hmul := mul_le_mul hcoeff hlog hlognonneg (by positivity)
    calc
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
          (10 * ((n : ℝ) + 1) ^ σ) * (C * ((n : ℝ) + 1) ^ gap) := hmul
      _ = 10 * C * (((n : ℝ) + 1) ^ σ * ((n : ℝ) + 1) ^ gap) := by ring
      _ = 10 * C * ((n : ℝ) + 1) ^ (σ + gap) := by
        rw [← Real.rpow_add (by positivity)]
      _ = 10 * C * ((n : ℝ) + 1) ^ P.u := by simp [gap, σ]
        _ ≤ (20 * C) * (n : ℝ) ^ P.u := by
        have hpn := Real.rpow_le_rpow (by positivity) hnplus (le_of_lt hu)
        calc
          10 * C * ((n : ℝ) + 1) ^ P.u ≤ 10 * C * (2 * (n : ℝ)) ^ P.u :=
            mul_le_mul_of_nonneg_left hpn (by positivity)
          _ = 10 * C * ((2 : ℝ) ^ P.u * (n : ℝ) ^ P.u) := by
            rw [Real.mul_rpow (by norm_num) (by positivity)]
          _ ≤ (20 * C) * (n : ℝ) ^ P.u := by
            have htwo : (2 : ℝ) ^ P.u ≤ 2 := by
              calc
                (2 : ℝ) ^ P.u ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) huOne.le
                _ = 2 := by norm_num
            have hpowMul : (2 : ℝ) ^ P.u * (n : ℝ) ^ P.u ≤
                2 * (n : ℝ) ^ P.u :=
              mul_le_mul_of_nonneg_right htwo (by positivity)
            calc
              10 * C * ((2 : ℝ) ^ P.u * (n : ℝ) ^ P.u) ≤
                  10 * C * (2 * (n : ℝ) ^ P.u) :=
                    mul_le_mul_of_nonneg_left hpowMul (by positivity)
              _ = (20 * C) * (n : ℝ) ^ P.u := by ring
      _ = (c / 5) * (n : ℝ) ^ P.u := by ring
  have hlogA : Real.log ((lllDegree9 P n : ℝ) + 1) ≤
      (c / 2) * (n : ℝ) ^ P.u := by
    have hdegreePos : 0 < lllDegree9 P n := by
      unfold lllDegree9
      positivity
    have hdegreeOne : 1 ≤ lllDegree9 P n := by omega
    have hApos : 0 < (lllDegree9 P n : ℝ) + 1 := by positivity
    have hDOne : 1 ≤ (lllDegree9 P n : ℝ) := by exact_mod_cast hdegreeOne
    have hA : (lllDegree9 P n : ℝ) + 1 ≤ 2 * (lllDegree9 P n : ℝ) := by nlinarith [hDOne]
    have hlogD : Real.log (lllDegree9 P n : ℝ) =
        ((2 * P.radius n + 8 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) := by
      simp [lllDegree9, Real.log_pow]
    calc
      Real.log ((lllDegree9 P n : ℝ) + 1) ≤ Real.log (2 * (lllDegree9 P n : ℝ)) :=
        Real.log_le_log hApos (by nlinarith)
      _ = Real.log 2 + Real.log (lllDegree9 P n : ℝ) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
      _ ≤ Real.log 2 + (c / 5) * (n : ℝ) ^ P.u := by
        rw [hlogD]
        push_cast
        linarith [hterm]
      _ ≤ (c / 10) * (n : ℝ) ^ P.u + (c / 5) * (n : ℝ) ^ P.u := by
        have hlog2le : Real.log 2 ≤ (c / 10) * (n : ℝ) ^ P.u := by
          have hqle : 10 * Real.log 2 / c ≤ (n : ℝ) ^ P.u :=
            le_trans (le_max_left _ _) hpower
          have hqle' : 10 * Real.log 2 ≤ c * (n : ℝ) ^ P.u :=
            by simpa [mul_comm] using (div_le_iff₀ hc).1 hqle
          nlinarith [hqle']
        linarith [hlog2le]
      _ ≤ (c / 2) * (n : ℝ) ^ P.u := by nlinarith
  have hApos : 0 < (lllDegree9 P n : ℝ) + 1 := by positivity
  have htailEq : P.tail c n * ((lllDegree9 P n : ℝ) + 1) =
      Real.exp (-(c * (n : ℝ) ^ P.u) + Real.log ((lllDegree9 P n : ℝ) + 1)) := by
    rw [Params9.tail]
    calc
      Real.exp (-(c * (n : ℝ) ^ P.u)) * ((lllDegree9 P n : ℝ) + 1) =
          Real.exp (-(c * (n : ℝ) ^ P.u)) *
            Real.exp (Real.log ((lllDegree9 P n : ℝ) + 1)) := by rw [Real.exp_log hApos]
      _ = Real.exp (-(c * (n : ℝ) ^ P.u) + Real.log ((lllDegree9 P n : ℝ) + 1)) := by
        rw [Real.exp_add]
  have hlog4le : Real.log 4 ≤ (c / 2) * (n : ℝ) ^ P.u := by
    have hqle : 2 * Real.log 4 / c ≤ (n : ℝ) ^ P.u :=
      le_trans (le_max_right _ _) hpower
    have hqle' : 2 * Real.log 4 ≤ c * (n : ℝ) ^ P.u :=
      by simpa [mul_comm] using (div_le_iff₀ hc).1 hqle
    nlinarith [hqle']
  calc
    P.tail c n * ((lllDegree9 P n : ℝ) + 1) =
        Real.exp (-(c * (n : ℝ) ^ P.u) + Real.log ((lllDegree9 P n : ℝ) + 1)) := htailEq
    _ ≤ Real.exp (-(c / 2) * (n : ℝ) ^ P.u) :=
      Real.exp_le_exp.mpr (by nlinarith [hlogA])
    _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by linarith [hlog4le])
    _ = 1 / 4 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      norm_num

private theorem condPenalty9 {x : ℝ} {d k t : ℕ}
    (hx : 0 ≤ x) (hsmall : x * ((d + 1 : ℕ) : ℝ) ≤ 1 / 4)
    (ht : t ≤ k * (d + 1)) :
    ((1 - x) ^ t)⁻¹ ≤ (2 : ℝ) ^ k := by
  have hdOne : 1 ≤ d + 1 := by omega
  have hdOneR : 1 ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hdOne
  have hxquarter : x ≤ 1 / 4 := by nlinarith [hx, hdOneR, hsmall]
  have hden : 0 < 1 - x := by linarith
  have hinvPos : 0 < (1 - x)⁻¹ := inv_pos.mpr hden
  have hlogInv : Real.log ((1 - x)⁻¹) ≤ 2 * x := by
    have hlog := Real.log_le_sub_one_of_pos hinvPos
    calc
      Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 := hlog
      _ = x / (1 - x) := by field_simp [ne_of_gt hden]; ring
      _ ≤ 2 * x := by
        apply (div_le_iff₀ hden).2
        have hprod : 0 ≤ x * (1 - 2 * x) :=
          mul_nonneg hx (by linarith [hxquarter])
        nlinarith [hprod]
  have hlogBase : -Real.log (1 - x) ≤ 2 * x := by
    simpa [Real.log_inv] using hlogInv
  have hTcast : (t : ℝ) ≤ ((k * (d + 1) : ℕ) : ℝ) := by exact_mod_cast ht
  have hsmallCast : x * ((d + 1 : ℕ) : ℝ) ≤ 1 / 4 := hsmall
  have hTx : (t : ℝ) * x ≤ (k : ℝ) / 4 := by
    calc
      (t : ℝ) * x ≤ ((k * (d + 1) : ℕ) : ℝ) * x :=
        mul_le_mul_of_nonneg_right hTcast hx
      _ = (k : ℝ) * (x * ((d + 1 : ℕ) : ℝ)) := by push_cast; ring
      _ ≤ (k : ℝ) * (1 / 4) := mul_le_mul_of_nonneg_left hsmallCast (by positivity)
      _ = (k : ℝ) / 4 := by ring
  have hpowPos : 0 < (1 - x) ^ t := pow_pos hden t
  have hfactor : ((1 - x) ^ t)⁻¹ =
      Real.exp ((t : ℝ) * (-Real.log (1 - x))) := by
    calc
      ((1 - x) ^ t)⁻¹ = Real.exp (-Real.log ((1 - x) ^ t)) := by
        rw [Real.exp_neg, Real.exp_log hpowPos]
      _ = Real.exp ((t : ℝ) * (-Real.log (1 - x))) := by
        rw [Real.log_pow]
        congr 1
        ring
  have hExpBound : (t : ℝ) * (-Real.log (1 - x)) ≤ (k : ℝ) / 2 := by
    calc
      (t : ℝ) * (-Real.log (1 - x)) ≤ (t : ℝ) * (2 * x) :=
        mul_le_mul_of_nonneg_left hlogBase (by positivity)
      _ = 2 * ((t : ℝ) * x) := by ring
      _ ≤ (k : ℝ) / 2 := by nlinarith [hTx]
  have hlog2lower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [hhalf, Real.log_inv] at hlog
    linarith
  have hkNonneg : 0 ≤ (k : ℝ) := by positivity
  have hExp : (t : ℝ) * (-Real.log (1 - x)) ≤
      (k : ℝ) * Real.log 2 := by
    calc
      (t : ℝ) * (-Real.log (1 - x)) ≤ (k : ℝ) / 2 := hExpBound
      _ ≤ (k : ℝ) * Real.log 2 := by nlinarith [hlog2lower, hkNonneg]
  have hpow : Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
    have hlogpow : Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := by rw [Real.log_pow]
    rw [← hlogpow, Real.exp_log (by positivity)]
  calc
    ((1 - x) ^ t)⁻¹ = Real.exp ((t : ℝ) * (-Real.log (1 - x))) := hfactor
    _ ≤ Real.exp ((k : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hExp
    _ = (2 : ℝ) ^ k := hpow

private theorem independentTargetStars9 {P : Params9} {n k N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (a : Fin k → EvenSites9 n) (x : Fin N) (ω : Outcome9 I N)
    (hcancel : StarCancel9 S I E G) :
    ∑ f : Fin k → Fin N, ∏ i : Fin k,
      (siteFirst9 S (a i).1).w (f i) *
        evenStar9 S E G (updAnc9 ω (I.center (a i).1) (f i)) (a i) x ≤
    ∏ i : Fin k, (N : ℝ) * (siteFirst9 S (a i).1).w x := by
  classical
  rw [← Fintype.prod_sum (κ := fun _ : Fin k => Fin N)
    (f := fun i y => (siteFirst9 S (a i).1).w y *
      evenStar9 S E G (updAnc9 ω (I.center (a i).1) y) (a i) x)]
  apply Finset.prod_le_prod₀
  · intro i hi
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg ((siteFirst9 S (a i).1).nonneg y) (evenStar9_nonneg S E G
      (updAnc9 ω (I.center (a i).1) y) (a i) x)
  · intro i hi
    exact hcancel ω (a i) x

private theorem hitSet9_eq_of_anchorAgree {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (ids : Finset I.ID)
    (hanc : ∀ c ∈ ids, anc9 ω c = anc9 ω' c) :
    hitSet9 E G ω ids = hitSet9 E G ω' ids := by
  classical
  ext y
  simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hy d hd
    have hval := hy d hd
    rw [hanc d hd] at hval
    exact hval
  · intro hy d hd
    have hval := hy d hd
    rw [← hanc d hd] at hval
    exact hval

private theorem maskedLaw9_eq_of_maskAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (ω ω' : Outcome9 I N)
    (b : OddSites9 n) (hmask : msk9 ω b = msk9 ω' b) :
    maskedLaw9 S ω b = maskedLaw9 S ω' b := by
  unfold maskedLaw9
  rw [hmask]

private theorem rowLaw9_eq_of_localAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (b : OddSites9 n)
    (hanc : ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c)
    (hmask : msk9 ω b = msk9 ω' b) : rowLaw9 S E G ω b = rowLaw9 S E G ω' b := by
  unfold rowLaw9
  rw [maskedLaw9_eq_of_maskAgree S ω ω' b hmask]
  rw [hitSet9_eq_of_anchorAgree E G ω ω' (I.seen b.1) hanc]

private theorem delLaw9_eq_of_localAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (b : OddSites9 n) (t : I.ID)
    (hanc : ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c)
    (hmask : msk9 ω b = msk9 ω' b) :
    delLaw9 S E G ω b t = delLaw9 S E G ω' b t := by
  unfold delLaw9
  rw [maskedLaw9_eq_of_maskAgree S ω ω' b hmask]
  apply congrArg (restrictOr9 (maskedLaw9 S ω' b))
  apply hitSet9_eq_of_anchorAgree E G ω ω' ((I.seen b.1).erase t)
  intro c hc
  exact hanc c (Finset.mem_of_mem_erase hc)

private theorem prefixLaw9_eq_of_orderAgree {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (base base' : Law N) (order : List I.ID) (k : ℕ)
    (hbase : base = base') (hanc : ∀ c ∈ order, anc9 ω c = anc9 ω' c) :
    prefixLaw9 E G ω base order k = prefixLaw9 E G ω' base' order k := by
  unfold prefixLaw9
  rw [hbase]
  congr 1
  apply hitSet9_eq_of_anchorAgree E G ω ω' (order.take k).toFinset
  intro c hc
  apply hanc c
  exact List.Sublist.subset (List.take_sublist k order) (List.mem_toFinset.mp hc)

private theorem orderRegular9_eq_of_orderAgree {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (base base' : Law N) (order : List I.ID)
    (hbase : base = base') (hanc : ∀ c ∈ order, anc9 ω c = anc9 ω' c) :
    orderRegular9 E G ω base order ↔ orderRegular9 E G ω' base' order := by
  have hprefix (k : ℕ) :
      prefixLaw9 E G ω base order k = prefixLaw9 E G ω' base' order k :=
    prefixLaw9_eq_of_orderAgree E G ω ω' base base' order k hbase hanc
  constructor
  · intro h k d hk hprev
    have hd : d ∈ order := List.mem_of_getElem? hk
    have hprev' : ∀ j d', j < k → order[j]? = some d' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω d') (prefixLaw9 E G ω base order j) := by
      intro j d' hj hj'
      have hd' : d' ∈ order := List.mem_of_getElem? hj'
      simpa [hanc d' hd', hprefix j] using hprev j d' hj hj'
    have hval := h k d hk hprev'
    simpa [hanc d hd, hprefix k] using hval
  · intro h k d hk hprev
    have hd : d ∈ order := List.mem_of_getElem? hk
    have hprev' : ∀ j d', j < k → order[j]? = some d' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω' d') (prefixLaw9 E G ω' base' order j) := by
      intro j d' hj hj'
      have hd' : d' ∈ order := List.mem_of_getElem? hj'
      simpa [hanc d' hd', hprefix j] using hprev j d' hj hj'
    have hval := h k d hk hprev'
    simpa [hanc d hd, hprefix k] using hval

private theorem targetFrac9_eq_of_localAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (v : EvenSites9 n) (b : StarOdd9 v)
    (hanc : ∀ c ∈ I.seen b.1.1, anc9 ω c = anc9 ω' c)
    (hmask : msk9 ω b.1 = msk9 ω' b.1) :
    targetFrac9 S E G ω v b.1 = targetFrac9 S E G ω' v b.1 := by
  have hcenter := hanc (I.center v.1) (center_mem_seen9 b)
  have hdel := delLaw9_eq_of_localAgree S E G ω ω' b.1 (I.center v.1) hanc hmask
  unfold targetFrac9
  rw [hcenter, hdel]

private theorem starValid9_eq_of_localAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (v : EvenSites9 n)
    (hanc : ∀ b : StarOdd9 v, ∀ c ∈ I.seen b.1.1, anc9 ω c = anc9 ω' c)
    (hmask : ∀ b : StarOdd9 v, msk9 ω b.1 = msk9 ω' b.1) :
    starValid9 S E G ω v = starValid9 S E G ω' v := by
  have hreg : starRegular9 S E G ω v ↔ starRegular9 S E G ω' v := by
    unfold starRegular9
    constructor
    · intro h b hb
      let sb : StarOdd9 v := ⟨b, hb⟩
      have horder : ∀ d ∈ fullOrder9 I v b, anc9 ω d = anc9 ω' d := by
        intro d hd
        exact hanc sb d (fullOrder9_mem_seen hb hd)
      have hcore : ∀ d ∈ coreOrder9 I v b, anc9 ω d = anc9 ω' d := by
        intro d hd
        exact hanc sb d (coreOrder9_mem_seen hd)
      rcases h b hb with ⟨h₁, h₂, h₃⟩
      refine ⟨?_, ?_, ?_⟩
      · exact (orderRegular9_eq_of_orderAgree E G ω ω'
          (maskedLaw9 S ω b) (maskedLaw9 S ω' b) (fullOrder9 I v b)
          (maskedLaw9_eq_of_maskAgree S ω ω' b (hmask sb)) horder).mp h₁
      · exact (orderRegular9_eq_of_orderAgree E G ω ω'
          (siteSecond9 S b.1) (siteSecond9 S b.1) (fullOrder9 I v b) rfl horder).mp h₂
      · exact (orderRegular9_eq_of_orderAgree E G ω ω'
          (siteSecond9 S b.1) (siteSecond9 S b.1) (coreOrder9 I v b) rfl hcore).mp h₃
    · intro h b hb
      let sb : StarOdd9 v := ⟨b, hb⟩
      have horder : ∀ d ∈ fullOrder9 I v b, anc9 ω d = anc9 ω' d := by
        intro d hd
        exact hanc sb d (fullOrder9_mem_seen hb hd)
      have hcore : ∀ d ∈ coreOrder9 I v b, anc9 ω d = anc9 ω' d := by
        intro d hd
        exact hanc sb d (coreOrder9_mem_seen hd)
      rcases h b hb with ⟨h₁, h₂, h₃⟩
      refine ⟨?_, ?_, ?_⟩
      · exact (orderRegular9_eq_of_orderAgree E G ω ω'
          (maskedLaw9 S ω b) (maskedLaw9 S ω' b) (fullOrder9 I v b)
          (maskedLaw9_eq_of_maskAgree S ω ω' b (hmask sb)) horder).mpr h₁
      · exact (orderRegular9_eq_of_orderAgree E G ω ω'
          (siteSecond9 S b.1) (siteSecond9 S b.1) (fullOrder9 I v b) rfl horder).mpr h₂
      · exact (orderRegular9_eq_of_orderAgree E G ω ω'
          (siteSecond9 S b.1) (siteSecond9 S b.1) (coreOrder9 I v b) rfl hcore).mpr h₃
  have hgain : starGain9 S E G ω v = starGain9 S E G ω' v := by
    unfold starGain9
    apply Finset.sum_congr rfl
    intro b hb
    exact congrArg Real.log (targetFrac9_eq_of_localAgree S E G ω ω' v b (hanc b) (hmask b))
  unfold starValid9
  exact propext (and_congr hreg (by rw [hgain]))

private theorem starLik9_eq_of_localAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (v : EvenSites9 n) (y : Fin N)
    (hanc : ∀ b : StarOdd9 v, ∀ d ∈ I.seen b.1.1, anc9 ω d = anc9 ω' d)
    (hmask : ∀ b : StarOdd9 v, msk9 ω b.1 = msk9 ω' b.1)
    (ys : StarOdd9 v → Fin N) :
    starLik9 S E G ω v y ys = starLik9 S E G ω' v y ys := by
  have hanc' : ∀ b : StarOdd9 v, ∀ d ∈ I.seen b.1.1,
      anc9 (updAnc9 ω (I.center v.1) y) d =
        anc9 (updAnc9 ω' (I.center v.1) y) d := by
    intro b d hd
    by_cases hdc : d = I.center v.1
    · subst d
      simp [anc9, updAnc9, Function.update]
    · rw [anc9_update_ne ω (I.center v.1) d y hdc,
        anc9_update_ne ω' (I.center v.1) d y hdc]
      exact hanc b d hd
  have hmask' : ∀ b : StarOdd9 v,
      msk9 (updAnc9 ω (I.center v.1) y) b.1 =
        msk9 (updAnc9 ω' (I.center v.1) y) b.1 := by
    intro b
    have h₁ : msk9 (updAnc9 ω (I.center v.1) y) b.1 = msk9 ω b.1 := by
      unfold msk9 updAnc9
      have hne : (Sum.inr b.1 : I.ID ⊕ OddSites9 n) ≠ Sum.inl (I.center v.1) := by simp
      rw [Function.update_of_ne hne]
    have h₂ : msk9 (updAnc9 ω' (I.center v.1) y) b.1 = msk9 ω' b.1 := by
      unfold msk9 updAnc9
      have hne : (Sum.inr b.1 : I.ID ⊕ OddSites9 n) ≠ Sum.inl (I.center v.1) := by simp
      rw [Function.update_of_ne hne]
    exact h₁.trans ((hmask b).trans h₂.symm)
  have hvalid : starValid9 S E G (updAnc9 ω (I.center v.1) y) v =
      starValid9 S E G (updAnc9 ω' (I.center v.1) y) v :=
    starValid9_eq_of_localAgree S E G (updAnc9 ω (I.center v.1) y)
      (updAnc9 ω' (I.center v.1) y) v hanc' hmask'
  unfold starLik9
  rw [hvalid]
  congr 1
  apply Finset.prod_congr rfl
  intro b hb
  exact congrArg (fun μ : Law N => μ.w (ys b))
    (rowLaw9_eq_of_localAgree S E G (updAnc9 ω (I.center v.1) y)
      (updAnc9 ω' (I.center v.1) y) b.1 (hanc' b) (hmask' b))

private theorem starMarg9_eq_of_localAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (v : EvenSites9 n)
    (hanc : ∀ b : StarOdd9 v, ∀ d ∈ I.seen b.1.1, anc9 ω d = anc9 ω' d)
    (hmask : ∀ b : StarOdd9 v, msk9 ω b.1 = msk9 ω' b.1)
    (ys : StarOdd9 v → Fin N) :
    starMarg9 S E G ω v ys = starMarg9 S E G ω' v ys := by
  unfold starMarg9
  apply Finset.sum_congr rfl
  intro y hy
  exact congrArg (fun z : ℝ => (siteFirst9 S v.1).w y * z)
    (starLik9_eq_of_localAgree S E G ω ω' v y hanc hmask ys)

private theorem starRef9_eq_of_localAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (v : EvenSites9 n)
    (hanc : ∀ b : StarOdd9 v, ∀ d ∈ I.seen b.1.1, anc9 ω d = anc9 ω' d)
    (hmask : ∀ b : StarOdd9 v, msk9 ω b.1 = msk9 ω' b.1)
    (ys : StarOdd9 v → Fin N) :
    starRef9 S E G ω v ys = starRef9 S E G ω' v ys := by
  unfold starRef9
  apply Finset.prod_congr rfl
  intro b hb
  exact congrArg (fun μ : Law N => μ.w (ys b))
    (delLaw9_eq_of_localAgree S E G ω ω' b.1 (I.center v.1) (hanc b) (hmask b))

private theorem predFail9_eq_of_localAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (v : EvenSites9 n)
    (hanc : ∀ b : StarOdd9 v, ∀ d ∈ I.seen b.1.1, anc9 ω d = anc9 ω' d)
    (hmask : ∀ b : StarOdd9 v, msk9 ω b.1 = msk9 ω' b.1)
    (ys : StarOdd9 v → Fin N) : predFail9 S E G ω v ys = predFail9 S E G ω' v ys := by
  unfold predFail9
  rw [starMarg9_eq_of_localAgree S E G ω ω' v hanc hmask ys,
    starRef9_eq_of_localAgree S E G ω ω' v hanc hmask ys]

private theorem evenRowAt9_eq_of_localAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (v : EvenSites9 n)
    (hanc : ∀ b : StarOdd9 v, ∀ d ∈ I.seen b.1.1, anc9 ω d = anc9 ω' d)
    (hmask : ∀ b : StarOdd9 v, msk9 ω b.1 = msk9 ω' b.1)
    (ys : StarOdd9 v → Fin N) (y : Fin N) :
    evenRowAt9 S E G ω v ys y = evenRowAt9 S E G ω' v ys y := by
  unfold evenRowAt9
  rw [starLik9_eq_of_localAgree S E G ω ω' v y hanc hmask ys,
    starMarg9_eq_of_localAgree S E G ω ω' v hanc hmask ys]

private theorem evenStar9_eq_of_localAgree {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω ω' : Outcome9 I N) (v : EvenSites9 n) (x : Fin N)
    (hcenter : anc9 ω (I.center v.1) = anc9 ω' (I.center v.1))
    (hanc : ∀ b : StarOdd9 v, ∀ d ∈ I.seen b.1.1, anc9 ω d = anc9 ω' d)
    (hmask : ∀ b : StarOdd9 v, msk9 ω b.1 = msk9 ω' b.1) :
    evenStar9 S E G ω v x = evenStar9 S E G ω' v x := by
  unfold evenStar9
  apply Finset.sum_congr rfl
  intro ys hys
  rw [← hcenter]
  rw [starLik9_eq_of_localAgree S E G ω ω' v (anc9 ω (I.center v.1)) hanc hmask ys]
  rw [predFail9_eq_of_localAgree S E G ω ω' v hanc hmask ys]
  rw [evenRowAt9_eq_of_localAgree S E G ω ω' v hanc hmask ys x]

private theorem glueStarLocalAgree9 {P : Params9} {n k N : ℕ}
    {I : IDMap9 P n} (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1)
    (ω : Outcome9 I N) (s : ∀ q : targetAnchorVars9 a, Val9 I N q.1) (i : Fin k) :
    ∃ y : Fin N,
      y = targetAssignmentEquiv9 (I := I) a hsep s i ∧
      anc9 (S07.glue (targetAnchorVars9 a) ω s) (I.center (a i).1) =
        anc9 (updAnc9 ω (I.center (a i).1) y) (I.center (a i).1) ∧
      (∀ b : StarOdd9 (a i), ∀ c ∈ I.seen b.1.1,
        anc9 (S07.glue (targetAnchorVars9 a) ω s) c =
          anc9 (updAnc9 ω (I.center (a i).1) y) c) ∧
      (∀ b : StarOdd9 (a i),
        msk9 (S07.glue (targetAnchorVars9 a) ω s) b.1 =
          msk9 (updAnc9 ω (I.center (a i).1) y) b.1) := by
  classical
  let e : Fin k ≃ targetAnchorVars9 (I := I) a := targetAnchorEquiv9 (I := I) a hsep
  let y : Fin N := s (e i)
  have hown : S07.glue (targetAnchorVars9 a) ω s (e i).1 = y := by
    unfold S07.glue
    rw [dif_pos (e i).2]
  have hglueCenter : S07.glue (targetAnchorVars9 a) ω s
      (Sum.inl (I.center (a i).1)) = y := by
    change S07.glue (targetAnchorVars9 a) ω s (e i).1 = y
    exact hown
  have hcenterOwn :
      anc9 (S07.glue (targetAnchorVars9 a) ω s) (I.center (a i).1) =
        anc9 (updAnc9 ω (I.center (a i).1) y) (I.center (a i).1) := by
    calc
      anc9 (S07.glue (targetAnchorVars9 a) ω s) (I.center (a i).1) = y := by
        simpa [anc9, Val9] using hglueCenter
      _ = anc9 (updAnc9 ω (I.center (a i).1) y) (I.center (a i).1) := by
        simp [anc9, updAnc9, Function.update]
  refine ⟨y, (targetAssignmentEquiv9_apply (I := I) a hsep s i).symm, ?_, ?_, ?_⟩
  · exact hcenterOwn
  · intro b c hc
    by_cases hq : (Sum.inl c : I.ID ⊕ OddSites9 n) ∈ targetAnchorVars9 a
    · rcases Finset.mem_image.mp hq with ⟨j, hj, hqj⟩
      have hcenter : I.center (a j).1 = c := Sum.inl.inj hqj
      have hji : j = i := by
        by_contra hne
        have hne' : i ≠ j := by
          intro h
          apply hne
          exact h.symm
        have hnot := otherTarget9_not_seen (P := P) (n := n) (k := k)
          (I := I) a hsep (i := i) (j := j) hne' b
        have hseen : I.center (a j).1 ∈ I.seen b.1.1 := by simpa [hcenter] using hc
        exact hnot hseen
      have hc_eq : c = I.center (a i).1 := by simpa [hji] using hcenter.symm
      rw [hc_eq]
      exact hcenterOwn
    · have hne : c ≠ I.center (a i).1 := by
        intro heq
        subst c
        exact hq ((e i).2)
      have hglue : S07.glue (targetAnchorVars9 a) ω s (Sum.inl c) = ω (Sum.inl c) := by
        simp [S07.glue, hq, Val9]
        rfl
      calc
        anc9 (S07.glue (targetAnchorVars9 a) ω s) c = anc9 ω c := by
          simpa [anc9, Val9] using hglue
        _ = anc9 (updAnc9 ω (I.center (a i).1) y) c := by
          rw [anc9_update_ne ω (I.center (a i).1) c y hne]
  · intro b
    have hnot : (Sum.inr b.1 : I.ID ⊕ OddSites9 n) ∉ targetAnchorVars9 a := by
      intro h
      rcases Finset.mem_image.mp h with ⟨j, hj, heq⟩
      cases heq
    simp [msk9, S07.glue, hnot, updAnc9, Function.update, Val9]
    rfl

set_option maxHeartbeats 1000000 in
private theorem targetAnchorFreeIntegralBound9 {P : Params9} {n k N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (a : Fin k → EvenSites9 n)
    (hsep : ∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1)
    (ω : Outcome9 I N) (x : Fin N) (hcancel : StarCancel9 S I E G) :
    ∑ s : ∀ q : targetAnchorVars9 a, Val9 I N q.1,
      (∏ q : targetAnchorVars9 a, (inputLaw9 S I q.1).w (s q)) *
        ∏ i : Fin k, evenStar9 S E G (S07.glue (targetAnchorVars9 a) ω s) (a i) x ≤
      ∏ i : Fin k, (N : ℝ) * (siteFirst9 S (a i).1).w x := by
  classical
  let e : Fin k ≃ targetAnchorVars9 (I := I) a := targetAnchorEquiv9 (I := I) a hsep
  let assignmentEquiv : (∀ q : targetAnchorVars9 (I := I) a, Val9 I N q.1) ≃
      (Fin k → Fin N) := targetAssignmentEquiv9 (I := I) (N := N) a hsep
  let F : (∀ q : targetAnchorVars9 a, Val9 I N q.1) → ℝ := fun s =>
    (∏ q : targetAnchorVars9 a, (inputLaw9 S I q.1).w (s q)) *
      ∏ i : Fin k, evenStar9 S E G (S07.glue (targetAnchorVars9 a) ω s) (a i) x
  let H : (Fin k → Fin N) → ℝ := fun f =>
    ∏ i : Fin k,
      (siteFirst9 S (a i).1).w (f i) *
        evenStar9 S E G (updAnc9 ω (I.center (a i).1) (f i)) (a i) x
  have hweight (s : ∀ q : targetAnchorVars9 a, Val9 I N q.1) :
      (∏ q : targetAnchorVars9 a, (inputLaw9 S I q.1).w (s q)) =
        ∏ i : Fin k, (siteFirst9 S (a i).1).w (assignmentEquiv s i) := by
    let wU : targetAnchorVars9 a → ℝ := fun q => (inputLaw9 S I q.1).w (s q)
    have hlabel (i : Fin k)
        (hq : (Sum.inl (I.center (a i).1) : I.ID ⊕ OddSites9 n) ∈ targetAnchorVars9 a) :
        assignmentEquiv s i = s ⟨Sum.inl (I.center (a i).1), hq⟩ := by
      rcases glueStarLocalAgree9 a hsep ω s i with ⟨y, hvalue, hcenter, hanc, hmask⟩
      have hown : anc9 (S07.glue (targetAnchorVars9 a) ω s) (I.center (a i).1) = y := by
        calc
          anc9 (S07.glue (targetAnchorVars9 a) ω s) (I.center (a i).1) =
              anc9 (updAnc9 ω (I.center (a i).1) y) (I.center (a i).1) := hcenter
          _ = y := by simp [anc9, updAnc9, Function.update]
      have hglue : S07.glue (targetAnchorVars9 a) ω s
          (Sum.inl (I.center (a i).1)) = s ⟨Sum.inl (I.center (a i).1), hq⟩ := by
        unfold S07.glue
        rw [dif_pos hq]
      have hglue' :
          (S07.glue (targetAnchorVars9 a) ω s
            (Sum.inl (I.center (a i).1)) : Fin N) =
          (s ⟨Sum.inl (I.center (a i).1), hq⟩ : Fin N) := by
        simpa [Val9] using hglue
      have hs : s ⟨Sum.inl (I.center (a i).1), hq⟩ = y := by
        change (s ⟨Sum.inl (I.center (a i).1), hq⟩ : Fin N) = y
        have hGlueAnc :
            (S07.glue (targetAnchorVars9 a) ω s (Sum.inl (I.center (a i).1)) : Fin N) =
              anc9 (S07.glue (targetAnchorVars9 a) ω s) (I.center (a i).1) := by
          change (S07.glue (targetAnchorVars9 a) ω s
            (Sum.inl (I.center (a i).1)) : Fin N) =
              (S07.glue (targetAnchorVars9 a) ω s
                (Sum.inl (I.center (a i).1)) : Fin N)
          rfl
        exact hglue'.symm.trans (hGlueAnc.trans hown)
      exact hvalue.symm.trans hs.symm
    have hweightCenter (i : Fin k)
        (hq : (Sum.inl (I.center (a i).1) : I.ID ⊕ OddSites9 n) ∈ targetAnchorVars9 a) :
        wU ⟨Sum.inl (I.center (a i).1), hq⟩ =
          (siteFirst9 S (a i).1).w (s ⟨Sum.inl (I.center (a i).1), hq⟩) := by
      dsimp [wU]
      simp [inputLaw9, siteFirst9, IDMap9.center_slice, Val9]
    calc
      (∏ q : targetAnchorVars9 a, (inputLaw9 S I q.1).w (s q)) =
          ∏ i : Fin k, wU (e i) := by
            exact (Equiv.prod_comp e wU).symm
      _ = ∏ i : Fin k, (siteFirst9 S (a i).1).w (assignmentEquiv s i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hq : (Sum.inl (I.center (a i).1) : I.ID ⊕ OddSites9 n) ∈
            targetAnchorVars9 a := by
          unfold targetAnchorVars9
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        have heq := targetAnchorEquiv9_apply (I := I) a hsep i hq
        calc
          wU (e i) = wU ⟨Sum.inl (I.center (a i).1), hq⟩ := congrArg wU heq
          _ = (siteFirst9 S (a i).1).w (s ⟨Sum.inl (I.center (a i).1), hq⟩) :=
            hweightCenter i hq
          _ = (siteFirst9 S (a i).1).w (assignmentEquiv s i) := by rw [← hlabel i hq]
  have hstars (s : ∀ q : targetAnchorVars9 a, Val9 I N q.1) :
      (∏ i : Fin k, evenStar9 S E G (S07.glue (targetAnchorVars9 a) ω s) (a i) x) =
        ∏ i : Fin k, evenStar9 S E G
          (updAnc9 ω (I.center (a i).1) (assignmentEquiv s i)) (a i) x := by
    apply Finset.prod_congr rfl
    intro i hi
    rcases glueStarLocalAgree9 a hsep ω s i with ⟨y, hvalue, hcenter, hanc, hmask⟩
    have hy : assignmentEquiv s i = y := hvalue.symm
    rw [hy]
    exact evenStar9_eq_of_localAgree S E G
      (S07.glue (targetAnchorVars9 a) ω s)
      (updAnc9 ω (I.center (a i).1) y) (a i) x hcenter hanc hmask
  have hF (s : ∀ q : targetAnchorVars9 a, Val9 I N q.1) : F s = H (assignmentEquiv s) := by
    have hweight' :
        (∏ q ∈ (targetAnchorVars9 a).attach, (inputLaw9 S I q.1).w (s q)) =
          ∏ i : Fin k, (siteFirst9 S (a i).1).w (assignmentEquiv s i) := by
      simpa only [Finset.univ_eq_attach] using hweight s
    dsimp [F, H]
    rw [hweight', hstars s]
    rw [← Finset.prod_mul_distrib]
  have hsum :
      (∑ s : ∀ q : targetAnchorVars9 a, Val9 I N q.1, F s) =
        ∑ f : Fin k → Fin N, H f :=
    Fintype.sum_equiv assignmentEquiv F H hF
  calc
    (∑ s : ∀ q : targetAnchorVars9 a, Val9 I N q.1,
        (∏ q : targetAnchorVars9 a, (inputLaw9 S I q.1).w (s q)) *
          ∏ i : Fin k, evenStar9 S E G (S07.glue (targetAnchorVars9 a) ω s) (a i) x) =
        ∑ f : Fin k → Fin N, H f := by
          rw [← hsum]
    _ ≤ ∏ i : Fin k, (N : ℝ) * (siteFirst9 S (a i).1).w x :=
      independentTargetStars9 S E G a x ω hcancel

theorem p92_even_anchor_integral_core (P : Params9) (hP : P.Valid) (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {M : TagMix N} {G : Colour}
      (S : Setup9 P n N M) (I : IDMap9 P n),
      S07.CondProductBound → AnchorLLL9 S I E G c → StarScopeFacts9 S I E G →
        StarCancel9 S I E G → EvenAnchorIntegral9 S I E G := by
  obtain ⟨n₀, htail⟩ := tail_degree_small9 P hP c hc
  refine ⟨n₀, ?_⟩
  intro n hn N E M G S I hCP hLLL hscope hcancel
  change S07.LLLInput (inputLaw9 S I) (fun v ω => StarBad9 S E G ω v)
      (starScope9 I) (P.tail c n) (lllDegree9 P n) at hLLL
  change ∀ (x : Fin N) (k : ℕ), k ≤ n → ∀ a : Fin k → EvenSites9 n,
    (∀ i j : Fin k, j < i → ¬ siteNear9 P n (a i).1 (a j).1) →
    (anchorLaw9 S I E G).expect (fun ω => ∏ i, evenStar9 S E G ω (a i) x) ≤
      2 ^ k * ∏ i, (N : ℝ) * (siteFirst9 S (a i).1).w x
  intro x k hk a hsep
  by_cases hk0 : k = 0
  · subst k
    simp [FinProb.expect_const]
  · have hnPos : 0 < n := by
      have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
      omega
    let U : Finset (I.ID ⊕ OddSites9 n) := targetAnchorVars9 a
    let Φ : Outcome9 I N → ℝ := fun ω => ∏ i : Fin k, evenStar9 S E G ω (a i) x
    let B : ℝ := ∏ i : Fin k, (N : ℝ) * (siteFirst9 S (a i).1).w x
    have hΦnonneg : ∀ ω, 0 ≤ Φ ω := by
      intro ω
      exact Finset.prod_nonneg fun i hi => evenStar9_nonneg S E G ω (a i) x
    have hfree : ∀ ω,
        ∑ s : ∀ q : U, Val9 I N q.1,
          (∏ q : U, (inputLaw9 S I q.1).w (s q)) * Φ (S07.glue U ω s) ≤ B := by
      intro ω
      simpa [U, Φ, B] using targetAnchorFreeIntegralBound9 S E G a hsep ω x hcancel
    have hbadCount :
        (Finset.univ.filter fun v : EvenSites9 n =>
          ¬ Disjoint (starScope9 I v) U).card ≤ k * (lllDegree9 P n + 1) := by
      simpa [U] using targetAnchor_badCount9 S E G a hnPos hscope
    let t := (Finset.univ.filter fun v : EvenSites9 n =>
      ¬ Disjoint (starScope9 I v) U).card
    have ht : t ≤ k * (lllDegree9 P n + 1) := by
      exact hbadCount
    have hsmall := htail n hn
    have hsmall' : P.tail c n * ((lllDegree9 P n + 1 : ℕ) : ℝ) ≤ 1 / 4 := by
      simpa [Nat.cast_add] using hsmall
    have hpen := condPenalty9 hLLL.x_nonneg hsmall' ht
    have hCPbound := hCP (inputLaw9 S I)
      (fun v ω => StarBad9 S E G ω v) (starScope9 I) (P.tail c n) (lllDegree9 P n) hLLL
    rcases hCPbound with ⟨havoid, hcond⟩
    have hcondBound : (anchorLaw9 S I E G).expect Φ ≤
        ((1 - P.tail c n) ^ t)⁻¹ * B := by
      simpa [anchorLaw9, rawLaw9, U, Φ, t] using hcond U Φ hΦnonneg B hfree
    have hBnonneg : 0 ≤ B := by
      dsimp [B]
      exact Finset.prod_nonneg fun i hi =>
        mul_nonneg (Nat.cast_nonneg N) ((siteFirst9 S (a i).1).nonneg x)
    calc
      (anchorLaw9 S I E G).expect Φ ≤ ((1 - P.tail c n) ^ t)⁻¹ * B := hcondBound
      _ ≤ (2 : ℝ) ^ k * B := mul_le_mul_of_nonneg_right hpen hBnonneg
      _ = 2 ^ k * ∏ i : Fin k, (N : ℝ) * (siteFirst9 S (a i).1).w x := by rfl

end HypercubeRamsey.Lane_q_s09_assign2
