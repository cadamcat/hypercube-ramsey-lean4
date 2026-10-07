import HypercubeRamsey.S07.AnchorStage
import HypercubeRamsey.S03.ClockSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 1000000

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open Filter
open scoped BigOperators

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans_eq (by norm_num)

theorem clockCellCap_small (d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, cellCap d n (gS d n) ≤ Real.exp ((n : ℝ) / 4) := by
  let gap : ℝ := 1 / 4 - d
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let r : ℝ := 1 / 4
  have hr : 0 < r := by norm_num [r]
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ r) atTop (nhds 0) := by
    simpa [r, Function.comp_def] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < (1 / 4 : ℝ))).tendsto_div_nhds_zero).comp
        tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ gap) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  have hlogSmall : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) / (n : ℝ) ^ r < 1 :=
    hloglim.eventually (eventually_lt_nhds (by norm_num))
  have hpowLarge : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ gap := hpow.eventually_ge_atTop 2
  have htail : ∀ᶠ n : ℕ in atTop,
      cellCap d n (gS d n) ≤ Real.exp ((n : ℝ) / 4) := by
    filter_upwards [hlogSmall, hpowLarge, Filter.eventually_ge_atTop (144 : ℕ)] with n hlog hgapN hn
    have hn1 : 1 ≤ n := by omega
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    have hx : 1 ≤ (n : ℝ) ^ d := Real.one_le_rpow hnR hd.le
    have hsceil : (gS d n : ℝ) ≤ (n : ℝ) ^ d + 1 := by
      dsimp [gS]
      exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ d)).le
    have hs : (gS d n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
      have hs' : (gS d n : ℝ) ≤ 2 * (n : ℝ) ^ d := by nlinarith [hsceil, hx]
      have hmul : 2 * (n : ℝ) ^ d ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
        have heq : (n : ℝ) ^ d * (n : ℝ) ^ gap = (n : ℝ) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add (by positivity : 0 < (n : ℝ))]
          congr 1
          dsimp [gap]
          ring
        rw [← heq]
        calc
          2 * (n : ℝ) ^ d ≤ (n : ℝ) ^ gap * (n : ℝ) ^ d :=
            mul_le_mul_of_nonneg_right hgapN (by positivity)
          _ = (n : ℝ) ^ d * (n : ℝ) ^ gap := by ring
      exact le_trans hs' hmul
    have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
      have hpowpos : 0 < (n : ℝ) ^ r := Real.rpow_pos_of_pos (by positivity) r
      have hlt := (div_lt_iff₀ hpowpos).mp hlog
      simpa [r] using hlt.le
    have hnd : (n : ℝ) ^ (d / 2) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
      have hexp : d / 2 ≤ (1 / 4 : ℝ) := by linarith
      exact Real.rpow_le_rpow_of_exponent_le hnR hexp
    have hcoeff : 0 ≤ 2 * (d / 80) := by positivity
    have hcapExp :
        (n : ℝ) ^ (d / 2) + 2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) + 1 ≤
          (n : ℝ) / 4 := by
      have hterm : 2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) ≤
          2 * (d / 80) * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
        have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
        calc
          2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) ≤
              2 * (d / 80) * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log (n : ℝ) := by
                calc
                  _ = 2 * (d / 80) * ((gS d n : ℝ) * Real.log (n : ℝ)) := by ring
                  _ ≤ 2 * (d / 80) * ((n : ℝ) ^ (1 / 4 : ℝ) * Real.log (n : ℝ)) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right hs hnlog) hcoeff
                  _ = _ := by ring
          _ ≤ 2 * (d / 80) * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
            calc
              _ = 2 * (d / 80) * ((n : ℝ) ^ (1 / 4 : ℝ) * Real.log (n : ℝ)) := by ring
              _ ≤ 2 * (d / 80) * ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hlog (by positivity)) hcoeff
              _ = _ := by ring
      have hrpow2 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (n : ℝ)) (1 / 4 : ℝ) 2]
        norm_num
      have hnquarter : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
      have hsmallCoeff : 2 * (d / 80) ≤ 1 / 100 := by
        nlinarith [hd']
      have hterm' : 2 * (d / 80) * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 ≤
          (1 / 100) * (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [hrpow2]
        exact mul_le_mul_of_nonneg_right hsmallCoeff (by positivity)
      have hroot : 3 * (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) / 4 := by
        have hroot2 : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 12 := by
          apply Real.sqrt_le_iff.mpr
          constructor
          · positivity
          · have hnR144 : (144 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            have hnprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 144) :=
              mul_nonneg (by positivity) (by linarith)
            nlinarith
        rw [← Real.sqrt_eq_rpow]
        nlinarith [hroot2]
      have hsum :
          (n : ℝ) ^ (d / 2) + 2 * (d / 80) * (gS d n : ℝ) * Real.log (n : ℝ) + 1 ≤
            (n : ℝ) ^ (1 / 4 : ℝ) + (1 / 100) * (n : ℝ) ^ (1 / 2 : ℝ) + 1 := by
        nlinarith [hnd, hterm.trans hterm']
      have hfinal :
          (n : ℝ) ^ (1 / 4 : ℝ) + (1 / 100) * (n : ℝ) ^ (1 / 2 : ℝ) + 1 ≤
            3 * (n : ℝ) ^ (1 / 2 : ℝ) := by
        nlinarith [hnquarter, Real.one_le_rpow hnR (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]
      exact hsum.trans (hfinal.trans hroot)
    unfold cellCap
    exact Real.exp_le_exp.mpr hcapExp
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 htail
  exact ⟨max n₀ 144, fun n hn => hn₀ n (le_trans (le_max_left _ _) hn)⟩

theorem pi_pr_dependsOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (S : Finset ι) (F : (∀ i, Ω i) → Prop)
    (hF : FinProb.DependsOn F S) (o₀ : ∀ i, Ω i) :
    (FinProb.pi P).pr F =
      (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).pr
        (fun z => F (fun i => if h : i ∈ S then z ⟨i, h⟩ else o₀ i)) := by
  classical
  let extend : (∀ i : {i // i ∈ S}, Ω i.1) → ∀ i, Ω i :=
    fun z i => if h : i ∈ S then z ⟨i, h⟩ else o₀ i
  let g : (∀ i : {i // i ∈ S}, Ω i.1) → ℝ := fun z => if F (extend z) then 1 else 0
  have hext (ω : ∀ i, Ω i) : F ω = F (extend (fun i => ω i.1)) := by
    apply hF
    intro i hi
    simp [extend, hi]
  calc
    (FinProb.pi P).pr F =
        (FinProb.pi P).expect (fun ω => if F ω then 1 else 0) := by
      simp [FinProb.pr, FinProb.expect]
    _ = (FinProb.pi P).expect (fun ω => g (fun i : {i // i ∈ S} => ω i.1)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro ω hω
      change (FinProb.pi P).w ω * (if F ω then 1 else 0) =
        (FinProb.pi P).w ω * (if F (extend (fun i : {i // i ∈ S} => ω i.1)) then 1 else 0)
      rw [hext ω]
    _ = (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).expect g :=
      FinProb.pi_marginal_expect P S g
    _ = (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).pr
        (fun z => F (extend z)) := by
      unfold FinProb.expect FinProb.pr
      apply Finset.sum_congr rfl
      intro z hz
      by_cases h : F (extend z) <;> simp [g, h]

def clockOddScope {n : ℕ} (a : EvenRole n) : Finset (OddRole n) :=
  Finset.univ.image (oddNbr a)

theorem cubeFlip_twice_early {n : ℕ} (v : CubeVertex n) (j : Fin n) :
    cubeFlip (cubeFlip v j) j = v := by
  funext k
  by_cases hkj : k = j <;> simp [cubeFlip, hkj]

theorem oddNbr_injective_early {n : ℕ} (a : EvenRole n) :
    Function.Injective (oddNbr a) := by
  intro j k h
  have hv : cubeFlip a.1 j = cubeFlip a.1 k := congrArg Subtype.val h
  by_contra hne
  have hj := congrFun hv j
  have hjFlip : cubeFlip a.1 j j = !a.1 j := by simp [cubeFlip]
  have hkStay : cubeFlip a.1 k j = a.1 j := by simp [cubeFlip, hne]
  rw [hjFlip, hkStay] at hj
  cases hb : a.1 j <;> simp [hb] at hj

noncomputable def clockOddScopeEquiv {n : ℕ} (a : EvenRole n) :
    Fin n ≃ {u : OddRole n // u ∈ clockOddScope a} := by
  classical
  let f : Fin n → {u : OddRole n // u ∈ clockOddScope a} := fun j =>
    ⟨oddNbr a j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro j k h
      exact oddNbr_injective_early a (congrArg Subtype.val h)
    · intro u
      rcases Finset.mem_image.mp u.2 with ⟨j, hj, hu⟩
      exact ⟨j, Subtype.ext hu⟩
  exact Equiv.ofBijective f hf

theorem nat_le_cube {k : ℕ} (hk : 1 ≤ k) : k ≤ k ^ 3 := by
  have hsq : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc
    k = k * 1 := by simp
    _ ≤ k * k ^ 2 := Nat.mul_le_mul_left k hsq
    _ = k ^ 3 := by rw [pow_succ]; exact Nat.mul_comm _ _

section Nodes

variable {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
  {p κ : ℝ}

theorem starLik_nonneg (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hrow : RowLaw Γ M) (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N)
    (v : CubeVertex n) (z : Fin N) (y : Fin n → Fin N) :
    0 ≤ starLik Γ M σ W v z y := by
  unfold starLik
  apply Finset.prod_nonneg
  intro j hj
  exact (hrow σ (Function.update W (Γ.key v) z) (Γ.key (cubeFlip v j))).1 (y j)

theorem starMarg_nonneg (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hrow : RowLaw Γ M) (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N)
    (v : CubeVertex n) (y : Fin n → Fin N) :
    0 ≤ starMarg Γ M σ W v y := by
  unfold starMarg
  apply Finset.sum_nonneg
  intro z hz
  exact mul_nonneg ((M.μ (σ (Γ.key v).1)).nonneg z) (starLik_nonneg Γ M hrow σ W v z y)

theorem evenRowAt_nonneg_of_success (Γ : GridGeom d n s ℓ q)
    (M : Menu7 n N E G X Y d p κ) (hrow : RowLaw Γ M) (σ : Γ.Key → M.ι)
    (W : Γ.Cell → Fin N) (a : EvenRole n) (y : Fin n → Fin N) (x : Fin N)
    (hgood : ¬ PredFail Γ M σ W a.1 y) : 0 ≤ evenRowAt Γ M σ W a y x := by
  have hmarg_nonneg := starMarg_nonneg Γ M hrow σ W a.1 y
  have hmarg_ne : starMarg Γ M σ W a.1 y ≠ 0 := by
    intro hzero
    exact hgood (Or.inl hzero)
  have hmarg_pos : 0 < starMarg Γ M σ W a.1 y := lt_of_le_of_ne hmarg_nonneg (Ne.symm hmarg_ne)
  unfold evenRowAt
  apply div_nonneg
  · exact mul_nonneg (starLik_nonneg Γ M hrow σ W a.1 x y)
      ((M.μ (σ (Γ.key a.1).1)).nonneg x)
  · exact hmarg_pos.le

theorem evenStar_nonneg (Γ : GridGeom d n s ℓ q)
    (M : Menu7 n N E G X Y d p κ) (hrow : RowLaw Γ M) (σ : Γ.Key → M.ι)
    (W : Γ.Cell → Fin N) (a : EvenRole n) (x : Fin N) :
    0 ≤ evenStar Γ M σ W a x := by
  unfold evenStar
  apply Finset.sum_nonneg
  intro y hy
  apply mul_nonneg
  · exact Finset.prod_nonneg fun j hj =>
      (hrow σ W (Γ.key (cubeFlip a.1 j))).1 (y j)
  · by_cases hfail : PredFail Γ M σ W a.1 y
    · simp [hfail]
    · simp only [if_neg hfail, one_mul]
      exact mul_nonneg (by positivity)
        (evenRowAt_nonneg_of_success Γ M hrow σ W a y x hfail)

theorem pi_expect_prod_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] {m : ℕ}
    (P : ∀ i, FinProb (Ω i)) (scope : Fin m → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (scope i) (scope j))
    (F : Fin m → (∀ i, Ω i) → ℝ)
    (hdep : ∀ j, FinProb.DependsOn (F j) (scope j)) :
    (FinProb.pi P).expect (fun ω => ∏ j, F j ω) =
      ∏ j, (FinProb.pi P).expect (F j) := by
  classical
  induction m with
  | zero =>
      simpa using (FinProb.expect_const (FinProb.pi P) (1 : ℝ))
  | succ m ih =>
      let tailScope : Fin m → Finset ι := fun i => scope i.castSucc
      let tailF : Fin m → (∀ i, Ω i) → ℝ := fun i ω => F i.castSucc ω
      let tailUnion : Finset ι := Finset.univ.biUnion tailScope
      have hdisj0 : Disjoint (scope (Fin.last m)) tailUnion := by
        apply Finset.disjoint_left.mpr
        intro u hu hU
        rcases Finset.mem_biUnion.mp hU with ⟨i, hi, hui⟩
        have hne : Fin.last m ≠ i.castSucc := by
          intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
        exact (Finset.disjoint_left.mp (hdisj (Fin.last m) i.castSucc hne)) hu hui
      have hdepTail : FinProb.DependsOn (fun ω => ∏ i : Fin m, tailF i ω) tailUnion := by
        intro ω ω' hagree
        apply Finset.prod_congr rfl
        intro i hi
        apply hdep i.castSucc ω ω'
        intro u hu
        exact hagree u (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hu⟩)
      have hdisjTail : ∀ i j : Fin m, i ≠ j → Disjoint (tailScope i) (tailScope j) := by
        intro i j hij
        apply hdisj i.castSucc j.castSucc
        intro h
        apply hij
        exact Fin.castSucc_injective _ h
      have htail := ih tailScope hdisjTail tailF (by
        intro i
        exact hdep i.castSucc)
      have hfactor := FinProb.pi_expect_mul_of_disjoint P
        (fun ω => ∏ i : Fin m, tailF i ω) (F (Fin.last m)) tailUnion (scope (Fin.last m))
        hdepTail (hdep (Fin.last m)) hdisj0.symm
      calc
        (FinProb.pi P).expect (fun ω => ∏ j : Fin (m + 1), F j ω) =
            (FinProb.pi P).expect (fun ω => ∏ i : Fin m, tailF i ω) *
              (FinProb.pi P).expect (F (Fin.last m)) := by
                calc
                  (FinProb.pi P).expect (fun ω => ∏ j : Fin (m + 1), F j ω) =
                      (FinProb.pi P).expect (fun ω =>
                        (∏ i : Fin m, tailF i ω) * F (Fin.last m) ω) := by
                          congr 1
                          funext ω
                          simp [tailF, Fin.prod_univ_castSucc]
                  _ = (FinProb.pi P).expect (fun ω => ∏ i : Fin m, tailF i ω) *
                        (FinProb.pi P).expect (F (Fin.last m)) := hfactor
        _ = (∏ i : Fin m, (FinProb.pi P).expect (tailF i)) *
              (FinProb.pi P).expect (F (Fin.last m)) := by rw [htail]
        _ = ∏ j : Fin (m + 1), (FinProb.pi P).expect (F j) := by
              rw [Fin.prod_univ_castSucc]

end Nodes

section Nodes

variable {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
  {p κ : ℝ}

theorem hammingDist_flip {n : ℕ} (v : CubeVertex n) (j : Fin n) :
    HypercubeRamsey.hammingDist v (cubeFlip v j) = 1 := by
  classical
  unfold HypercubeRamsey.hammingDist
  have hset : Finset.univ.filter (fun k : Fin n => v k ≠ cubeFlip v j k) = {j} := by
    ext k
    by_cases hkj : k = j
    · subst k
      cases hv : v j <;> simp [cubeFlip, hv]
    · have hflip : cubeFlip v j k = v k := Function.update_of_ne hkj _ _
      simp [hflip, hkj]
  rw [hset]
  simp

theorem hammingDist_comm {n : ℕ} (v w : CubeVertex n) :
    HypercubeRamsey.hammingDist v w = HypercubeRamsey.hammingDist w v := by
  classical
  unfold HypercubeRamsey.hammingDist
  congr 1
  ext j
  constructor
  · intro h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    intro hEq
    exact h hEq.symm
  · intro h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    intro hEq
    exact h hEq.symm

theorem auxDist_le_hamming {d : ℝ} {n s ℓ q : ℕ}
    (Γ : GridGeom d n s ℓ q) (v w : CubeVertex n) :
    Γ.auxDist (Γ.key v).2 (Γ.key w).2 ≤ HypercubeRamsey.hammingDist v w := by
  classical
  unfold GridGeom.auxDist HypercubeRamsey.hammingDist
  change (Finset.univ.filter (fun j : Γ.aux => v j.1 ≠ w j.1)).card ≤
    (Finset.univ.filter (fun j : Fin n => v j ≠ w j)).card
  let U : Finset Γ.aux := Finset.univ.filter (fun j : Γ.aux => v j.1 ≠ w j.1)
  have hsubset : U.image (fun j : Γ.aux => j.1) ⊆
      Finset.univ.filter (fun j : Fin n => v j ≠ w j) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨u, hu, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
  calc
    U.card = (U.image (fun j : Γ.aux => j.1)).card := by
      symm
      exact Finset.card_image_of_injective U (fun x y h => Subtype.ext h)
    _ ≤ (Finset.univ.filter (fun j : Fin n => v j ≠ w j)).card := Finset.card_le_card hsubset

theorem auxDist_comm {d : ℝ} {n s ℓ q : ℕ}
    (Γ : GridGeom d n s ℓ q) (t t' : Γ.AuxWord) :
    Γ.auxDist t t' = Γ.auxDist t' t := by
  classical
  unfold GridGeom.auxDist
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

theorem auxDist_le_two_of_shared_neighbor {d : ℝ} {n s ℓ q : ℕ}
    (Γ : GridGeom d n s ℓ q) (a b : EvenRole n) (j k : Fin n)
    (h : oddNbr a j = oddNbr b k) :
    Γ.auxDist (Γ.key a.1).2 (Γ.key b.1).2 ≤ 2 := by
  have hv : cubeFlip a.1 j = cubeFlip b.1 k := congrArg Subtype.val h
  have htri := HypercubeRamsey.hammingDist_triangle a.1 (cubeFlip a.1 j) b.1
  have ha := hammingDist_flip a.1 j
  have hb := hammingDist_flip b.1 k
  have hb' : HypercubeRamsey.hammingDist (cubeFlip b.1 k) b.1 = 1 := by
    rw [hammingDist_comm]
    exact hb
  have hdist : HypercubeRamsey.hammingDist a.1 b.1 ≤ 2 := by
    calc
      HypercubeRamsey.hammingDist a.1 b.1 ≤
          HypercubeRamsey.hammingDist a.1 (cubeFlip a.1 j) +
            HypercubeRamsey.hammingDist (cubeFlip a.1 j) b.1 := htri
      _ = 1 + 1 := by rw [ha, hv, hb']
  exact le_trans (auxDist_le_hamming Γ a.1 b.1) hdist

theorem oddNbr_injective {n : ℕ} (a : EvenRole n) : Function.Injective (oddNbr a) := by
  intro j k h
  have hv : cubeFlip a.1 j = cubeFlip a.1 k := congrArg Subtype.val h
  by_contra hne
  have hj := congrFun hv j
  have hjFlip : cubeFlip a.1 j j = !a.1 j := by simp [cubeFlip]
  have hkStay : cubeFlip a.1 k j = a.1 j := by
    simp [cubeFlip, hne]
  rw [hjFlip, hkStay] at hj
  cases hb : a.1 j <;> simp [hb] at hj

end Nodes

theorem evenLoadsTail (d : ℝ) (hd : 0 < d) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (n : ℝ) * ((gQ d n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ (gQ d n))⁻¹ *
        Real.exp ((6 / 100 : ℝ) * (gQ d n : ℝ)) ≤ 1 := by
  classical
  let α : ℝ := 4 * d
  have hα : 0 < α := by dsimp [α]; positivity
  let c : ℝ := Real.log 2 - 6 / 100
  have hc : 0 < c := by
    dsimp [c]
    have hlog : (2 : ℝ) / 3 < Real.log 2 := by
      have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num)
      norm_num at h ⊢
      linarith
    linarith
  have hq_tendsto : Tendsto (fun n : ℕ => (gQ d n : ℝ)) atTop atTop := by
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ α) atTop atTop :=
      (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
    exact Filter.tendsto_atTop_mono (l := atTop)
      (f := fun n : ℕ => (n : ℝ) ^ α) (g := fun n => (gQ d n : ℝ))
      (fun n => by simpa [gQ, α] using (Nat.le_ceil ((n : ℝ) ^ (4 * d)))) hpow
  have hlim :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 + α⁻¹) c hc).comp hq_tendsto
  have hevent : ∀ᶠ n : ℕ in atTop,
      32 * (gQ d n : ℝ) ^ (5 + α⁻¹) * Real.exp (-c * (gQ d n : ℝ)) < 1 := by
    have hsmall : ∀ᶠ n : ℕ in atTop,
        (gQ d n : ℝ) ^ (5 + α⁻¹) * Real.exp (-c * (gQ d n : ℝ)) < (1 / 32 : ℝ) :=
      hlim.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hsmall] with n hn
    nlinarith
  have hq_ge_one : ∀ᶠ n : ℕ in atTop, 1 ≤ (gQ d n : ℝ) :=
    hq_tendsto.eventually_ge_atTop 1
  have htail : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * ((gQ d n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ (gQ d n))⁻¹ *
        Real.exp ((6 / 100 : ℝ) * (gQ d n : ℝ)) ≤ 1 := by
    filter_upwards [hevent, hq_ge_one, Filter.eventually_ge_atTop (1 : ℕ)] with n hlimn hq1 hn
    let q : ℝ := (gQ d n : ℝ)
    have hqpow : (n : ℝ) ^ α ≤ q := by
      dsimp [q, gQ]
      simpa [α] using (Nat.le_ceil ((n : ℝ) ^ (4 * d)))
    have hqpos : 0 < q := by dsimp [q]; linarith
    have hqone : 1 ≤ q := by dsimp [q]; exact hq1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnle : (n : ℝ) ≤ q ^ α⁻¹ := by
      calc
        (n : ℝ) = ((n : ℝ) ^ α) ^ α⁻¹ := by
          rw [Real.rpow_rpow_inv hnpos.le hα.ne']
        _ ≤ q ^ α⁻¹ := Real.rpow_le_rpow (by positivity) hqpow (inv_nonneg.mpr hα.le)
    have hqplus : q + 1 ≤ 2 * q := by linarith
    have hpowexp : ((2 : ℝ) ^ (gQ d n)) = Real.exp (q * Real.log 2) := by
      calc
        ((2 : ℝ) ^ (gQ d n)) = (Real.exp (Real.log 2)) ^ (gQ d n) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        _ = Real.exp (q * Real.log 2) := by
          rw [← Real.exp_nat_mul]
    have hdecay : ((2 : ℝ) ^ (gQ d n))⁻¹ *
        Real.exp ((6 / 100 : ℝ) * q) = Real.exp (-c * q) := by
      rw [hpowexp, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      dsimp [c]
      ring
    calc
      (n : ℝ) * (q + 1) ^ 5 * ((2 : ℝ) ^ (gQ d n))⁻¹ *
          Real.exp ((6 / 100 : ℝ) * q) =
        (n : ℝ) * (q + 1) ^ 5 * Real.exp (-c * q) := by
          calc
            _ = (n : ℝ) * (q + 1) ^ 5 *
                (((2 : ℝ) ^ (gQ d n))⁻¹ * Real.exp ((6 / 100 : ℝ) * q)) := by ring
            _ = _ := by rw [hdecay]
      _ ≤ q ^ α⁻¹ * (2 * q) ^ 5 * Real.exp (-c * q) := by
        gcongr
      _ = 32 * q ^ (5 + α⁻¹) * Real.exp (-c * q) := by
        rw [show (2 * q) ^ 5 = (2 : ℝ) ^ 5 * q ^ 5 by rw [mul_pow],
          show (2 : ℝ) ^ 5 = 32 by norm_num]
        calc
          q ^ α⁻¹ * (32 * q ^ 5) * Real.exp (-c * q) =
              32 * (q ^ α⁻¹ * q ^ (5 : ℝ)) * Real.exp (-c * q) := by
                have hq5 : q ^ (5 : ℝ) = q ^ 5 := Real.rpow_natCast q 5
                rw [← hq5]
                ring
          _ = 32 * q ^ (α⁻¹ + 5) * Real.exp (-c * q) := by
            rw [← Real.rpow_add hqpos]
          _ = 32 * q ^ (5 + α⁻¹) * Real.exp (-c * q) := by
            rw [add_comm α⁻¹ 5]
      _ ≤ 1 := by simpa [q] using hlimn.le
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 htail
  exact ⟨n₀, fun n hn => hn₀ n hn⟩

theorem auxDist_le_cellDist {d : ℝ} {n s ℓ q : ℕ}
    (Γ : GridGeom d n s ℓ q) (c c' : Γ.Cell) :
    Γ.auxDist c.2 c'.2 ≤ Γ.cellDist c c' := by
  unfold GridGeom.cellDist
  exact Nat.le_add_left _ _

theorem cellDist_comm {d : ℝ} {n s ℓ q : ℕ}
    (Γ : GridGeom d n s ℓ q) (c c' : Γ.Cell) :
    Γ.cellDist c c' = Γ.cellDist c' c := by
  unfold GridGeom.cellDist GridGeom.keyDist
  simp [Nat.dist_comm, auxDist_comm]

theorem auxDist_triangle {d : ℝ} {n s ℓ q : ℕ}
    (Γ : GridGeom d n s ℓ q) (t t' t'' : Γ.AuxWord) :
    Γ.auxDist t t'' ≤ Γ.auxDist t t' + Γ.auxDist t' t'' := by
  classical
  unfold GridGeom.auxDist
  let A : Finset Γ.aux := Finset.univ.filter fun j => t j ≠ t' j
  let B : Finset Γ.aux := Finset.univ.filter fun j => t' j ≠ t'' j
  let C : Finset Γ.aux := Finset.univ.filter fun j => t j ≠ t'' j
  have hsub : C ⊆ A ∪ B := by
    intro j hj
    have hjac : t j ≠ t'' j := (Finset.mem_filter.mp hj).2
    by_cases hjab : t j ≠ t' j
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjab⟩))
    · have hjab' : t j = t' j := by simpa using hjab
      have hjbc : t' j ≠ t'' j := by
        intro heq
        exact hjac (hjab'.trans heq)
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjbc⟩))
  calc
    C.card ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le _ _

theorem auxDist_le_one_of_mem_fullNames {d : ℝ} {n s ℓ q : ℕ}
    (Γ : GridGeom d n s ℓ q) {c w : Γ.Cell} (hw : w ∈ Γ.fullNames c) :
    Γ.auxDist c.2 w.2 ≤ 1 := by
  classical
  rcases List.mem_append.mp hw with hcross | hown
  · unfold GridGeom.crossNames at hcross
    rcases List.mem_map.mp hcross with ⟨g, hg, hgw⟩
    have haux : w.2 = c.2 := by
      have h := congrArg Prod.snd hgw
      simpa using h.symm
    rw [haux]
    simp [GridGeom.auxDist]
  · unfold GridGeom.ownNames at hown
    rcases List.mem_map.mp hown with ⟨t, ht, htw⟩
    have haux : w.2 = t := by
      have h := congrArg Prod.snd htw
      exact h.symm
    rw [haux]
    have htball : t ∈ Γ.auxBall c.2 1 := by
      simpa [GridGeom.ownWords] using ht
    exact (Finset.mem_filter.mp htball).2

theorem cellRow_update_of_not_fullNames {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι)
    (W : Γ.Cell → Fin N) (c w : Γ.Cell) (z y : Fin N)
    (hnot : w ∉ Γ.fullNames c) :
    cellRow Γ M σ (Function.update W w z) c y = cellRow Γ M σ W c y := by
  classical
  have hlabelUpdate (u : Γ.Cell) (hu : u ∈ Γ.fullNames c) :
      Function.update W w z u = W u := by
    have hne : u ≠ w := by
      intro heq
      apply hnot
      simpa [heq] using hu
    exact Function.update_of_ne hne z W
  have hlabels : cellLabels Γ (Function.update W w z) c = cellLabels Γ W c := by
    unfold cellLabels
    apply List.map_congr_left
    intro u hu
    exact hlabelUpdate u hu
  have hcrossOrder (h₀ : Γ.Key) (hh₀ : h₀ ∈ Γ.crossKeys c.1) :
      (Γ.crossOrder c.1 h₀).map (fun h => Function.update W w z (h, c.2)) =
        (Γ.crossOrder c.1 h₀).map (fun h => W (h, c.2)) := by
    unfold GridGeom.crossOrder
    apply List.map_congr_left
    intro h hh
    have hkey : h ∈ Γ.crossKeys c.1 := by
      rcases List.mem_append.mp hh with he | hs
      · exact List.mem_of_mem_erase he
      · simp only [List.mem_singleton] at hs
        subst h
        exact hh₀
    have hmem : (h, c.2) ∈ Γ.fullNames c := by
      unfold GridGeom.fullNames GridGeom.crossNames
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨h, hkey, rfl⟩))
    exact hlabelUpdate (h, c.2) hmem
  have hcrossLabels : crossLabels Γ (Function.update W w z) c = crossLabels Γ W c := by
    unfold crossLabels
    apply List.map_congr_left
    intro u hu
    have hmem : u ∈ Γ.fullNames c :=
      List.mem_append.mpr (Or.inl hu)
    exact hlabelUpdate u hmem
  have hcrossValid :
      CrossValidRow Γ M (σ c.1) (fun h => Function.update W w z (h, c.2)) c.1 =
        CrossValidRow Γ M (σ c.1) (fun h => W (h, c.2)) c.1 := by
    unfold CrossValidRow
    apply propext
    constructor
    · intro hv h₀ hh₀ k hk
      rw [← hcrossOrder h₀ hh₀]
      exact hv h₀ hh₀ k hk
    · intro hv h₀ hh₀ k hk
      rw [hcrossOrder h₀ hh₀]
      exact hv h₀ hh₀ k hk
  have hownValid : OwnValid Γ M (σ c.1) (Function.update W w z) c =
      OwnValid Γ M (σ c.1) W c := by
    unfold OwnValid
    rw [hcrossLabels, hlabels]
  have hvalid : CellValid Γ M σ (Function.update W w z) c = CellValid Γ M σ W c := by
    unfold CellValid
    rw [hcrossValid, hownValid]
  simp [cellRow, hvalid, hlabels]

theorem delRow_update_of_not_fullNames {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι)
    (W : Γ.Cell → Fin N) (c w t : Γ.Cell) (z : Fin N)
    (hnot : w ∉ Γ.fullNames c) (hwt : w ≠ t) :
    delRow Γ M σ (Function.update W w z) c t = delRow Γ M σ W c t := by
  classical
  have hlabels : cellLabels Γ (Function.update W w z) c = cellLabels Γ W c := by
    unfold cellLabels
    apply List.map_congr_left
    intro u hu
    have hne : u ≠ w := by
      intro heq
      apply hnot
      simpa [heq] using hu
    exact Function.update_of_ne hne z W
  have htval : Function.update W w z t = W t := Function.update_of_ne hwt.symm z W
  simp [delRow, hlabels, htval]

theorem evenStar_update_far {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hGeom : GeomLocal Γ) (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N)
    (a : EvenRole n) (x : Fin N) (w : Γ.Cell) (z : Fin N)
    (hsep : 6 ≤ Γ.auxDist (Γ.key a.1).2 w.2)
    (hwneq : w ≠ Γ.key a.1) :
    evenStar Γ M σ (Function.update W w z) a x = evenStar Γ M σ W a x := by
  classical
  let target : Γ.Cell := Γ.key a.1
  have hnot (j : Fin n) : w ∉ Γ.fullNames (Γ.key (cubeFlip a.1 j)) := by
    intro hmem
    have hname := auxDist_le_one_of_mem_fullNames Γ hmem
    have hnear : Γ.auxDist target.2 (Γ.key (cubeFlip a.1 j)).2 ≤ 1 :=
      le_trans (auxDist_le_cellDist Γ target (Γ.key (cubeFlip a.1 j)))
        (by simpa [target] using hGeom.flip_dist a.1 j)
    have htri := auxDist_triangle Γ target.2 (Γ.key (cubeFlip a.1 j)).2 w.2
    have hle : Γ.auxDist target.2 w.2 ≤ 2 := by
      calc
        Γ.auxDist target.2 w.2 ≤
            Γ.auxDist target.2 (Γ.key (cubeFlip a.1 j)).2 +
              Γ.auxDist (Γ.key (cubeFlip a.1 j)).2 w.2 := htri
        _ ≤ 2 := by omega
    have : 6 ≤ 2 := le_trans hsep (by simpa [target] using hle)
    omega
  have hcomm (t : Fin N) :
      Function.update (Function.update W w z) target t =
        Function.update (Function.update W target t) w z := by
    funext c
    by_cases hc : c = target
    · subst c
      simp [Function.update, target, Ne.symm hwneq]
    · by_cases hc' : c = w
      · subst c
        simp [Function.update, hc, target]
      · simp [Function.update, hc, hc', target]
  have hrow (t : Fin N) (j : Fin n) (y : Fin N) :
      cellRow Γ M σ (Function.update (Function.update W w z) target t)
          (Γ.key (cubeFlip a.1 j)) y =
        cellRow Γ M σ (Function.update W target t) (Γ.key (cubeFlip a.1 j)) y := by
    rw [hcomm t]
    exact cellRow_update_of_not_fullNames Γ M σ (Function.update W target t)
      (Γ.key (cubeFlip a.1 j)) w z y (hnot j)
  have hstarLik (t : Fin N) (y : Fin n → Fin N) :
      starLik Γ M σ (Function.update W w z) a.1 t y =
        starLik Γ M σ W a.1 t y := by
    unfold starLik
    apply Finset.prod_congr rfl
    intro j hj
    exact hrow t j (y j)
  have hstarMarg (y : Fin n → Fin N) :
      starMarg Γ M σ (Function.update W w z) a.1 y =
        starMarg Γ M σ W a.1 y := by
    unfold starMarg
    apply Finset.sum_congr rfl
    intro t ht
    rw [hstarLik t y]
  have hstarRef (y : Fin n → Fin N) :
      starRef Γ M σ (Function.update W w z) a.1 y = starRef Γ M σ W a.1 y := by
    unfold starRef
    apply Finset.prod_congr rfl
    intro j hj
    exact congrArg (fun L : Law N => L.w (y j))
      (delRow_update_of_not_fullNames Γ M σ W (Γ.key (cubeFlip a.1 j))
        w target z (hnot j) hwneq)
  have hpred (y : Fin n → Fin N) :
      PredFail Γ M σ (Function.update W w z) a.1 y = PredFail Γ M σ W a.1 y := by
    unfold PredFail
    rw [hstarMarg, hstarRef]
  have hposterior (y : Fin n → Fin N) :
      evenRowAt Γ M σ (Function.update W w z) a y x = evenRowAt Γ M σ W a y x := by
    unfold evenRowAt
    rw [hstarLik x y, hstarMarg y]
  unfold evenStar
  apply Finset.sum_congr rfl
  intro y hy
  have hprod :
      (∏ j, cellRow Γ M σ (Function.update W w z)
        (Γ.key (cubeFlip a.1 j)) (y j)) =
        ∏ j, cellRow Γ M σ W (Γ.key (cubeFlip a.1 j)) (y j) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact cellRow_update_of_not_fullNames Γ M σ W
      (Γ.key (cubeFlip a.1 j)) w z (y j) (hnot j)
  rw [hprod, hpred, hposterior]

theorem evenStar_eq_off_far {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hGeom : GeomLocal Γ) (σ : Γ.Key → M.ι) (a : EvenRole n) (x : Fin N)
    (D : Finset Γ.Cell) (W W' : Γ.Cell → Fin N)
    (hAgree : ∀ c, c ∉ D → W c = W' c)
    (hFar : ∀ w ∈ D, 6 ≤ Γ.auxDist (Γ.key a.1).2 w.2)
    (hNe : ∀ w ∈ D, w ≠ Γ.key a.1) :
    evenStar Γ M σ W a x = evenStar Γ M σ W' a x := by
  classical
  induction D using Finset.induction_on generalizing W W' with
  | empty =>
      have hEq : W = W' := by
        funext c
        exact hAgree c (by simp)
      simpa [hEq]
  | @insert w D hwD ih =>
      let Wmid : Γ.Cell → Fin N := Function.update W w (W' w)
      have hFarW : 6 ≤ Γ.auxDist (Γ.key a.1).2 w.2 := hFar w (Finset.mem_insert_self _ _)
      have hNeW : w ≠ Γ.key a.1 := hNe w (Finset.mem_insert_self _ _)
      have hmid : evenStar Γ M σ Wmid a x = evenStar Γ M σ W a x := by
        exact evenStar_update_far Γ M hGeom σ W a x w (W' w) hFarW hNeW
      have hAgreeMid : ∀ c, c ∉ D → Wmid c = W' c := by
        intro c hc
        by_cases hcw : c = w
        · subst c
          simp [Wmid]
        · have hc' : c ∉ insert w D := by simp [hc, hcw]
          rw [show Wmid c = W c by simp [Wmid, hcw]]
          exact hAgree c hc'
      have hFarD : ∀ v ∈ D, 6 ≤ Γ.auxDist (Γ.key a.1).2 v.2 := by
        intro v hv
        exact hFar v (Finset.mem_insert_of_mem hv)
      have hNeD : ∀ v ∈ D, v ≠ Γ.key a.1 := by
        intro v hv
        exact hNe v (Finset.mem_insert_of_mem hv)
      calc
        evenStar Γ M σ W a x = evenStar Γ M σ Wmid a x := hmid.symm
        _ = evenStar Γ M σ W' a x := ih Wmid W' hAgreeMid hFarD hNeD

theorem pi_expect_singleton {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (P : ι → FinProb Ω) (a : ι) (f : Ω → ℝ) :
    (FinProb.pi P).expect (fun ω => f (ω a)) = (P a).expect f := by
  classical
  let S : Finset ι := {a}
  let aS : {i // i ∈ S} := ⟨a, by simp [S]⟩
  let e : (∀ i : {i // i ∈ S}, Ω) ≃ Ω := {
    toFun := fun z => z aS
    invFun := fun y _ => y
    left_inv := by
      intro z
      funext i
      have hi : i.1 = a :=
        Finset.mem_singleton.mp (show i.1 ∈ ({a} : Finset ι) from i.2)
      have hi' : i = aS := Subtype.ext hi
      rw [hi']
    right_inv := by intro y; rfl
  }
  let g : (∀ i : {i // i ∈ S}, Ω) → ℝ := fun z => f (z aS)
  have hproj : (fun ω : (∀ i, Ω) => g (fun i : {i // i ∈ S} => ω i.1)) =
      (fun ω : (∀ i, Ω) => f (ω a)) := by
    funext ω
    rfl
  rw [← hproj, FinProb.pi_marginal_expect P S g]
  unfold FinProb.expect
  have hweight (z : ∀ i : {i // i ∈ S}, Ω) :
      (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).w z = (P a).w (z aS) := by
    change (∏ i : {i // i ∈ S}, (P i.1).w (z i)) = _
    rw [Finset.prod_eq_single_of_mem aS (Finset.mem_univ aS)]
    intro i hi hia
    have hiVal : i.1 = a :=
      Finset.mem_singleton.mp (show i.1 ∈ ({a} : Finset ι) from i.2)
    exact (hia (Subtype.ext hiVal)).elim
  exact Fintype.sum_equiv e
    (fun z => (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).w z * g z)
    (fun y => (P a).w y * f y)
    (by intro z; simp [g, e, hweight])

theorem anchorChargeSmall (D₀ d : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d)
    (hd' : d < D₀ / 1000) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ^ 2 * xL D₀ n ≤ 1 / 2 := by
  let δ : ℝ := D₀ / 4 - 8 * d
  have hδ : 0 < δ := by
    dsimp [δ]
    have hD : 1000 * d < D₀ := by linarith
    linarith
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-δ)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hpow49 : Tendsto (fun n : ℕ => 49 * (n : ℝ) ^ (-δ)) atTop (nhds 0) := by
    simpa using hpow.const_mul 49
  have hsmall : ∀ᶠ n : ℕ in atTop, 49 * (n : ℝ) ^ (-δ) < 1 / 2 :=
    hpow49.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have htail : ∀ᶠ n : ℕ in atTop,
      ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ^ 2 * xL D₀ n ≤ 1 / 2 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hsmall] with n hn hnsmall
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hpowD : 1 ≤ (n : ℝ) ^ d := Real.one_le_rpow hnR1 hd.le
    have hpow4D : 1 ≤ (n : ℝ) ^ (4 * d) := Real.one_le_rpow hnR1 (by positivity)
    have hsceil : (gS d n : ℝ) ≤ (n : ℝ) ^ d + 1 := by
      dsimp [gS]
      exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ d)).le
    have hqceil : (gQ d n : ℝ) ≤ (n : ℝ) ^ (4 * d) + 1 := by
      dsimp [gQ]
      exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ (4 * d))).le
    have hs : (gS d n : ℝ) ≤ 2 * (n : ℝ) ^ d := by nlinarith [hsceil, hpowD]
    have hq : (gQ d n : ℝ) ≤ 2 * (n : ℝ) ^ (4 * d) := by nlinarith [hqceil, hpow4D]
    have hpowMon : (n : ℝ) ^ d ≤ (n : ℝ) ^ (4 * d) :=
      Real.rpow_le_rpow_of_exponent_le hnR1 (by nlinarith)
    have hR : ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ≤
        7 * (n : ℝ) ^ (4 * d) := by
      calc
        ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) =
            2 * (gS d n : ℝ) + (gQ d n : ℝ) + 1 := by push_cast; ring
        _ ≤ 7 * (n : ℝ) ^ (4 * d) := by
          nlinarith [hs, hq, hpowMon, hpow4D]
    have hRsq : ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ^ 2 ≤
        (7 * (n : ℝ) ^ (4 * d)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hR 2
    have hpowSq : ((n : ℝ) ^ (4 * d)) ^ 2 = (n : ℝ) ^ (8 * d) := by
      rw [← Real.rpow_mul_natCast hnR.le (4 * d) 2]
      congr 1
      ring
    have hcost : ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ^ 2 * xL D₀ n ≤
        49 * (n : ℝ) ^ (-δ) := by
      calc
        _ ≤ (7 * (n : ℝ) ^ (4 * d)) ^ 2 * xL D₀ n :=
          mul_le_mul_of_nonneg_right hRsq (Real.rpow_nonneg (by positivity) _)
        _ = 49 * (((n : ℝ) ^ (4 * d)) ^ 2 * (n : ℝ) ^ (-(D₀ / 4))) := by
          simp [xL]
          ring
        _ = 49 * ((n : ℝ) ^ (8 * d) * (n : ℝ) ^ (-(D₀ / 4))) := by
          rw [hpowSq]
        _ = 49 * (n : ℝ) ^ (8 * d + -(D₀ / 4)) := by
          rw [← Real.rpow_add hnR]
        _ = 49 * (n : ℝ) ^ (-δ) := by
          congr 1
          dsimp [δ]
          ring
    exact le_trans hcost hnsmall.le
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 htail
  exact ⟨n₀, fun n hn => hn₀ n hn⟩

theorem one_sub_mul_pow_lower (x : ℝ) (k : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (k : ℝ) * x ≤ (1 - x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hstep := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hx1)
      calc
        1 - (↑(k + 1) : ℝ) * x ≤ (1 - (k : ℝ) * x) * (1 - x) := by
          rw [Nat.cast_succ]
          nlinarith [mul_nonneg (Nat.cast_nonneg k) (sq_nonneg x)]
        _ ≤ (1 - x) ^ k * (1 - x) := hstep


end HypercubeRamsey.S07
