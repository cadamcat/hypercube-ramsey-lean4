import HypercubeRamsey.S04.CoreLemmas
import HypercubeRamsey.S03.NearProductInjection
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.Tools.ScatteredUnion
import HypercubeRamsey.Tools.CubeGeometry

namespace HypercubeRamsey.Lane_q_s04_load

open Classical
open Filter
open scoped BigOperators

private theorem joint_expect_le_product
    {R : Type*} [Fintype R] [DecidableEq R] {N : ℕ}
    (P : R → FinProb (Fin N)) (J : FinProb (R → Fin N))
    (S : Finset R) (B : ℝ) (hS : (S.card : ℝ) ≤ B)
    (hjoint : ∀ (S' : Finset R) (o : R → Fin N), (S'.card : ℝ) ≤ B →
      J.pr (fun f => ∀ u ∈ S', f u = o u) ≤
        2 * ∏ u ∈ S', (P u).w (o u))
    (g : (R → Fin N) → ℝ) (hg : ∀ f, 0 ≤ g f)
    (hdep : FinProb.DependsOn g S) :
    J.expect g ≤ 2 * (FinProb.pi P).expect g := by
  classical
  have hNE : Nonempty (R → Fin N) := by
    by_contra h
    have hE : IsEmpty (R → Fin N) := ⟨fun f => h ⟨f⟩⟩
    have hzero : (∑ f, J.w f) = 0 := by simp
    rw [J.sum_eq_one] at hzero
    norm_num at hzero
  let f₀ : R → Fin N := Classical.choice hNE
  let proj : (R → Fin N) → (∀ i : {u // u ∈ S}, Fin N) := fun f i => f i.1
  let ext : (∀ i : {u // u ∈ S}, Fin N) → R → Fin N := fun o u =>
    if hu : u ∈ S then o ⟨u, hu⟩ else f₀ u
  let gS : (∀ i : {u // u ∈ S}, Fin N) → ℝ := fun o => g (ext o)
  let Jm : FinProb (∀ i : {u // u ∈ S}, Fin N) := FinProb.map J proj
  let Qs : FinProb (∀ i : {u // u ∈ S}, Fin N) := FinProb.pi fun i => P i.1
  have hrepr (f : R → Fin N) : g f = gS (proj f) := by
    apply hdep f (ext (proj f))
    intro u hu
    simp [proj, ext, hu]
  have hmap (o : ∀ i : {u // u ∈ S}, Fin N) :
      Jm.w o = J.pr (fun f => ∀ u ∈ S, f u = ext o u) := by
    dsimp [Jm, FinProb.map, FinProb.pr]
    apply Finset.sum_congr rfl
    intro f hf
    have heq : (proj f = o) ↔ ∀ u ∈ S, f u = ext o u := by
      constructor
      · intro h u hu
        have hi := congrFun h ⟨u, hu⟩
        simpa [proj, ext, hu] using hi
      · intro h
        funext i
        simpa [proj, ext, i.2] using h i.1 i.2
    simp [heq]
  have hprod (o : ∀ i : {u // u ∈ S}, Fin N) :
      (∏ u ∈ S, (P u).w (ext o u)) = Qs.w o := by
    have hattach :
        (∏ i : {u // u ∈ S}, (P i.1).w (ext o i.1)) =
          ∏ u ∈ S, (P u).w (ext o u) := by
      exact Finset.prod_attach S (fun u => (P u).w (ext o u))
    rw [← hattach]
    simp [Qs, FinProb.pi, ext]
  have hbound (o : ∀ i : {u // u ∈ S}, Fin N) : Jm.w o ≤ 2 * Qs.w o := by
    rw [hmap, ← hprod]
    exact hjoint S (ext o) hS
  have hsum : Jm.expect gS ≤ 2 * Qs.expect gS := by
    unfold FinProb.expect
    calc
      (∑ o, Jm.w o * gS o) ≤ ∑ o, (2 * Qs.w o) * gS o := by
        apply Finset.sum_le_sum
        intro o ho
        exact mul_le_mul_of_nonneg_right (hbound o) (hg (ext o))
      _ = 2 * ∑ o, Qs.w o * gS o := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro o ho
        ring
  have hQ : (FinProb.pi P).expect (fun f => gS (proj f)) = Qs.expect gS := by
    simpa [proj, Qs] using (FinProb.pi_marginal_expect P S gS)
  have hQg : Qs.expect gS = (FinProb.pi P).expect g := by
    calc
      Qs.expect gS = (FinProb.pi P).expect (fun f => gS (proj f)) := hQ.symm
      _ = (FinProb.pi P).expect g := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro f hf
        rw [hrepr]
  calc
    J.expect g = Jm.expect gS := by
      calc
        J.expect g = J.expect (fun f => gS (proj f)) := by
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro f
          intro hf
          rw [hrepr]
        _ = Jm.expect gS := (FinProb.map_expect J proj gS).symm
    _ ≤ 2 * Qs.expect gS := hsum
    _ = 2 * (FinProb.pi P).expect g := by rw [hQg]

private theorem pi_expect_prod_of_disjoint
    {I R : Type*} [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]
    {N : ℕ} (P : R → FinProb (Fin N))
    (S : I → Finset R) (g : I → (R → Fin N) → ℝ)
    (hdep : ∀ i, FinProb.DependsOn (g i) (S i))
    (hdisj : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j → Disjoint (S i) (S j)) :
    (FinProb.pi P).expect (fun f => ∏ i, g i f) = ∏ i, (FinProb.pi P).expect (g i) := by
  classical
  let Q := FinProb.pi P
  have hInd (A : Finset I) :
      Q.expect (fun f => ∏ i ∈ A, g i f) = ∏ i ∈ A, Q.expect (g i) := by
    induction A using Finset.induction_on with
    | empty => simp [FinProb.expect_const]
    | @insert i A hi ih =>
      have hprodDep : FinProb.DependsOn (fun f => ∏ j ∈ A, g j f) (A.biUnion S) := by
        intro f f' hagree
        apply Finset.prod_congr rfl
        intro j hj
        apply hdep j
        intro u hu
        exact hagree u (Finset.mem_biUnion.mpr ⟨j, hj, hu⟩)
      have hsets : Disjoint (S i) (A.biUnion S) := by
        rw [Finset.disjoint_left]
        intro u hu hmem
        rcases Finset.mem_biUnion.mp hmem with ⟨j, hj, huj⟩
        have hij : i ≠ j := by
          intro heq
          subst j
          exact hi hj
        exact (Finset.disjoint_left.mp (hdisj i (Finset.mem_univ i) j (Finset.mem_univ j) hij)) hu huj
      have hsplit := FinProb.pi_expect_mul_of_disjoint P (g i)
        (fun f => ∏ j ∈ A, g j f) (S i) (A.biUnion S) (hdep i) hprodDep hsets
      calc
        Q.expect (fun f => ∏ j ∈ insert i A, g j f) =
            Q.expect (fun f => g i f * ∏ j ∈ A, g j f) := by
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro f hf
          have hprod : (∏ j ∈ insert i A, g j f) =
              g i f * ∏ j ∈ A, g j f := Finset.prod_insert hi
          exact congrArg (fun z => Q.w f * z) hprod
        _ = Q.expect (g i) * Q.expect (fun f => ∏ j ∈ A, g j f) := by
          simpa [Q] using hsplit
        _ = ∏ j ∈ insert i A, Q.expect (g j) := by
          rw [ih]
          have hprodExpect : (∏ j ∈ insert i A, Q.expect (g j)) =
              Q.expect (g i) * ∏ j ∈ A, Q.expect (g j) := Finset.prod_insert hi
          exact hprodExpect.symm
  simpa [Q] using hInd Finset.univ

private def nbrSet {n : ℕ} (a : HypercubeRamsey.S04.EvenRole n) : Finset (HypercubeRamsey.S04.OddRole n) :=
  Finset.univ.image (HypercubeRamsey.S04.oddNbr a)

private noncomputable def evenRead
    {β γ : ℝ} {G : HypercubeRamsey.Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (ω : HypercubeRamsey.S04.Prep M tag) (x : Fin N) (a : HypercubeRamsey.S04.EvenRole n)
    (f : HypercubeRamsey.S04.OddRole n → Fin N) : ℝ :=
  (N : ℝ) * HypercubeRamsey.S04.evenRowAt M tag ω a
    (HypercubeRamsey.S04.nbrLabels f a) x

private theorem evenRead_nonneg
    {β γ : ℝ} {G : HypercubeRamsey.Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (ω : HypercubeRamsey.S04.Prep M tag) (x : Fin N) (a : HypercubeRamsey.S04.EvenRole n)
    (f : HypercubeRamsey.S04.OddRole n → Fin N) : 0 ≤ evenRead M tag ω x a f := by
  unfold evenRead HypercubeRamsey.S04.evenRowAt
  cases hs : HypercubeRamsey.S04.sel M tag ω a.1 with
  | none => simp [hs]
  | some c =>
    simp only [hs, Option.elim_some]
    split_ifs <;> positivity

private theorem evenRead_depends
    {β γ : ℝ} {G : HypercubeRamsey.Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (ω : HypercubeRamsey.S04.Prep M tag) (x : Fin N) (a : HypercubeRamsey.S04.EvenRole n) :
    FinProb.DependsOn (evenRead M tag ω x a) (nbrSet a) := by
  intro f f' hagree
  unfold evenRead HypercubeRamsey.S04.nbrLabels
  congr 1
  apply congrArg (fun y => HypercubeRamsey.S04.evenRowAt M tag ω a y x)
  funext j
  apply hagree (HypercubeRamsey.S04.oddNbr a j)
  apply Finset.mem_image.mpr
  exact ⟨j, Finset.mem_univ j, rfl⟩

private theorem nbr_sets_disjoint
    {β γ : ℝ} {n m : ℕ}
    (a : Fin m → HypercubeRamsey.S04.EvenRole n)
    (hsep : HypercubeRamsey.S04.Sep β γ (fun i => (a i).1))
    {i j : Fin m} (hij : i ≠ j) : Disjoint (nbrSet (a i)) (nbrSet (a j)) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  rcases Finset.mem_image.mp hu with ⟨p, hp, rfl⟩
  rcases Finset.mem_image.mp hu' with ⟨q, hq, heq⟩
  have hleft : _root_.hammingDist (a i).1 (HypercubeRamsey.S04.oddNbr (a i) p).1 = 1 :=
    HypercubeRamsey.cubeFlip_adj (a i).1 p
  have hright : _root_.hammingDist (HypercubeRamsey.S04.oddNbr (a j) q).1 (a j).1 = 1 := by
    rw [_root_.hammingDist_comm]
    exact HypercubeRamsey.cubeFlip_adj (a j).1 q
  have hnear : _root_.hammingDist (a i).1 (a j).1 ≤ 2 := by
    calc
      _ ≤ _root_.hammingDist (a i).1 (HypercubeRamsey.S04.oddNbr (a i) p).1 +
          _root_.hammingDist (HypercubeRamsey.S04.oddNbr (a i) p).1 (a j).1 :=
        HypercubeRamsey.hammingDist_triangle _ _ _
      _ = 1 + 1 := by rw [heq] at hright; rw [hleft, hright]
      _ = 2 := by norm_num
  have hlarge := hsep i j hij
  have hloc : 2 ≤ 2 * HypercubeRamsey.S04.locR β γ n := by
    dsimp [HypercubeRamsey.S04.locR, HypercubeRamsey.S04.hd]
    omega
  change 2 * HypercubeRamsey.S04.locR β γ n < _root_.hammingDist (a i).1 (a j).1 at hlarge
  have hlarge' : 2 < _root_.hammingDist (a i).1 (a j).1 := lt_of_le_of_lt hloc hlarge
  exact (not_lt_of_ge hnear) hlarge'

theorem even_clock
    {β γ : ℝ} {G : HypercubeRamsey.Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (hgeo : HypercubeRamsey.S04.GeoCons M tag) :
    HypercubeRamsey.S04.EvenClock M tag := by
  classical
  intro ω J hpre hinj x m a hm hsep
  let P : HypercubeRamsey.S04.OddRole n → FinProb (Fin N) :=
    fun u => HypercubeRamsey.S04.oddDraw M tag ω u
  let Q : FinProb (HypercubeRamsey.S04.OddRole n → Fin N) := FinProb.pi P
  let T : Fin m → Finset (HypercubeRamsey.S04.OddRole n) := fun i => nbrSet (a i)
  let S : Finset (HypercubeRamsey.S04.OddRole n) := Finset.univ.biUnion T
  let F : (HypercubeRamsey.S04.OddRole n → Fin N) → ℝ :=
    fun f => ∏ i, evenRead M tag ω x (a i) f
  have hgood : ∀ u : HypercubeRamsey.S04.OddRole n, HypercubeRamsey.S04.OddOK M tag ω u :=
    (hgeo ω hpre.1).2
  have hrow (u : HypercubeRamsey.S04.OddRole n) (y : Fin N) :
      HypercubeRamsey.S04.oddRow M tag ω u y = (P u).w y := by
    simp [P, HypercubeRamsey.S04.oddRow, hgood u]
  have hjoint : ∀ (S' : Finset (HypercubeRamsey.S04.OddRole n))
      (o : HypercubeRamsey.S04.OddRole n → Fin N), (S'.card : ℝ) ≤ (n : ℝ) ^ 2 →
      J.pr (fun f => ∀ u ∈ S', f u = o u) ≤ 2 * ∏ u ∈ S', (P u).w (o u) := by
    intro S' o hcard
    simpa [hrow] using hinj.2 S' o hcard
  have hS_card : (S.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc
      (S.card : ℝ) ≤ ∑ i : Fin m, ((T i).card : ℝ) := by
        have hbiNat : S.card ≤ ∑ i : Fin m, (T i).card :=
          Finset.card_biUnion_le (s := Finset.univ) (t := T)
        exact_mod_cast hbiNat
      _ ≤ ∑ _i : Fin m, (n : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hcard : (T i).card ≤ n := by
          dsimp [T, nbrSet]
          calc
            (Finset.univ.image (HypercubeRamsey.S04.oddNbr (a i))).card ≤
                (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
            _ = n := by simp
        exact_mod_cast hcard
      _ = (m : ℝ) * (n : ℝ) := by simp
      _ ≤ (n : ℝ) ^ 2 := by
        have hmn : m * n ≤ n * n := Nat.mul_le_mul_right n hm
        exact_mod_cast (by simpa [pow_two] using hmn)
  have hFdep : FinProb.DependsOn F S := by
    intro f f' hagree
    apply Finset.prod_congr rfl
    intro i hi
    exact (evenRead_depends M tag ω x (a i)) f f' (by
      intro u hu
      exact hagree u (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hu⟩))
  have hFnonneg (f : HypercubeRamsey.S04.OddRole n → Fin N) : 0 ≤ F f := by
    apply Finset.prod_nonneg
    intro i hi
    exact evenRead_nonneg M tag ω x (a i) f
  have hdom : J.expect F ≤ 2 * Q.expect F :=
    joint_expect_le_product P J S ((n : ℝ) ^ 2) hS_card hjoint F hFnonneg hFdep
  have hfacdep : ∀ i, FinProb.DependsOn (evenRead M tag ω x (a i)) (T i) := by
    intro i
    simpa [T] using evenRead_depends M tag ω x (a i)
  have hdisj : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j → Disjoint (T i) (T j) := by
    intro i hi j hj hij
    exact nbr_sets_disjoint a hsep hij
  have hfactor : Q.expect F = ∏ i, Q.expect (evenRead M tag ω x (a i)) := by
    simpa [Q, F] using pi_expect_prod_of_disjoint P T
      (evenRead M tag ω x ∘ a) hfacdep hdisj
  have hmeans (i : Fin m) : Q.expect (evenRead M tag ω x (a i)) =
      (N : ℝ) * HypercubeRamsey.S04.evenMean M tag ω (a i) x := by
    change (FinProb.pi P).expect (fun f => (N : ℝ) *
      HypercubeRamsey.S04.evenRowAt M tag ω (a i) (HypercubeRamsey.S04.nbrLabels f (a i)) x) = _
    rw [FinProb.expect_smul]
    rfl
  calc
    J.expect F ≤ 2 * Q.expect F := hdom
    _ = 2 * ∏ i, (N : ℝ) * HypercubeRamsey.S04.evenMean M tag ω (a i) x := by
      rw [hfactor]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact hmeans i

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < 2 ^ n := pow_pos (by omega) _
    omega

private theorem eventually_small_poly_exp (b : ℝ) (hb : 0 < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (n : ℝ) ^ (2 : ℝ) * Real.exp (-b * n) < ε := by
  have hlim : Tendsto (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-b * x)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 b hb
  have hlimN := hlim.comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hlimN.eventually (Iio_mem_nhds hε))
  exact ⟨n₀, hn₀⟩

private theorem injection_thresholds (γ : ℝ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      1 ≤ n ∧
      (n : ℝ) ^ (2 : ℝ) * Real.exp (-((1 / 40 : ℝ) * Real.log 2) * n) < 1 ∧
      (n : ℝ) ^ (2 : ℝ) * Real.exp (-((1 / 25 : ℝ) * Real.log 2) * n) < Real.log 2 ∧
      (n : ℝ) ^ (γ - 1) < Real.log 2 / 40 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsize := eventually_small_poly_exp ((1 / 40 : ℝ) * Real.log 2)
    (mul_pos (by norm_num) hlog2) 1 (by norm_num)
  have herr := eventually_small_poly_exp ((1 / 25 : ℝ) * Real.log 2)
    (mul_pos (by norm_num) hlog2) (Real.log 2) hlog2
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ (γ - 1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hγ)).comp tendsto_natCast_atTop_atTop
    have h' : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 - γ))) atTop (nhds 0) := by
      have heq : (fun n : ℕ => (n : ℝ) ^ (-(1 - γ))) =ᶠ[atTop]
          ((fun x : ℝ => x ^ (-(1 - γ))) ∘ Nat.cast) := by
        filter_upwards [] with n
        rfl
      exact Tendsto.congr' heq h
    simpa only [show γ - 1 = -(1 - γ) by ring] using h'
  have hratioEv := Filter.eventually_atTop.1
    (hratio.eventually (Iio_mem_nhds (by positivity : 0 < Real.log 2 / 40)))
  obtain ⟨nSize, hSize⟩ := hsize
  obtain ⟨nErr, hErr⟩ := herr
  obtain ⟨nRatio, hRatio⟩ := hratioEv
  have hevent : ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧
      (n : ℝ) ^ (2 : ℝ) * Real.exp (-((1 / 40 : ℝ) * Real.log 2) * n) < 1 ∧
      (n : ℝ) ^ (2 : ℝ) * Real.exp (-((1 / 25 : ℝ) * Real.log 2) * n) < Real.log 2 ∧
      (n : ℝ) ^ (γ - 1) < Real.log 2 / 40 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ),
      Filter.eventually_atTop.2 ⟨nSize, hSize⟩,
      Filter.eventually_atTop.2 ⟨nErr, hErr⟩,
      Filter.eventually_atTop.2 ⟨nRatio, hRatio⟩] with n hn1 hnSize hnErr hnRatio
    exact ⟨hn1, hnSize, hnErr, hnRatio⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hevent
  exact ⟨n₀, hn₀⟩

theorem injection_exists
    (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, (2 : ℝ) ^ n ≤ N →
      ∀ {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour} {X Y : Finset (Fin N)}
        (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
        (tag : HypercubeRamsey.S04.Key β γ n → M.ι),
        HypercubeRamsey.S04.GeoCons M tag → HypercubeRamsey.S04.OddCap M tag →
        ∀ ω : HypercubeRamsey.S04.Prep M tag, HypercubeRamsey.S04.SPre M tag ω →
          ∃ J, HypercubeRamsey.S04.InjOK M tag ω J := by
  classical
  obtain ⟨d₀, hd₀⟩ := HypercubeRamsey.near_product_injection
  obtain ⟨nA, hnA⟩ := injection_thresholds γ hγ
  refine ⟨max d₀ nA, ?_⟩
  intro n hn N hN E G X Y M tag hgeo hcap ω hpre
  have hnA' : nA ≤ n := le_trans (Nat.le_max_right d₀ nA) hn
  have ⟨hn1, hsizeSmall, herrSmall, hratioSmall⟩ := hnA n hnA'
  have hNnat : 2 ^ n ≤ N := by exact_mod_cast hN
  have hdN : d₀ ≤ N := by
    calc
      d₀ ≤ n := le_trans (Nat.le_max_left d₀ nA) hn
      _ ≤ 2 ^ n := nat_le_two_pow n
      _ ≤ N := hNnat
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (by positivity : 0 < (2 : ℝ) ^ n) hN
  have hNbase : (2 : ℝ) ^ n ≤ (N : ℝ) := hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmallSize : (n : ℝ) ^ (2 : ℝ) < Real.exp ((1 / 40 : ℝ) * Real.log 2 * n) := by
    have hcancel : Real.exp (-((1 / 40 : ℝ) * Real.log 2) * n) *
        Real.exp ((1 / 40 : ℝ) * Real.log 2 * n) = 1 := by
      calc
        _ = Real.exp (-((1 / 40 : ℝ) * Real.log 2) * n +
            (1 / 40 : ℝ) * Real.log 2 * n) := by rw [← Real.exp_add]
        _ = Real.exp 0 := by congr 1 <;> ring
        _ = 1 := Real.exp_zero
    calc
      (n : ℝ) ^ (2 : ℝ) = ((n : ℝ) ^ (2 : ℝ) *
          Real.exp (-((1 / 40 : ℝ) * Real.log 2) * n)) *
          Real.exp ((1 / 40 : ℝ) * Real.log 2 * n) := by rw [mul_assoc, hcancel, mul_one]
      _ < 1 * Real.exp ((1 / 40 : ℝ) * Real.log 2 * n) :=
        mul_lt_mul_of_pos_right hsizeSmall (Real.exp_pos _)
      _ = Real.exp ((1 / 40 : ℝ) * Real.log 2 * n) := by ring
  have hpowSize : ((2 : ℝ) ^ n) ^ (1 / 40 : ℝ) =
      Real.exp ((1 / 40 : ℝ) * Real.log 2 * n) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    rw [Real.log_pow]
    congr 1
    push_cast
    ring
  have hNsize : (n : ℝ) ^ (2 : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) := by
    calc
      (n : ℝ) ^ (2 : ℝ) ≤ Real.exp ((1 / 40 : ℝ) * Real.log 2 * n) := hsmallSize.le
      _ = ((2 : ℝ) ^ n) ^ (1 / 40 : ℝ) := hpowSize.symm
      _ ≤ (N : ℝ) ^ (1 / 40 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hNbase (by norm_num)
  have hNratio : Real.log ((N : ℝ)) ≥ (n : ℝ) * Real.log 2 := by
    calc
      (n : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ n) := by rw [Real.log_pow]
      _ ≤ Real.log (N : ℝ) := Real.log_le_log (by positivity) hNbase
  have hmainExp : Real.exp (2 * (n : ℝ) ^ γ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
    have hpowRel : (n : ℝ) ^ γ = (n : ℝ) ^ (γ - 1) * (n : ℝ) := by
      rw [show γ = (γ - 1) + 1 by ring]
      simpa [Real.rpow_one] using (Real.rpow_add hnpos (γ - 1) 1)
    have hExponent : 2 * (n : ℝ) ^ γ ≤ (1 / 20 : ℝ) * (n : ℝ) * Real.log 2 := by
      rw [hpowRel]
      nlinarith [hratioSmall, hnpos]
    calc
      Real.exp (2 * (n : ℝ) ^ γ) ≤
          Real.exp ((1 / 20 : ℝ) * (n : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hExponent
      _ ≤ Real.exp ((1 / 20 : ℝ) * Real.log (N : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [hNratio])
      _ = (N : ℝ) ^ (1 / 20 : ℝ) := by
        rw [Real.rpow_def_of_pos hNpos]
        congr 1
        ring
  have hpowRatio : (N : ℝ) ^ (1 / 20 : ℝ) / (N : ℝ) = (N : ℝ) ^ (-(0.95 : ℝ)) := by
    have hinv : (N : ℝ)⁻¹ = (N : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg hNpos.le 1, Real.rpow_one]
    calc
      (N : ℝ) ^ (1 / 20 : ℝ) / (N : ℝ) =
          (N : ℝ) ^ (1 / 20 : ℝ) * (N : ℝ) ^ (-1 : ℝ) := by rw [div_eq_mul_inv, hinv]
      _ = (N : ℝ) ^ ((1 / 20 : ℝ) + (-1 : ℝ)) := (Real.rpow_add hNpos _ _).symm
      _ = (N : ℝ) ^ (-(0.95 : ℝ)) := by congr 1 <;> norm_num
  let P : HypercubeRamsey.S04.OddRole n → FinProb (Fin N) :=
    fun u => HypercubeRamsey.S04.oddDraw M tag ω u
  have hodd : ∀ u : HypercubeRamsey.S04.OddRole n, HypercubeRamsey.S04.OddOK M tag ω u :=
    (hgeo ω hpre.1).2
  have hrow (u : HypercubeRamsey.S04.OddRole n) (y : Fin N) :
      HypercubeRamsey.S04.oddRow M tag ω u y = (P u).w y := by
    simp [P, HypercubeRamsey.S04.oddRow, hodd u]
  have hAtom : ∀ u y, HypercubeRamsey.labMarg (P u) id y ≤ (N : ℝ) ^ (-(0.95 : ℝ)) := by
    intro u y
    have hcap' := hcap ω u y
    rw [show HypercubeRamsey.labMarg (P u) id y = (P u).w y by simp [HypercubeRamsey.labMarg]]
    calc
      (P u).w y ≤ Real.exp (2 * (n : ℝ) ^ γ) / (N : ℝ) := by
        apply (le_div_iff₀ hNpos).2
        rw [← hrow u y]
        nlinarith [hcap']
      _ ≤ (N : ℝ) ^ (1 / 20 : ℝ) / (N : ℝ) :=
        div_le_div_of_nonneg_right hmainExp hNpos.le
      _ = (N : ℝ) ^ (-(0.95 : ℝ)) := hpowRatio
  have hLoad : ∀ y, ∑ u : HypercubeRamsey.S04.OddRole n,
      HypercubeRamsey.labMarg (P u) id y ≤ 0.4 := by
    intro y
    calc
      ∑ u : HypercubeRamsey.S04.OddRole n, HypercubeRamsey.labMarg (P u) id y =
          ∑ u : HypercubeRamsey.S04.OddRole n, HypercubeRamsey.S04.oddRow M tag ω u y := by
            apply Finset.sum_congr rfl
            intro u hu
            simp [HypercubeRamsey.labMarg, hrow]
      _ = HypercubeRamsey.S04.oddCol M tag ω y := by simp [HypercubeRamsey.S04.oddCol]
      _ ≤ 0.4 := (hpre.2 y).trans (by norm_num)
  obtain ⟨J, hJinj, _hJmarg, hJjoint⟩ :=
    hd₀ N hdN (lab := fun _ => id) (p := P) hAtom hLoad
  refine ⟨J, ?_⟩
  constructor
  · intro f hf
    exact hJinj f hf
  · intro S o hS
    have hSreal : (S.card : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
      simpa [Real.rpow_natCast] using hS
    have hS' : (S.card : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) := le_trans hSreal hNsize
    have hS025 : (S.card : ℝ) ≤ (N : ℝ) ^ (0.025 : ℝ) := by
      simpa only [show (0.025 : ℝ) = 1 / 40 by norm_num] using hS'
    have hErrArg : (N : ℝ) ^ (-(1 / 25 : ℝ)) * (S.card : ℝ) ≤ Real.log 2 := by
      have hneg : (N : ℝ) ^ (-(1 / 25 : ℝ)) ≤ ((2 : ℝ) ^ n) ^ (-(1 / 25 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hNbase (by norm_num)
      have hnegEq : ((2 : ℝ) ^ n) ^ (-(1 / 25 : ℝ)) =
          Real.exp (-((1 / 25 : ℝ) * Real.log 2) * n) := by
        rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
        congr 1
        push_cast
        ring
      calc
        (N : ℝ) ^ (-(1 / 25 : ℝ)) * (S.card : ℝ) ≤
            ((2 : ℝ) ^ n) ^ (-(1 / 25 : ℝ)) * (n : ℝ) ^ (2 : ℝ) := by
              exact mul_le_mul hneg hSreal (by positivity) (Real.rpow_nonneg (by positivity) _)
        _ = (n : ℝ) ^ (2 : ℝ) * Real.exp (-((1 / 25 : ℝ) * Real.log 2) * n) := by
              rw [hnegEq]; ring
        _ ≤ Real.log 2 := le_of_lt herrSmall
    have hExp : Real.exp ((N : ℝ) ^ (-(1 / 25 : ℝ)) * (S.card : ℝ)) ≤ 2 := by
      calc
        Real.exp ((N : ℝ) ^ (-(1 / 25 : ℝ)) * (S.card : ℝ)) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr hErrArg
        _ = 2 := Real.exp_log (by norm_num)
    have hprod : 0 ≤ ∏ u ∈ S, (P u).w (o u) :=
      Finset.prod_nonneg fun u hu => (P u).nonneg _
    calc
      J.pr (fun f => ∀ u ∈ S, f u = o u) ≤
          Real.exp ((N : ℝ) ^ (-(1 / 25 : ℝ)) * (S.card : ℝ)) *
            ∏ u ∈ S, (P u).w (o u) := by
              simpa only [show (-(0.04 : ℝ)) = -(1 / 25 : ℝ) by norm_num,
                show (0.025 : ℝ) = 1 / 40 by norm_num] using hJjoint S o hS025
      _ ≤ 2 * ∏ u ∈ S, (P u).w (o u) :=
        mul_le_mul_of_nonneg_right hExp hprod
      _ = 2 * ∏ u ∈ S, HypercubeRamsey.S04.oddRow M tag ω u (o u) := by
        congr 1
        apply Finset.prod_congr rfl
        intro u hu
        exact (hrow u (o u)).symm

private theorem scale_index_exists_local (M R target : ℕ) (hM : 2 ≤ M) (hR : 1 ≤ R) :
    ∃ i : ℕ, target ≤ M ^ i * R := by
  induction target with
  | zero => exact ⟨0, by simp⟩
  | succ target ih =>
      obtain ⟨i, hi⟩ := ih
      have hx : 1 ≤ M ^ i * R := by
        have hM0 : 0 < M := by omega
        have hpow : 0 < M ^ i := pow_pos hM0 _
        exact Nat.mul_pos hpow (by omega)
      have hstep : M ^ i * R + 1 ≤ M * (M ^ i * R) := by
        calc
          M ^ i * R + 1 ≤ 2 * (M ^ i * R) := by omega
          _ ≤ M * (M ^ i * R) := Nat.mul_le_mul_right _ hM
      refine ⟨i + 1, ?_⟩
      calc
        target + 1 ≤ M ^ i * R + 1 := Nat.succ_le_succ hi
        _ ≤ M * (M ^ i * R) := hstep
        _ = M ^ (i + 1) * R := by rw [pow_succ]; ring

private theorem eventually_rpow_gt_const (a b : ℝ) (ha : 0 < a) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, b < (n : ℝ) ^ a := by
  have h := (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (h.eventually (Filter.eventually_gt_atTop b))
  exact ⟨n₀, hn₀⟩

private theorem topScale_small (σ ζ : ℝ) (hσ : 0 < σ) (hζ : 0 < ζ)
    (hσζ : σ < ζ / 2) (hζ1 : ζ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (HypercubeRamsey.topScale n σ ζ : ℝ) ≤
      (n : ℝ) ^ (1 - ζ / 2) := by
  let α : ℝ := 1 - ζ / 2
  let ε : ℝ := α / 4
  have hα : 0 < α := by dsimp [α]; linarith
  have hε : 0 < ε := div_pos hα (by norm_num)
  have hδ : 0 < ζ / 2 - σ := by linarith
  have hRpow := eventually_rpow_gt_const (2 * ε) (max (4 / ε ^ 2) 4)
    (mul_pos (by norm_num) hε)
  have hSpow := eventually_rpow_gt_const σ 3 hσ
  have hDpow := eventually_rpow_gt_const (ζ / 2 - σ) 4 hδ
  have hLpow := eventually_rpow_gt_const (ζ / 8) 12 (by positivity)
  have hZpow := eventually_rpow_gt_const (1 - ζ) 1 (by linarith)
  have hRpowE : ∀ᶠ n : ℕ in atTop, max (4 / ε ^ 2) 4 < (n : ℝ) ^ (2 * ε) :=
    Filter.eventually_atTop.2 hRpow
  have hSpowE : ∀ᶠ n : ℕ in atTop, 3 < (n : ℝ) ^ σ := Filter.eventually_atTop.2 hSpow
  have hDpowE : ∀ᶠ n : ℕ in atTop, 4 < (n : ℝ) ^ (ζ / 2 - σ) :=
    Filter.eventually_atTop.2 hDpow
  have hLpowE : ∀ᶠ n : ℕ in atTop, 12 < (n : ℝ) ^ (ζ / 8) :=
    Filter.eventually_atTop.2 hLpow
  have hZpowE : ∀ᶠ n : ℕ in atTop, 1 < (n : ℝ) ^ (1 - ζ) :=
    Filter.eventually_atTop.2 hZpow
  have hEvent : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ max (4 / ε ^ 2) 4 < (n : ℝ) ^ (2 * ε) ∧
      3 < (n : ℝ) ^ σ ∧ 4 < (n : ℝ) ^ (ζ / 2 - σ) ∧
      12 < (n : ℝ) ^ (ζ / 8) ∧ 1 < (n : ℝ) ^ (1 - ζ) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ), hRpowE, hSpowE, hDpowE, hLpowE, hZpowE]
      with n hn2 hRlarge hSlarge hDlarge hLlarge hZlarge
    exact ⟨hn2, hRlarge, hSlarge, hDlarge, hLlarge, hZlarge⟩
  obtain ⟨nBase, hBase⟩ := Filter.eventually_atTop.1 hEvent
  refine ⟨nBase, ?_⟩
  intro n hn
  rcases hBase n hn with ⟨hn2, hRlarge, hSlarge, hDlarge, hLlarge, hZlarge⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnσ : 3 < (n : ℝ) ^ σ := hSlarge
  have hnζ : 1 < (n : ℝ) ^ (1 - ζ) := hZlarge
  let R0 : ℕ := max 1 (Nat.ceil (Real.log (n : ℝ) ^ 2))
  let M : ℕ := max 2 (Nat.ceil ((n : ℝ) ^ σ))
  let target : ℕ := Nat.ceil ((n : ℝ) ^ (1 - ζ))
  have hR0small : (R0 : ℝ) ≤ (n : ℝ) ^ α := by
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnOne
    have hlog := Real.log_le_rpow_div (by positivity : 0 ≤ (n : ℝ)) hε
    have hlogSq : (Real.log (n : ℝ)) ^ 2 ≤
        (n : ℝ) ^ (2 * ε) / ε ^ 2 := by
      have hpow := pow_le_pow_left₀ hlog0 hlog 2
      have hEq : ((n : ℝ) ^ ε / ε) ^ 2 = (n : ℝ) ^ (2 * ε) / ε ^ 2 := by
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
        congr 1
        ring
      simpa [hEq] using hpow
    have hceil : (Nat.ceil (Real.log (n : ℝ) ^ 2) : ℝ) ≤
        (Real.log (n : ℝ)) ^ 2 + 1 := (Nat.ceil_lt_add_one (sq_nonneg _)).le
    have hmaxNat : R0 ≤ Nat.ceil (Real.log (n : ℝ) ^ 2) + 1 := by
      dsimp [R0]
      omega
    have hR0log : (R0 : ℝ) ≤ (n : ℝ) ^ (2 * ε) / ε ^ 2 + 2 := by
      have hmaxReal : (R0 : ℝ) ≤ (Nat.ceil (Real.log (n : ℝ) ^ 2) : ℝ) + 1 := by
        exact_mod_cast hmaxNat
      calc
        (R0 : ℝ) ≤ (Nat.ceil (Real.log (n : ℝ) ^ 2) : ℝ) + 1 := hmaxReal
        _ ≤ (Real.log (n : ℝ)) ^ 2 + 2 := by linarith [hceil]
        _ ≤ (n : ℝ) ^ (2 * ε) / ε ^ 2 + 2 := by linarith [hlogSq]
    have hT : max (4 / ε ^ 2) 4 < (n : ℝ) ^ (2 * ε) := hRlarge
    have hR0T : (n : ℝ) ^ (2 * ε) / ε ^ 2 + 2 ≤ ((n : ℝ) ^ (2 * ε)) ^ 2 := by
      have hT1 : 4 / ε ^ 2 ≤ (n : ℝ) ^ (2 * ε) := le_of_lt (le_max_left _ _ |>.trans_lt hT)
      have hT2 : 4 ≤ (n : ℝ) ^ (2 * ε) := le_of_lt (le_max_right _ _ |>.trans_lt hT)
      have hInv : 1 / ε ^ 2 ≤ (n : ℝ) ^ (2 * ε) / 4 := by
        calc
          1 / ε ^ 2 = (4 / ε ^ 2) / 4 := by ring
          _ ≤ (n : ℝ) ^ (2 * ε) / 4 := div_le_div_of_nonneg_right hT1 (by norm_num)
      have hDiv : (n : ℝ) ^ (2 * ε) / ε ^ 2 ≤
          ((n : ℝ) ^ (2 * ε)) ^ 2 / 4 := by
        calc
          (n : ℝ) ^ (2 * ε) / ε ^ 2 =
              (n : ℝ) ^ (2 * ε) * (1 / ε ^ 2) := by ring
          _ ≤ (n : ℝ) ^ (2 * ε) * ((n : ℝ) ^ (2 * ε) / 4) :=
            mul_le_mul_of_nonneg_left hInv (by positivity)
          _ = ((n : ℝ) ^ (2 * ε)) ^ 2 / 4 := by ring
      nlinarith [hDiv, hT2]
    have hPowEq : ((n : ℝ) ^ (2 * ε)) ^ 2 = (n : ℝ) ^ α := by
      calc
        ((n : ℝ) ^ (2 * ε)) ^ 2 = (n : ℝ) ^ ((2 * ε) * 2) := by
          calc
            ((n : ℝ) ^ (2 * ε)) ^ 2 = ((n : ℝ) ^ (2 * ε)) ^ (2 : ℝ) :=
              (Real.rpow_natCast ((n : ℝ) ^ (2 * ε)) 2).symm
            _ = (n : ℝ) ^ ((2 * ε) * 2) := (Real.rpow_mul hnpos.le _ _).symm
        _ = (n : ℝ) ^ α := by rw [show (2 * ε) * 2 = α by dsimp [α, ε]; ring]
    exact (hR0log.trans (hR0T.trans_eq hPowEq))
  have hM : (M : ℝ) ≤ 2 * (n : ℝ) ^ σ := by
    have hceilLe : (2 : ℝ) ≤ (Nat.ceil ((n : ℝ) ^ σ) : ℝ) := by
      calc
        2 ≤ (n : ℝ) ^ σ := by linarith
        _ ≤ (Nat.ceil ((n : ℝ) ^ σ) : ℝ) := Nat.le_ceil _
    have hM_eq : M = Nat.ceil ((n : ℝ) ^ σ) := by
      dsimp [M]
      exact max_eq_right (by exact_mod_cast hceilLe)
    rw [hM_eq]
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ σ)
    have hpowOne : 1 ≤ (n : ℝ) ^ σ := by linarith
    exact le_of_lt (by linarith)
  have htarget : (target : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) := by
    dsimp [target]
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ (1 - ζ))
    have hpowOne : 1 ≤ (n : ℝ) ^ (1 - ζ) := by linarith
    exact le_of_lt (by linarith)
  let Hgood : ∃ i : ℕ, target ≤ M ^ i * R0 :=
    scale_index_exists_local M R0 target (by dsimp [M]; omega) (by dsimp [R0]; omega)
  let i : ℕ := Nat.find Hgood
  have hiSpec : target ≤ M ^ i * R0 := by exact Nat.find_spec Hgood
  have htopEq : HypercubeRamsey.topScale n σ ζ = M ^ i * R0 := by
    dsimp [HypercubeRamsey.topScale, M, R0, target, i, Hgood]
  by_cases hi0 : i = 0
  · rw [htopEq, hi0, pow_zero, one_mul]
    exact hR0small
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    have hprev : M ^ (i - 1) * R0 < target := by
      have hnot := Nat.find_min Hgood (Nat.sub_lt hipos one_pos)
      exact lt_of_not_ge hnot
    have htopNat : M ^ i * R0 ≤ M * target := by
      have hi1 : 1 ≤ i := by omega
      have hiEq : i - 1 + 1 = i := Nat.sub_add_cancel hi1
      have hpowEq : M ^ i = M ^ (i - 1 + 1) := congrArg (fun k : ℕ => M ^ k) hiEq.symm
      calc
        M ^ i * R0 = M * (M ^ (i - 1) * R0) := by
          calc
            M ^ i * R0 = M ^ (i - 1 + 1) * R0 := congrArg (fun k : ℕ => k * R0) hpowEq
            _ = (M ^ (i - 1) * M) * R0 := by rw [pow_succ]
            _ = M * (M ^ (i - 1) * R0) := by ring
        _ ≤ M * target := Nat.mul_le_mul_left M hprev.le
    have htop : (HypercubeRamsey.topScale n σ ζ : ℝ) ≤
        4 * (n : ℝ) ^ (1 - ζ + σ) := by
      rw [htopEq]
      calc
        (M ^ i * R0 : ℕ) = (M : ℝ) ^ i * (R0 : ℝ) := by norm_cast
        _ ≤ (M : ℝ) * (target : ℝ) := by
          exact_mod_cast htopNat
        _ ≤ 4 * (n : ℝ) ^ (1 - ζ + σ) := by
          calc
            (M : ℝ) * (target : ℝ) ≤
                (2 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ (1 - ζ)) :=
              mul_le_mul hM htarget (by positivity) (by positivity)
            _ = 4 * ((n : ℝ) ^ σ * (n : ℝ) ^ (1 - ζ)) := by ring
            _ = 4 * (n : ℝ) ^ (σ + (1 - ζ)) := by rw [← Real.rpow_add hnpos]
            _ = 4 * (n : ℝ) ^ (1 - ζ + σ) := by
              rw [show σ + (1 - ζ) = 1 - ζ + σ by ring]
    have htopSmall : 4 * (n : ℝ) ^ (1 - ζ + σ) ≤ (n : ℝ) ^ α := by
      let δ : ℝ := ζ / 2 - σ
      have hδ : 0 < δ := by dsimp [δ]; linarith
      have hDlarge : 4 ≤ (n : ℝ) ^ δ := by
        dsimp [δ]
        exact le_of_lt hDlarge
      have hmul := mul_le_mul_of_nonneg_right hDlarge
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)) (1 - ζ + σ))
      calc
        4 * (n : ℝ) ^ (1 - ζ + σ) ≤
            (n : ℝ) ^ δ * (n : ℝ) ^ (1 - ζ + σ) := hmul
        _ = (n : ℝ) ^ (δ + (1 - ζ + σ)) := by rw [← Real.rpow_add hnpos]
        _ = (n : ℝ) ^ α := by congr 1 <;> dsimp [δ, α] <;> ring
    exact htop.trans htopSmall

private theorem binEntropy_upper_rpow {x δ : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    Real.binEntropy x ≤ (δ⁻¹ + 1) * x ^ (1 - δ) := by
  by_cases hx0 : x = 0
  · have hexp : 0 < 1 - δ := by linarith
    simp [hx0, Real.binEntropy_zero, Real.zero_rpow (ne_of_gt hexp)]
  by_cases hxOne : x = 1
  · simp [hxOne, Real.binEntropy_one]
    positivity
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hypos : 0 < 1 - x := by rcases lt_or_eq_of_le hx1 with h | h <;> simp_all
  have hlog := Real.log_le_rpow_div (inv_nonneg.mpr hxpos.le) hδ
  have hinvPow : x⁻¹ ^ δ = x ^ (-δ) := (Real.rpow_neg_eq_inv_rpow x δ).symm
  have hfirst : x * Real.log x⁻¹ ≤ δ⁻¹ * x ^ (1 - δ) := by
    calc
      x * Real.log x⁻¹ ≤ x * ((x⁻¹) ^ δ / δ) :=
        mul_le_mul_of_nonneg_left hlog hx
      _ = δ⁻¹ * x ^ (1 - δ) := by
        rw [div_eq_mul_inv, hinvPow]
        have heq : x * x ^ (-δ) = x ^ (1 - δ) := by
          calc
            x * x ^ (-δ) = x ^ (1 : ℝ) * x ^ (-δ) := by rw [Real.rpow_one]
            _ = x ^ (1 + (-δ)) := (Real.rpow_add hxpos 1 (-δ)).symm
            _ = x ^ (1 - δ) := by congr 1 <;> ring
        calc
          x * (x ^ (-δ) * δ⁻¹) = δ⁻¹ * (x * x ^ (-δ)) := by ring
          _ = δ⁻¹ * x ^ (1 - δ) := by rw [heq]
  have hlog' := Real.log_le_sub_one_of_pos (inv_pos.mpr hypos)
  have hsecond : (1 - x) * Real.log (1 - x)⁻¹ ≤ x := by
    calc
      (1 - x) * Real.log (1 - x)⁻¹ ≤ (1 - x) * ((1 - x)⁻¹ - 1) :=
        mul_le_mul_of_nonneg_left hlog' (by linarith)
      _ = x := by field_simp [ne_of_gt hypos] <;> ring
  have hpow : x ≤ x ^ (1 - δ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hxpos hx1 (by linarith : 1 - δ ≤ 1))
  unfold Real.binEntropy
  calc
    x * Real.log x⁻¹ + (1 - x) * Real.log (1 - x)⁻¹ ≤
        δ⁻¹ * x ^ (1 - δ) + x := add_le_add hfirst hsecond
    _ ≤ δ⁻¹ * x ^ (1 - δ) + x ^ (1 - δ) := by
      have hcoeff : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
      have hscaled := mul_le_mul_of_nonneg_left hpow hcoeff
      linarith
    _ = (δ⁻¹ + 1) * x ^ (1 - δ) := by ring

private theorem locR_near_radius_small (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
  (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, 1 ≤ n ∧
      (2 * HypercubeRamsey.S04.locR β γ n : ℝ) ≤
        (n : ℝ) ^ (1 - HypercubeRamsey.S04.zetaH β γ / 4) := by
  have hω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have hω' := HypercubeRamsey.S04.omega4_lt hβ hβγ
  let ζ := HypercubeRamsey.S04.zetaH β γ
  let σ := HypercubeRamsey.S04.sigmaH β γ
  have hζ : 0 < ζ := by dsimp [ζ, HypercubeRamsey.S04.zetaH,
      HypercubeRamsey.S04.b0H, HypercubeRamsey.S04.bH]; positivity
  have hζ1 : ζ < 1 := by
    dsimp [ζ, HypercubeRamsey.S04.zetaH, HypercubeRamsey.S04.b0H,
      HypercubeRamsey.S04.bH]
    linarith
  have hσ : 0 < σ := by dsimp [σ, HypercubeRamsey.S04.sigmaH]; positivity
  have hσζ : σ < ζ / 2 := by dsimp [σ, ζ, HypercubeRamsey.S04.sigmaH]; linarith
  have hρ : HypercubeRamsey.S04.rhoH β γ = 2 * ζ := by
    dsimp [ζ, HypercubeRamsey.S04.rhoH, HypercubeRamsey.S04.zetaH,
      HypercubeRamsey.S04.b0H, HypercubeRamsey.S04.bH]
    ring
  obtain ⟨ntop, htop⟩ := topScale_small σ ζ hσ hζ hσζ hζ1
  obtain ⟨nabs, habs⟩ := eventually_rpow_gt_const (ζ / 4) 18 (by positivity)
  refine ⟨max (max ntop nabs) 1, ?_⟩
  intro n hn
  have hnTop : ntop ≤ n := by omega
  have hnAbs : nabs ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hbase : 0 ≤ 1 - ζ / 2 := by linarith
  have htop' : (HypercubeRamsey.topScale n σ ζ : ℝ) ≤ (n : ℝ) ^ (1 - ζ / 2) :=
    htop n hnTop
  have hrad : (HypercubeRamsey.S04.radius β γ n : ℝ) ≤ (n : ℝ) ^ (1 - ζ / 2) := by
    have hfloor : (HypercubeRamsey.S04.radius β γ n : ℝ) ≤
        (n : ℝ) ^ (1 - HypercubeRamsey.S04.rhoH β γ) := by
      exact Nat.floor_le (by positivity)
    rw [hρ] at hfloor
    exact hfloor.trans (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith))
  have hpowOne : 1 ≤ (n : ℝ) ^ (1 - ζ / 2) := by
    calc
      1 = (n : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ (1 - ζ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
  have hRlong : (HypercubeRamsey.S04.hd β γ n).Rlong =
      4 * HypercubeRamsey.S04.topH β γ n := by
    simp [HypercubeRamsey.S04.hd, HypercubeRamsey.HDParams.Rlong]
  have hloc : (HypercubeRamsey.S04.locR β γ n : ℝ) ≤
      5 * (n : ℝ) ^ (1 - ζ / 2) + 4 := by
    rw [show HypercubeRamsey.S04.locR β γ n =
        4 * HypercubeRamsey.S04.topH β γ n + HypercubeRamsey.S04.radius β γ n + 4 by
          simp [HypercubeRamsey.S04.locR, hRlong]]
    push_cast
    have htopH : (HypercubeRamsey.S04.topH β γ n : ℝ) ≤
        (n : ℝ) ^ (1 - ζ / 2) := by simpa [σ, ζ, HypercubeRamsey.S04.topH] using htop'
    nlinarith [htopH, hrad]
  have hnear18 : (2 * HypercubeRamsey.S04.locR β γ n : ℝ) ≤
      18 * (n : ℝ) ^ (1 - ζ / 2) := by nlinarith [hloc, hpowOne]
  have hlarge := habs n hnAbs
  have hlarge' : 18 ≤ (n : ℝ) ^ (ζ / 4) := le_of_lt hlarge
  refine ⟨hn1, ?_⟩
  calc
    (2 * HypercubeRamsey.S04.locR β γ n : ℝ) ≤
        18 * (n : ℝ) ^ (1 - ζ / 2) := hnear18
    _ ≤ (n : ℝ) ^ (ζ / 4) * (n : ℝ) ^ (1 - ζ / 2) :=
      mul_le_mul_of_nonneg_right hlarge' (Real.rpow_nonneg hnpos.le _)
    _ = (n : ℝ) ^ (1 - ζ / 4) := by
      rw [← Real.rpow_add hnpos]
      congr 1 <;> ring

private theorem evenRole_card_eq {n : ℕ} (hn : 0 < n) :
    Fintype.card (HypercubeRamsey.S04.EvenRole n) = 2 ^ (n - 1) := by
  classical
  have hcard : Fintype.card (HypercubeRamsey.S04.EvenRole n) =
      (HypercubeRamsey.evenRoleSet n).card := by
    simpa [HypercubeRamsey.S04.EvenRole, HypercubeRamsey.evenRoleSet] using
      (Fintype.card_subtype (fun v : OAI.HypercubeRamsey.CubeVertex n =>
        HypercubeRamsey.IsEvenRole v))
  rw [hcard]
  exact (HypercubeRamsey.parity_class_card hn).1

private theorem oddRole_card_eq {n : ℕ} (hn : 0 < n) :
    Fintype.card (HypercubeRamsey.S04.OddRole n) = 2 ^ (n - 1) := by
  classical
  have hsub : Fintype.card (HypercubeRamsey.S04.OddRole n) =
      (Finset.univ.filter fun v : OAI.HypercubeRamsey.CubeVertex n =>
        ¬ HypercubeRamsey.IsEvenRole v).card := by
    simpa [HypercubeRamsey.S04.OddRole] using
      (Fintype.card_subtype (fun v : OAI.HypercubeRamsey.CubeVertex n =>
        ¬ HypercubeRamsey.IsEvenRole v))
  have hset : (Finset.univ.filter fun v : OAI.HypercubeRamsey.CubeVertex n =>
        ¬ HypercubeRamsey.IsEvenRole v) =
      Finset.univ \ HypercubeRamsey.evenRoleSet n := by
    ext v
    simp [HypercubeRamsey.evenRoleSet]
  rw [hsub, hset]
  exact (HypercubeRamsey.parity_class_card hn).2

private theorem ballV_eq_hammingBall {n : ℕ} (v : OAI.HypercubeRamsey.CubeVertex n) (R : ℕ) :
    HypercubeRamsey.S04.ballV v R = HypercubeRamsey.hammingBall v R := by
  ext w
  simp [HypercubeRamsey.S04.ballV, HypercubeRamsey.hammingBall,
    HypercubeRamsey.hammingDist, _root_.hammingDist]

private theorem ballV_volume_bound {n R : ℕ} (hn : 0 < n) (hR : R ≤ n / 2)
    (v : OAI.HypercubeRamsey.CubeVertex n) :
    (HypercubeRamsey.S04.ballV v R).card ≤
      Real.exp (Real.binEntropy ((R : ℝ) / n) * n) := by
  rw [ballV_eq_hammingBall]
  exact HypercubeRamsey.hammingBall_volume_bound hn hR v

private noncomputable def oddNearSet {n : ℕ} (R : ℕ) (u : HypercubeRamsey.S04.OddRole n) :
    Finset (HypercubeRamsey.S04.OddRole n) :=
  Finset.univ.filter fun v => v.1 ∈ HypercubeRamsey.S04.ballV u.1 R

private noncomputable def evenNearSet {n : ℕ} (R : ℕ) (a : HypercubeRamsey.S04.EvenRole n) :
    Finset (HypercubeRamsey.S04.EvenRole n) :=
  Finset.univ.filter fun b => b.1 ∈ HypercubeRamsey.S04.ballV a.1 R

private theorem oddNearSet_card_le {n R : ℕ} (u : HypercubeRamsey.S04.OddRole n) :
    (oddNearSet R u).card ≤ (HypercubeRamsey.S04.ballV u.1 R).card := by
  classical
  have hsub : (oddNearSet R u).image Subtype.val ⊆ HypercubeRamsey.S04.ballV u.1 R := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    exact (Finset.mem_filter.mp hw).2
  calc
    (oddNearSet R u).card = ((oddNearSet R u).image Subtype.val).card := by
      symm
      exact Finset.card_image_of_injective _ Subtype.val_injective
    _ ≤ (HypercubeRamsey.S04.ballV u.1 R).card := Finset.card_le_card hsub

private theorem oddNearSet_mem_iff {n R : ℕ} (u v : HypercubeRamsey.S04.OddRole n) :
    v ∈ oddNearSet R u ↔ _root_.hammingDist u.1 v.1 ≤ R := by
  simp [oddNearSet, HypercubeRamsey.S04.ballV]

private theorem oddRow_nonneg
    {β γ : ℝ} {G : HypercubeRamsey.Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (ω : HypercubeRamsey.S04.Prep M tag) (u : HypercubeRamsey.S04.OddRole n) (y : Fin N) :
    0 ≤ HypercubeRamsey.S04.oddRow M tag ω u y := by
  unfold HypercubeRamsey.S04.oddRow
  split_ifs
  · exact (HypercubeRamsey.S04.oddDraw M tag ω u).nonneg y
  · exact le_rfl

private noncomputable def predGateWeight
    {β γ : ℝ} {G : HypercubeRamsey.Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (a : HypercubeRamsey.S04.EvenRole n) (c : HypercubeRamsey.S04.Loc β γ n)
    (ω : HypercubeRamsey.S04.Prep M tag) : ℝ :=
  ∑ y : Fin n → Fin N,
    (if HypercubeRamsey.S04.EvLocal M tag ω a c then 1 else 0) *
      (∏ j, HypercubeRamsey.S04.oddRow M tag ω
        (HypercubeRamsey.S04.oddNbr a j) (y j)) *
      (if ¬ HypercubeRamsey.S04.PredOK M tag ω a c y then 1 else 0)

private theorem predGateWeight_expect_le_eps
    {β γ : ℝ} {G : HypercubeRamsey.Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (q : HypercubeRamsey.S04.XProf M tag) (q' : HypercubeRamsey.S04.YProf M tag)
    (hRef : HypercubeRamsey.S04.RefIndep M tag)
    (hResample : HypercubeRamsey.S04.Resample M tag q q')
    (a : HypercubeRamsey.S04.EvenRole n) (c : HypercubeRamsey.S04.Loc β γ n) :
    (HypercubeRamsey.S04.prepLaw M tag q q').expect
      (predGateWeight M tag a c) ≤ HypercubeRamsey.S04.eps4 β γ n := by
  classical
  let κ := HypercubeRamsey.S04.key β γ n a.1
  let ε := HypercubeRamsey.S04.eps4 β γ n
  have hε : 0 < ε := by dsimp [ε, HypercubeRamsey.S04.eps4]; positivity
  have hF0 (ω : HypercubeRamsey.S04.Prep M tag)
      (z : Fin (HypercubeRamsey.S04.tupLen β γ n) → Fin N) (y : Fin n → Fin N) :
      0 ≤ HypercubeRamsey.S04.lik M tag ω a c z y := by
    unfold HypercubeRamsey.S04.lik
    apply mul_nonneg
    · split_ifs <;> norm_num
    · apply Finset.prod_nonneg
      intro j hj
      exact oddRow_nonneg M tag
        (HypercubeRamsey.S04.updW ω (c, κ) z) (HypercubeRamsey.S04.oddNbr a j) (y j)
  have hgateBound (ω : HypercubeRamsey.S04.Prep M tag) :
      (∑ y, if HypercubeRamsey.S04.marg M tag ω a c y <
          ε * (HypercubeRamsey.S04.refProd M tag ω a c y) ∨
          HypercubeRamsey.S04.marg M tag ω a c y = 0 then
          HypercubeRamsey.S04.marg M tag ω a c y else 0) ≤ ε := by
    let πω := HypercubeRamsey.S04.prior M tag ω c κ
    let Q := HypercubeRamsey.FinProb.pi
      (fun j : Fin n => HypercubeRamsey.S04.refRow M tag ω
        (HypercubeRamsey.S04.oddNbr a j) c κ)
    let F : (Fin (HypercubeRamsey.S04.tupLen β γ n) → Fin N) →
        (Fin n → Fin N) → ℝ := fun z y => HypercubeRamsey.S04.lik M tag ω a c z y
    have hQ (y : Fin n → Fin N) : Q.w y = HypercubeRamsey.S04.refProd M tag ω a c y := by
      simp [Q, κ, HypercubeRamsey.FinProb.pi, HypercubeRamsey.S04.refProd]
    have hGate := HypercubeRamsey.gated_posterior πω F (hF0 ω) Q ε 0 hε
    have hGateMassRaw := hGate.1
    change (∑ y, if (∑ z, πω.w z * F z y) < ε * Q.w y ∨
        (∑ z, πω.w z * F z y) = 0 then (∑ z, πω.w z * F z y) else 0) ≤ ε at hGateMassRaw
    have hMarg (y : Fin n → Fin N) :
        HypercubeRamsey.S04.marg M tag ω a c y = ∑ z, πω.w z * F z y := by
      rfl
    have hGateMassQ :
        (∑ y, if HypercubeRamsey.S04.marg M tag ω a c y < ε * Q.w y ∨
          HypercubeRamsey.S04.marg M tag ω a c y = 0 then
          HypercubeRamsey.S04.marg M tag ω a c y else 0) ≤ ε := by
      simpa only [hMarg] using hGateMassRaw
    have hGateMass :
        (∑ y, if HypercubeRamsey.S04.marg M tag ω a c y <
          ε * HypercubeRamsey.S04.refProd M tag ω a c y ∨
          HypercubeRamsey.S04.marg M tag ω a c y = 0 then
          HypercubeRamsey.S04.marg M tag ω a c y else 0) ≤ ε := by
      convert hGateMassQ using 1 <;> simp [hQ]
    exact hGateMass
  have hmarg0 (ω : HypercubeRamsey.S04.Prep M tag) (y : Fin n → Fin N) :
      0 ≤ HypercubeRamsey.S04.marg M tag ω a c y := by
    unfold HypercubeRamsey.S04.marg
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg
      ((HypercubeRamsey.S04.prior M tag ω c κ).nonneg z) (hF0 ω z y)
  have hfailGate (ω : HypercubeRamsey.S04.Prep M tag) (y : Fin n → Fin N)
      (hfail : ¬ HypercubeRamsey.S04.PredOK M tag ω a c y) :
      HypercubeRamsey.S04.marg M tag ω a c y <
          ε * HypercubeRamsey.S04.refProd M tag ω a c y ∨
        HypercubeRamsey.S04.marg M tag ω a c y = 0 := by
    by_cases hz : HypercubeRamsey.S04.marg M tag ω a c y = 0
    · exact Or.inr hz
    · have hpos : 0 < HypercubeRamsey.S04.marg M tag ω a c y :=
        lt_of_le_of_ne (hmarg0 ω y) (Ne.symm hz)
      left
      by_contra hnot
      have hge : ε * HypercubeRamsey.S04.refProd M tag ω a c y ≤
          HypercubeRamsey.S04.marg M tag ω a c y := le_of_not_gt hnot
      exact hfail ⟨hpos, hge⟩
  have hfailMass (ω : HypercubeRamsey.S04.Prep M tag) :
      (∑ y, if ¬ HypercubeRamsey.S04.PredOK M tag ω a c y then
        HypercubeRamsey.S04.marg M tag ω a c y else 0) ≤ ε := by
    calc
      (∑ y, if ¬ HypercubeRamsey.S04.PredOK M tag ω a c y then
          HypercubeRamsey.S04.marg M tag ω a c y else 0) ≤
        ∑ y, if HypercubeRamsey.S04.marg M tag ω a c y <
          ε * HypercubeRamsey.S04.refProd M tag ω a c y ∨
          HypercubeRamsey.S04.marg M tag ω a c y = 0 then
          HypercubeRamsey.S04.marg M tag ω a c y else 0 := by
            apply Finset.sum_le_sum
            intro y hy
            by_cases hf : ¬ HypercubeRamsey.S04.PredOK M tag ω a c y
            · have hg := hfailGate ω y hf
              simp [hf, hg]
            · by_cases hg : HypercubeRamsey.S04.marg M tag ω a c y <
                  ε * HypercubeRamsey.S04.refProd M tag ω a c y ∨
                  HypercubeRamsey.S04.marg M tag ω a c y = 0
              · simp [hf, hg, hmarg0 ω y]
              · simp [hf, hg]
      _ ≤ ε := hgateBound ω
  have hresample := hResample c κ (predGateWeight M tag a c)
  have hinner (ω : HypercubeRamsey.S04.Prep M tag) :
      (∑ z, (HypercubeRamsey.S04.prior M tag ω c κ).w z *
        predGateWeight M tag a c (HypercubeRamsey.S04.updW ω (c, κ) z)) =
      ∑ y, if ¬ HypercubeRamsey.S04.PredOK M tag ω a c y then
        HypercubeRamsey.S04.marg M tag ω a c y else 0 := by
    have hInv (z : Fin (HypercubeRamsey.S04.tupLen β γ n) → Fin N)
        (y : Fin n → Fin N) :
        HypercubeRamsey.S04.PredOK M tag
            (HypercubeRamsey.S04.updW ω (c, κ) z) a c y ↔
          HypercubeRamsey.S04.PredOK M tag ω a c y := by
      have h := hRef ω a c z y
      unfold HypercubeRamsey.S04.PredOK
      rw [h.2, h.1]
    unfold predGateWeight
    calc
      (∑ z, (HypercubeRamsey.S04.prior M tag ω c κ).w z *
          ∑ y, (if HypercubeRamsey.S04.EvLocal M tag
              (HypercubeRamsey.S04.updW ω (c, κ) z) a c then 1 else 0) *
              (∏ j, HypercubeRamsey.S04.oddRow M tag
                (HypercubeRamsey.S04.updW ω (c, κ) z)
                (HypercubeRamsey.S04.oddNbr a j) (y j)) *
              (if ¬ HypercubeRamsey.S04.PredOK M tag
                  (HypercubeRamsey.S04.updW ω (c, κ) z) a c y then 1 else 0)) =
        ∑ z, ∑ y, (HypercubeRamsey.S04.prior M tag ω c κ).w z *
          ((if HypercubeRamsey.S04.EvLocal M tag
              (HypercubeRamsey.S04.updW ω (c, κ) z) a c then 1 else 0) *
            (∏ j, HypercubeRamsey.S04.oddRow M tag
              (HypercubeRamsey.S04.updW ω (c, κ) z)
              (HypercubeRamsey.S04.oddNbr a j) (y j)) *
            (if ¬ HypercubeRamsey.S04.PredOK M tag
                (HypercubeRamsey.S04.updW ω (c, κ) z) a c y then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [Finset.mul_sum]
      _ = ∑ y, ∑ z, (if ¬ HypercubeRamsey.S04.PredOK M tag ω a c y then
          (HypercubeRamsey.S04.prior M tag ω c κ).w z *
            HypercubeRamsey.S04.lik M tag ω a c z y else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hf : ¬ HypercubeRamsey.S04.PredOK M tag ω a c y
        · have hf' : ¬ HypercubeRamsey.S04.PredOK M tag
              (HypercubeRamsey.S04.updW ω (c, κ) z) a c y := by
            intro hgood
            exact hf ((hInv z y).mp hgood)
          simp [hf, hf', HypercubeRamsey.S04.lik]
          ring
        · have hgood : HypercubeRamsey.S04.PredOK M tag ω a c y := by
            by_contra hh
            exact hf hh
          have hgood' := (hInv z y).mpr hgood
          simp [hf, hgood, hgood', HypercubeRamsey.S04.lik]
      _ = ∑ y, if ¬ HypercubeRamsey.S04.PredOK M tag ω a c y then
            HypercubeRamsey.S04.marg M tag ω a c y else 0 := by
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hf : ¬ HypercubeRamsey.S04.PredOK M tag ω a c y
              · simp [hf, κ, HypercubeRamsey.S04.marg,
                  HypercubeRamsey.S04.prior]
              · simp [hf]
  calc
    (HypercubeRamsey.S04.prepLaw M tag q q').expect (predGateWeight M tag a c) =
        (HypercubeRamsey.S04.prepLaw M tag q q').expect
          (fun ω => ∑ z, (HypercubeRamsey.S04.prior M tag ω c κ).w z *
            predGateWeight M tag a c (HypercubeRamsey.S04.updW ω (c, κ) z)) :=
      hresample
    _ = (HypercubeRamsey.S04.prepLaw M tag q q').expect
          (fun ω => ∑ y, if ¬ HypercubeRamsey.S04.PredOK M tag ω a c y then
            HypercubeRamsey.S04.marg M tag ω a c y else 0) := by
      unfold HypercubeRamsey.FinProb.expect
      apply Finset.sum_congr rfl
      intro ω hω
      exact congrArg (fun t =>
        (HypercubeRamsey.S04.prepLaw M tag q q').w ω * t) (hinner ω)
    _ ≤ (HypercubeRamsey.S04.prepLaw M tag q q').expect (fun _ => ε) :=
      HypercubeRamsey.FinProb.expect_mono _ (fun ω => hfailMass ω)
    _ = ε := HypercubeRamsey.FinProb.expect_const _ ε

private theorem succ_le_two_pow_of_pos {n : ℕ} (hn : 1 ≤ n) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hn' : 1 ≤ n := by omega
      have hi := ih hn'
      have hp : 0 < 2 ^ n := Nat.pow_pos (by omega)
      rw [pow_succ]
      omega

private theorem pred_fail_union_tail_small (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      2 * (Fintype.card (HypercubeRamsey.S04.EvenRole n ×
        HypercubeRamsey.S04.Loc β γ n) : ℝ) * HypercubeRamsey.S04.eps4 β γ n ≤ 1 / 10 := by
  have hω := HypercubeRamsey.S04.omega4_pos hβ hγ
  let η := HypercubeRamsey.omega4 β γ / 3 - HypercubeRamsey.h4 β γ
  have hη : 0 < η := by
    dsimp [η, HypercubeRamsey.h4]
    nlinarith [hω]
  let c := HypercubeRamsey.S04.c2 / 4
  have hc : 0 < c := by dsimp [c, HypercubeRamsey.S04.c2,
    HypercubeRamsey.S04.c1]; norm_num
  obtain ⟨nPow, hPow⟩ := eventually_rpow_gt_const η (4 / c) hη
  obtain ⟨nExp, hExp⟩ := eventually_small_poly_exp (Real.log 2 / 2)
    (by positivity) (1 / 10) (by norm_num)
  let ζ := HypercubeRamsey.S04.zetaH β γ
  let σ := HypercubeRamsey.S04.sigmaH β γ
  have hζ : 0 < ζ := by
    dsimp [ζ, HypercubeRamsey.S04.zetaH, HypercubeRamsey.S04.b0H,
      HypercubeRamsey.S04.bH]
    positivity
  have hζ1 : ζ < 1 := by
    have hωlt := HypercubeRamsey.S04.omega4_lt hβ hβγ
    dsimp [ζ, HypercubeRamsey.S04.zetaH, HypercubeRamsey.S04.b0H,
      HypercubeRamsey.S04.bH]
    linarith
  have hσ : 0 < σ := by
    dsimp [σ, HypercubeRamsey.S04.sigmaH]
    positivity
  have hσζ : σ < ζ / 2 := by
    dsimp [σ, ζ, HypercubeRamsey.S04.sigmaH]
    linarith
  obtain ⟨nTop, hTop⟩ := topScale_small σ ζ hσ hζ hσζ hζ1
  refine ⟨max (max nPow nExp) (max nTop 2), ?_⟩
  intro n hn
  have hnPow : nPow ≤ n := by omega
  have hnExp : nExp ≤ n := by omega
  have hnTop : nTop ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hTuple : (n : ℝ) ^ (HypercubeRamsey.omega4 β γ / 3) ≤
      (HypercubeRamsey.S04.tupLen β γ n : ℝ) := by
    dsimp [HypercubeRamsey.S04.tupLen]
    exact Nat.le_ceil _
  have hPowId : (n : ℝ) ^ (-HypercubeRamsey.h4 β γ) *
      (n : ℝ) ^ (HypercubeRamsey.omega4 β γ / 3) = (n : ℝ) ^ η := by
    calc
      _ = (n : ℝ) ^ (-HypercubeRamsey.h4 β γ +
          HypercubeRamsey.omega4 β γ / 3) :=
        (Real.rpow_add hnR _ _).symm
      _ = (n : ℝ) ^ η := by congr 1 <;> dsimp [η] <;> ring
  have hProductLower : (n : ℝ) ^ η * (n : ℝ) ≤
      HypercubeRamsey.S04.aStar β γ n *
        (HypercubeRamsey.S04.tupLen β γ n : ℝ) * (n : ℝ) := by
    calc
      (n : ℝ) ^ η * (n : ℝ) =
          ((n : ℝ) ^ (-HypercubeRamsey.h4 β γ) *
            (n : ℝ) ^ (HypercubeRamsey.omega4 β γ / 3)) * (n : ℝ) := by
              rw [hPowId]
      _ ≤ (HypercubeRamsey.S04.aStar β γ n *
          (HypercubeRamsey.S04.tupLen β γ n : ℝ)) * (n : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hnR.le
            simpa [HypercubeRamsey.S04.aStar] using
              (mul_le_mul_of_nonneg_left hTuple
                (Real.rpow_nonneg hnR.le (-HypercubeRamsey.h4 β γ)))
      _ = HypercubeRamsey.S04.aStar β γ n *
          (HypercubeRamsey.S04.tupLen β γ n : ℝ) * (n : ℝ) := by ring
  have hpowLarge := hPow n hnPow
  have hcoef : 4 ≤ c * (n : ℝ) ^ η := by
    have hmul := mul_lt_mul_of_pos_left hpowLarge hc
    have hcancel : c * (4 / c) = 4 := by field_simp [ne_of_gt hc]
    linarith
  have hExponent : 4 * (n : ℝ) ≤
      HypercubeRamsey.S04.c2 * HypercubeRamsey.S04.aStar β γ n *
        (HypercubeRamsey.S04.tupLen β γ n : ℝ) * (n : ℝ) / 4 := by
    calc
      4 * (n : ℝ) ≤ c * (n : ℝ) ^ η * (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcoef hnR.le
      _ ≤ c * (HypercubeRamsey.S04.aStar β γ n *
          (HypercubeRamsey.S04.tupLen β γ n : ℝ) * (n : ℝ)) := by
        calc
          c * (n : ℝ) ^ η * (n : ℝ) = c * ((n : ℝ) ^ η * (n : ℝ)) := by ring
          _ ≤ c * (HypercubeRamsey.S04.aStar β γ n *
              (HypercubeRamsey.S04.tupLen β γ n : ℝ) * (n : ℝ)) :=
                mul_le_mul_of_nonneg_left hProductLower hc.le
      _ = HypercubeRamsey.S04.c2 * HypercubeRamsey.S04.aStar β γ n *
          (HypercubeRamsey.S04.tupLen β γ n : ℝ) * (n : ℝ) / 4 := by
            dsimp [c]
            ring
  have hEps : HypercubeRamsey.S04.eps4 β γ n ≤ Real.exp (-4 * (n : ℝ)) := by
    dsimp [HypercubeRamsey.S04.eps4]
    apply Real.exp_le_exp.mpr
    nlinarith [hExponent]
  have hTopReal : (HypercubeRamsey.S04.topH β γ n : ℝ) ≤ n := by
    have hTop' := hTop n hnTop
    have hpowle : (n : ℝ) ^ (1 - ζ / 2) ≤ (n : ℝ) := by
      calc
        (n : ℝ) ^ (1 - ζ / 2) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)
        _ = n := Real.rpow_one _
    have hTop'' : (HypercubeRamsey.S04.topH β γ n : ℝ) ≤
        (n : ℝ) ^ (1 - ζ / 2) := by
      simpa [HypercubeRamsey.S04.topH, σ, ζ] using hTop'
    exact hTop''.trans hpowle
  have hTopNat : HypercubeRamsey.S04.topH β γ n ≤ n := by exact_mod_cast hTopReal
  have hTopSucc : HypercubeRamsey.S04.topH β γ n + 1 ≤ 2 ^ n :=
    (Nat.add_le_add_right hTopNat 1).trans (succ_le_two_pow_of_pos hn1)
  have hCardLoc : Fintype.card (HypercubeRamsey.S04.Loc β γ n) =
      2 ^ n * (HypercubeRamsey.S04.topH β γ n + 1) := by
    simp [HypercubeRamsey.S04.Loc, OAI.HypercubeRamsey.card_cubeVertex]
  have hLocBound : (Fintype.card (HypercubeRamsey.S04.Loc β γ n) : ℝ) ≤
      (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [hCardLoc]
    have hnat : 2 ^ n * (HypercubeRamsey.S04.topH β γ n + 1) ≤ 2 ^ n * 2 ^ n :=
      Nat.mul_le_mul_left (2 ^ n) hTopSucc
    exact_mod_cast hnat
  have hRoleBound : (Fintype.card (HypercubeRamsey.S04.EvenRole n) : ℝ) ≤
      (2 : ℝ) ^ n := by
    rw [evenRole_card_eq hn0]
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1))
  have hCardPair : (Fintype.card (HypercubeRamsey.S04.EvenRole n ×
      HypercubeRamsey.S04.Loc β γ n) : ℝ) ≤ (2 : ℝ) ^ (3 * n) := by
    rw [Fintype.card_prod]
    push_cast
    calc
      (Fintype.card (HypercubeRamsey.S04.EvenRole n) : ℝ) *
          Fintype.card (HypercubeRamsey.S04.Loc β γ n) ≤
        (2 : ℝ) ^ n * ((2 : ℝ) ^ n * (2 : ℝ) ^ n) :=
          mul_le_mul hRoleBound hLocBound (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (3 * n) := by
        calc
          (2 : ℝ) ^ n * ((2 : ℝ) ^ n * (2 : ℝ) ^ n) = ((2 : ℝ) ^ n) ^ 3 := by ring
          _ = (2 : ℝ) ^ (n * 3) := by rw [← pow_mul]
          _ = (2 : ℝ) ^ (3 * n) := by congr 1 <;> omega
  have hpowExp (m : ℕ) : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ m = Real.exp (Real.log ((2 : ℝ) ^ m)) :=
        (Real.exp_log (by positivity)).symm
      _ = Real.exp ((m : ℝ) * Real.log 2) := by rw [Real.log_pow]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hcardExp : 2 * (Fintype.card (HypercubeRamsey.S04.EvenRole n ×
      HypercubeRamsey.S04.Loc β γ n) : ℝ) ≤ Real.exp (1 + 3 * (n : ℝ)) := by
    calc
      _ ≤ 2 * (2 : ℝ) ^ (3 * n) := mul_le_mul_of_nonneg_left hCardPair (by norm_num)
      _ = Real.exp (Real.log 2 + ((3 * n : ℕ) : ℝ) * Real.log 2) := by
        rw [hpowExp]
        calc
          2 * Real.exp (((3 * n : ℕ) : ℝ) * Real.log 2) =
              Real.exp (Real.log 2) *
                Real.exp (((3 * n : ℕ) : ℝ) * Real.log 2) := by
                  rw [Real.exp_log (by norm_num : 0 < (2 : ℝ))]
          _ = Real.exp (Real.log 2 + ((3 * n : ℕ) : ℝ) * Real.log 2) :=
            (Real.exp_add _ _).symm
      _ ≤ Real.exp (1 + 3 * (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [hlog2]
  have hsmall := hExp n hnExp
  have hfinal : Real.exp (1 - (n : ℝ)) ≤
      (n : ℝ) ^ (2 : ℝ) * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := by
    calc
      Real.exp (1 - (n : ℝ)) ≤ Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        nlinarith [hlog2]
      _ ≤ (n : ℝ) ^ (2 : ℝ) * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := by
        have hnSq : 1 ≤ (n : ℝ) ^ (2 : ℝ) :=
          Real.one_le_rpow hnR1 (by norm_num)
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hnSq (Real.exp_nonneg _))
  have hEpsNonneg : 0 ≤ HypercubeRamsey.S04.eps4 β γ n := by
    dsimp [HypercubeRamsey.S04.eps4]
    positivity
  calc
    2 * (Fintype.card (HypercubeRamsey.S04.EvenRole n ×
        HypercubeRamsey.S04.Loc β γ n) : ℝ) * HypercubeRamsey.S04.eps4 β γ n ≤
      Real.exp (1 + 3 * (n : ℝ)) * Real.exp (-4 * (n : ℝ)) := by
        exact mul_le_mul hcardExp hEps hEpsNonneg (Real.exp_nonneg _)
    _ = Real.exp (1 - (n : ℝ)) := by rw [← Real.exp_add]; congr 1 <;> ring
    _ ≤ (n : ℝ) ^ (2 : ℝ) * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := hfinal
    _ ≤ 1 / 10 := le_of_lt hsmall
private theorem evenMean_nonneg
    {β γ : ℝ} {G : HypercubeRamsey.Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (hRows : HypercubeRamsey.S04.EvenRowFacts M tag)
    (ω : HypercubeRamsey.S04.Prep M tag) (a : HypercubeRamsey.S04.EvenRole n)
    (x : Fin N) : 0 ≤ HypercubeRamsey.S04.evenMean M tag ω a x := by
  unfold HypercubeRamsey.S04.evenMean HypercubeRamsey.S04.oddDrawLaw
    HypercubeRamsey.FinProb.expect
  apply Finset.sum_nonneg
  intro f hf
  exact mul_nonneg ((HypercubeRamsey.S04.oddDrawLaw M tag ω).nonneg f)
    ((hRows ω a (HypercubeRamsey.S04.nbrLabels f a)).1 x)

private theorem lane_nonempty_of_finProb {α : Type*} [Fintype α]
    (P : HypercubeRamsey.FinProb α) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := ⟨fun a => h ⟨a⟩⟩
  have hsum : (∑ a, P.w a) = 0 := by simp
  rw [P.sum_eq_one] at hsum
  norm_num at hsum

private theorem pr_fintype_union
    {I Ω : Type*} [Fintype I] [Fintype Ω]
    (P : HypercubeRamsey.FinProb Ω) (A : I → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) := by
  classical
  let event : Ω → Prop := fun ω => ∃ i, A i ω
  letI : DecidablePred event := fun ω => Classical.propDecidable (event ω)
  change P.pr event ≤ ∑ i, P.pr (A i)
  have hpr : P.pr event = ∑ ω, if event ω then P.w ω else 0 := by rfl
  rw [hpr]
  calc
    (∑ ω, if event ω then P.w ω else 0) ≤
        ∑ ω, ∑ i, if A i ω then P.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases he : event ω
      · obtain ⟨i, hi⟩ := he
        have he' : event ω := ⟨i, hi⟩
        calc
          (if event ω then P.w ω else 0) = P.w ω := by simp [he']
          _ = (if A i ω then P.w ω else 0) := by simp [hi]
          _ ≤ ∑ i, if A i ω then P.w ω else 0 :=
            Finset.single_le_sum
              (s := Finset.univ) (f := fun j => if A j ω then P.w ω else 0)
              (fun j hj => by
                by_cases hAj : A j ω <;> simp [hAj, P.nonneg ω])
              (Finset.mem_univ i)
      · simp [he]
        apply Finset.sum_nonneg
        intro i hi
        by_cases hAi : A i ω <;> simp [hAi, P.nonneg ω]
    _ = ∑ i, P.pr (A i) := by
      simp only [HypercubeRamsey.FinProb.pr]
      rw [Finset.sum_comm]

private theorem oddNbr_injective {n : ℕ} (a : HypercubeRamsey.S04.EvenRole n) :
    Function.Injective (HypercubeRamsey.S04.oddNbr a) := by
  intro i j h
  have hval : HypercubeRamsey.cubeFlip a.1 i = HypercubeRamsey.cubeFlip a.1 j :=
    congrArg Subtype.val h
  by_contra hne
  have hcoord := congrFun hval i
  have hleft : HypercubeRamsey.cubeFlip a.1 i i = !a.1 i := by
    simp [HypercubeRamsey.cubeFlip]
  have hright : HypercubeRamsey.cubeFlip a.1 j i = a.1 i := by
    simp [HypercubeRamsey.cubeFlip, hne]
  rw [hleft, hright] at hcoord
  cases hv : a.1 i <;> simp [hv] at hcoord

private noncomputable def nbrRolesEquiv {n : ℕ} (a : HypercubeRamsey.S04.EvenRole n) :
    Fin n ≃ {u : HypercubeRamsey.S04.OddRole n // u ∈ nbrSet a} where
  toFun j := ⟨HypercubeRamsey.S04.oddNbr a j,
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  invFun u := Classical.choose (Finset.mem_image.mp u.2)
  left_inv := by
    intro j
    apply oddNbr_injective a
    exact (Classical.choose_spec (Finset.mem_image.mp
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))).2
  right_inv := by
    intro u
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp u.2)).2

private noncomputable def nbrTupleEquiv {n N : ℕ}
    (a : HypercubeRamsey.S04.EvenRole n) :
    (∀ u : {u : HypercubeRamsey.S04.OddRole n // u ∈ nbrSet a}, Fin N) ≃
      (Fin n → Fin N) where
  toFun o j := o (nbrRolesEquiv a j)
  invFun y u := y ((nbrRolesEquiv a).symm u)
  left_inv := by intro o; funext u; simp
  right_inv := by intro y; funext j; simp

private theorem nbrProduct_reindex {n N : ℕ} (a : HypercubeRamsey.S04.EvenRole n)
    (P : HypercubeRamsey.S04.OddRole n → HypercubeRamsey.FinProb (Fin N))
    (o : ∀ u : {u : HypercubeRamsey.S04.OddRole n // u ∈ nbrSet a}, Fin N) :
    (∏ u : {u : HypercubeRamsey.S04.OddRole n // u ∈ nbrSet a}, (P u.1).w (o u)) =
      ∏ j : Fin n, (P (HypercubeRamsey.S04.oddNbr a j)).w (o (nbrRolesEquiv a j)) := by
  symm
  exact Fintype.prod_equiv (nbrRolesEquiv a)
    (fun j => (P (HypercubeRamsey.S04.oddNbr a j)).w (o (nbrRolesEquiv a j)))
    (fun u => (P u.1).w (o u)) (by intro j; rfl)

private theorem odd_neighbor_expect {β γ : ℝ} {G : HypercubeRamsey.Colour}
    {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (ω : HypercubeRamsey.S04.Prep M tag) (a : HypercubeRamsey.S04.EvenRole n)
    (g : (Fin n → Fin N) → ℝ) :
    (HypercubeRamsey.S04.oddDrawLaw M tag ω).expect
        (fun f => g (HypercubeRamsey.S04.nbrLabels f a)) =
      (HypercubeRamsey.FinProb.pi
        (fun j : Fin n => HypercubeRamsey.S04.oddDraw M tag ω
          (HypercubeRamsey.S04.oddNbr a j))).expect g := by
  classical
  let P : HypercubeRamsey.S04.OddRole n → HypercubeRamsey.FinProb (Fin N) :=
    fun u => HypercubeRamsey.S04.oddDraw M tag ω u
  let S := nbrSet a
  let T := nbrTupleEquiv (N := N) a
  let Qs := HypercubeRamsey.FinProb.pi (fun u : {u : HypercubeRamsey.S04.OddRole n // u ∈ S} => P u.1)
  let Q := HypercubeRamsey.FinProb.pi (fun j : Fin n => P (HypercubeRamsey.S04.oddNbr a j))
  let gS : (∀ u : {u : HypercubeRamsey.S04.OddRole n // u ∈ S}, Fin N) → ℝ :=
    fun o => g (T o)
  have hproj (f : HypercubeRamsey.S04.OddRole n → Fin N) :
      g (HypercubeRamsey.S04.nbrLabels f a) = gS (fun u => f u.1) := by
    congr 1
  have hfull :
      (HypercubeRamsey.S04.oddDrawLaw M tag ω).expect
          (fun f => g (HypercubeRamsey.S04.nbrLabels f a)) =
        (HypercubeRamsey.FinProb.pi P).expect (fun f => gS (fun u => f u.1)) := by
    unfold HypercubeRamsey.FinProb.expect
    apply Finset.sum_congr rfl
    intro f hf
    change (HypercubeRamsey.S04.oddDrawLaw M tag ω).w f *
        g (HypercubeRamsey.S04.nbrLabels f a) =
      (HypercubeRamsey.FinProb.pi P).w f * gS (fun u => f u.1)
    rw [hproj]
    simp [P, HypercubeRamsey.S04.oddDrawLaw]
  rw [hfull, HypercubeRamsey.FinProb.pi_marginal_expect P S gS]
  have hweight (y : Fin n → Fin N) : Qs.w (T.symm y) = Q.w y := by
    dsimp [Qs, Q, HypercubeRamsey.FinProb.pi]
    rw [← Finset.univ_eq_attach]
    rw [nbrProduct_reindex]
    simp [T, nbrTupleEquiv]
  calc
    Qs.expect gS = ∑ o, Qs.w o * gS o := rfl
    _ = ∑ y, Qs.w (T.symm y) * gS (T.symm y) :=
      Fintype.sum_equiv T _ _ (by intro o; simp)
    _ = ∑ y, Q.w y * g y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hweight]
      simp [gS, T]
    _ = Q.expect g := rfl

private theorem evenNearSet_card_le {n R : ℕ} (a : HypercubeRamsey.S04.EvenRole n) :
    (evenNearSet R a).card ≤ (HypercubeRamsey.S04.ballV a.1 R).card := by
  classical
  have hsub : (evenNearSet R a).image Subtype.val ⊆ HypercubeRamsey.S04.ballV a.1 R := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
    exact (Finset.mem_filter.mp hw).2
  calc
    (evenNearSet R a).card = ((evenNearSet R a).image Subtype.val).card := by
      symm
      exact Finset.card_image_of_injective _ Subtype.val_injective
    _ ≤ (HypercubeRamsey.S04.ballV a.1 R).card := Finset.card_le_card hsub

private theorem evenNearSet_mem_iff {n R : ℕ} (a b : HypercubeRamsey.S04.EvenRole n) :
    b ∈ evenNearSet R a ↔ _root_.hammingDist a.1 b.1 ≤ R := by
  simp [evenNearSet, HypercubeRamsey.S04.ballV]

private theorem locR_ratio_tendsto_zero (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hγ : γ < 1) :
    Tendsto (fun n : ℕ => (2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n) atTop (nhds 0) := by
  obtain ⟨n₀, hR⟩ := locR_near_radius_small β γ hβ hβγ hγ
  let δ := HypercubeRamsey.S04.zetaH β γ / 4
  have hω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have hδ : 0 < δ := by dsimp [δ, HypercubeRamsey.S04.zetaH,
    HypercubeRamsey.S04.b0H, HypercubeRamsey.S04.bH]; positivity
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-δ)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
    have heq : (fun n : ℕ => (n : ℝ) ^ (-δ)) =ᶠ[atTop]
        ((fun x : ℝ => x ^ (-δ)) ∘ Nat.cast) := by
      filter_upwards [] with n
      rfl
    exact Tendsto.congr' heq h
  have hle : ∀ᶠ n : ℕ in atTop,
      (2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n ≤ (n : ℝ) ^ (-δ) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨n₀, hR⟩,
      Filter.eventually_gt_atTop (0 : ℕ)] with n hn hnn
    rcases hn with ⟨hn1, hnBound⟩
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnn
    have hbound : (2 * HypercubeRamsey.S04.locR β γ n : ℝ) ≤ (n : ℝ) ^ (1 - δ) := by
      simpa [δ] using hnBound
    have hinv : (n : ℝ)⁻¹ = (n : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg hnpos.le 1, Real.rpow_one]
    have hdiv : (n : ℝ) ^ (1 - δ) / (n : ℝ) = (n : ℝ) ^ (-δ) := by
      rw [div_eq_mul_inv, hinv, ← Real.rpow_add hnpos]
      congr 1 <;> ring
    calc
      (2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n ≤
          (n : ℝ) ^ (1 - δ) / (n : ℝ) := div_le_div_of_nonneg_right hbound (by positivity)
      _ = (n : ℝ) ^ (-δ) := hdiv
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      (0 : ℝ) ≤ (2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n := by
    filter_upwards [] with n
    positivity
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow hnonneg hle

private theorem locR_ratio_le_rpow (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n ≤
        (n : ℝ) ^ (-(HypercubeRamsey.S04.zetaH β γ / 4)) := by
  obtain ⟨n₀, hR⟩ := locR_near_radius_small β γ hβ hβγ hγ
  let δ := HypercubeRamsey.S04.zetaH β γ / 4
  refine ⟨n₀, ?_⟩
  intro n hn
  have hnBound := hR n hn
  have hn1 : 1 ≤ n := hnBound.1
  have hn0 : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hbound : (2 * HypercubeRamsey.S04.locR β γ n : ℝ) ≤ (n : ℝ) ^ (1 - δ) := by
    simpa [δ] using hnBound.2
  have hinv : (n : ℝ)⁻¹ = (n : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg hnpos.le 1, Real.rpow_one]
  have hdiv : (n : ℝ) ^ (1 - δ) / (n : ℝ) = (n : ℝ) ^ (-δ) := by
    rw [div_eq_mul_inv, hinv, ← Real.rpow_add hnpos]
    congr 1 <;> ring
  calc
    (2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n ≤
        (n : ℝ) ^ (1 - δ) / (n : ℝ) := div_le_div_of_nonneg_right hbound (by positivity)
    _ = (n : ℝ) ^ (-δ) := hdiv

private theorem eventually_union_tail_small :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n ≤ 1 / 10 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n₀, hpoly⟩ := eventually_small_poly_exp (Real.log 2 / 2)
    (by positivity) (1 / 10) (by norm_num)
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hsmall := hpoly n (by omega)
  have hpow : (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have hhalf : (1 / 2 : ℝ) ^ n = Real.exp (-(n : ℝ) * Real.log 2) := by
    calc
      (1 / 2 : ℝ) ^ n = Real.exp (Real.log ((1 / 2 : ℝ) ^ n)) :=
        (Real.exp_log (by positivity)).symm
      _ = Real.exp ((n : ℝ) * Real.log (1 / 2 : ℝ)) := by rw [Real.log_pow]
      _ = Real.exp (-(n : ℝ) * Real.log 2) := by
        congr 1
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
        ring
  have hexp : Real.exp (-(n : ℝ) * Real.log 2) ≤
      Real.exp (-(Real.log 2 / 2) * n) := by
    apply Real.exp_le_exp.mpr
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith [hlog2, hn1R]
  have hnSq : (n : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ n by exact_mod_cast hn1)
        (by norm_num : (1 : ℝ) ≤ 2))
  exact (calc
    (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n = (n : ℝ) * (1 / 2 : ℝ) ^ n := by
      rw [mul_assoc, hpow]
    _ = (n : ℝ) * Real.exp (-(n : ℝ) * Real.log 2) := by rw [hhalf]
    _ ≤ (n : ℝ) ^ (2 : ℝ) * Real.exp (-(Real.log 2 / 2) * n) := by
      gcongr
    _ < 1 / 10 := hsmall
  ).le

private theorem eventually_nat_mul_rpow_exp_small (a b ε : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (n : ℝ) * Real.exp (-b * (n : ℝ) ^ a) < ε := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun x : ℝ => x ^ a⁻¹ * Real.exp (-b * x))
      atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a⁻¹) b hb
  have hcomp := hexp.comp hpow
  have heq : (fun n : ℕ => (n : ℝ) * Real.exp (-b * (n : ℝ) ^ a)) =ᶠ[atTop]
      (fun n : ℕ => ((n : ℝ) ^ a) ^ a⁻¹ * Real.exp (-b * (n : ℝ) ^ a)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hpowEq : ((n : ℝ) ^ a) ^ a⁻¹ = (n : ℝ) := by
      calc
        ((n : ℝ) ^ a) ^ a⁻¹ = (n : ℝ) ^ (a * a⁻¹) :=
          (Real.rpow_mul hnpos.le a a⁻¹).symm
        _ = (n : ℝ) ^ (1 : ℝ) := by
          rw [show a * a⁻¹ = (1 : ℝ) from mul_inv_cancel₀ ha.ne']
        _ = (n : ℝ) := Real.rpow_one _
    rw [hpowEq]
  have hcomp' : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ a) ^ a⁻¹ * Real.exp (-b * (n : ℝ) ^ a))
      atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ a⁻¹ * Real.exp (-b * x)) ∘
      (fun n : ℕ => (n : ℝ) ^ a)) atTop (nhds 0)
    exact hcomp
  have hlim := Tendsto.congr' heq.symm hcomp'
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds hε))
  exact ⟨n₀, hn₀⟩

private theorem bind_filter_expect
    {Ω F : Type*} [Fintype Ω] [Fintype F]
    (P : HypercubeRamsey.FinProb Ω) (J : Ω → HypercubeRamsey.FinProb F)
    (good : Ω → Prop) (g : Ω → F → ℝ) :
    (Finset.univ.filter (fun z : Ω × F => good z.1)).sum
        (fun z => (HypercubeRamsey.FinProb.bind P J).w z * g z.1 z.2) =
      ∑ ω, if good ω then P.w ω * (J ω).expect (g ω) else 0 := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [HypercubeRamsey.FinProb.bind]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hg : good ω
  · simp only [hg, ↓reduceIte]
    calc
      ∑ f, P.w ω * (J ω).w f * g ω f =
          P.w ω * ∑ f, (J ω).w f * g ω f := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f hf
        ring
      _ = P.w ω * (J ω).expect (g ω) := by rw [HypercubeRamsey.FinProb.expect]
  · simp [hg]

private theorem odd_near_small (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      2 * HypercubeRamsey.S04.locR β γ n ≤ n / 2 ∧
      (n : ℝ) * Real.exp
          (Real.binEntropy (((2 * HypercubeRamsey.S04.locR β γ n : ℕ) : ℝ) / n) * n) /
          (2 : ℝ) ^ (n - 1) * Real.exp (2 * (n : ℝ) ^ γ) ≤ 1 := by
  have hxlim := locR_ratio_tendsto_zero β γ hβ hβγ hγ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hentlim : Tendsto
      (fun n : ℕ => Real.binEntropy ((2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n))
      atTop (nhds 0) := by
    change Tendsto (Real.binEntropy ∘
      (fun n : ℕ => (2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n)) atTop (nhds 0)
    simpa [Real.binEntropy_zero] using
      Real.binEntropy_continuous.continuousAt.tendsto.comp hxlim
  have hradEv : ∀ᶠ n : ℕ in atTop,
      (2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n < 1 / 2 :=
    hxlim.eventually (Iio_mem_nhds (by norm_num : 0 < (1 / 2 : ℝ)))
  have hentEv : ∀ᶠ n : ℕ in atTop,
      Real.binEntropy ((2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n) < Real.log 2 / 4 :=
    hentlim.eventually (Iio_mem_nhds (by positivity : 0 < Real.log 2 / 4))
  have hgammaLim : Tendsto (fun n : ℕ => (n : ℝ) ^ (γ - 1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hγ)).comp tendsto_natCast_atTop_atTop
    have h' : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 - γ))) atTop (nhds 0) := by
      change Tendsto ((fun x : ℝ => x ^ (-(1 - γ))) ∘ Nat.cast) atTop (nhds 0)
      exact h
    simpa only [show γ - 1 = -(1 - γ) by ring] using h'
  have hgammaEv : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (γ - 1) < Real.log 2 / 16 :=
    hgammaLim.eventually (Iio_mem_nhds (by positivity : 0 < Real.log 2 / 16))
  obtain ⟨nPoly, hpoly⟩ := eventually_small_poly_exp (Real.log 2 / 2)
    (by positivity) (1 / 2) (by norm_num)
  have hradN := Filter.eventually_atTop.1 hradEv
  have hentN := Filter.eventually_atTop.1 hentEv
  have hgammaN := Filter.eventually_atTop.1 hgammaEv
  refine ⟨max (max (max hradN.choose hentN.choose) hgammaN.choose) (max nPoly 1), ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hradLt : (2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n < 1 / 2 :=
    hradN.choose_spec n (by omega)
  have hRnat : 2 * HypercubeRamsey.S04.locR β γ n ≤ n / 2 := by
    have hRreal : 2 * (2 * HypercubeRamsey.S04.locR β γ n : ℝ) ≤ (n : ℝ) := by
      rw [div_lt_iff₀ hnpos] at hradLt
      linarith
    have hRnat' : 2 * (2 * HypercubeRamsey.S04.locR β γ n) ≤ n := by exact_mod_cast hRreal
    omega
  have hEnt : Real.binEntropy ((2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n) <
      Real.log 2 / 4 := hentN.choose_spec n (by omega)
  have hgam : (n : ℝ) ^ (γ - 1) < Real.log 2 / 16 := hgammaN.choose_spec n (by omega)
  have hpowRel : (n : ℝ) ^ γ = (n : ℝ) ^ (γ - 1) * n := by
    rw [show γ = (γ - 1) + 1 by ring]
    simpa [Real.rpow_one] using (Real.rpow_add hnpos (γ - 1) 1)
  have hgamCap : 2 * (n : ℝ) ^ γ < Real.log 2 / 8 * n := by
    rw [hpowRel]
    nlinarith [hgam, hnpos]
  have hpoly' : (n : ℝ) ^ (2 : ℝ) * Real.exp (-(Real.log 2 / 2) * n) < 1 / 2 :=
    hpoly n (by omega)
  have hnSq : (n : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ n by exact_mod_cast hn1)
        (by norm_num : (1 : ℝ) ≤ 2))
  have hcardNat : Fintype.card (HypercubeRamsey.S04.OddRole n) = 2 ^ (n - 1) :=
    oddRole_card_eq hn0
  have hcard : (Fintype.card (HypercubeRamsey.S04.OddRole n) : ℝ) =
      (2 : ℝ) ^ (n - 1) := by exact_mod_cast hcardNat
  have hden : (2 : ℝ) ^ (n - 1) = Real.exp (((n - 1 : ℕ) : ℝ) * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hcastSub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.sub_add_cancel hn1)
    push_cast at h
    linarith
  have hExpId :
      (Real.exp (Real.binEntropy ((2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n) * n) /
          (2 : ℝ) ^ (n - 1)) * Real.exp (2 * (n : ℝ) ^ γ) =
        2 * Real.exp (Real.binEntropy ((2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n) * n +
          2 * (n : ℝ) ^ γ - (n : ℝ) * Real.log 2) := by
    rw [hden, ← Real.exp_sub, ← Real.exp_add]
    have hshift :
        Real.binEntropy ((2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n) * n -
            ((n - 1 : ℕ) : ℝ) * Real.log 2 + 2 * (n : ℝ) ^ γ =
          Real.log 2 +
            (Real.binEntropy ((2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n) * n +
              2 * (n : ℝ) ^ γ - (n : ℝ) * Real.log 2) := by rw [hcastSub]; ring
    rw [hshift, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hExpSmall :
      Real.binEntropy ((2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n) * n +
          2 * (n : ℝ) ^ γ - (n : ℝ) * Real.log 2 ≤
        -(Real.log 2 / 2) * n := by
    nlinarith [hEnt, hgamCap, hlog2, hnpos]
  refine ⟨hRnat, ?_⟩
  have hfinal := (calc
    (n : ℝ) *
          (Real.exp (Real.binEntropy ((2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n) * n) /
            (Fintype.card (HypercubeRamsey.S04.OddRole n) : ℝ)) *
          Real.exp (2 * (n : ℝ) ^ γ) =
        2 * (n : ℝ) * Real.exp
          (Real.binEntropy ((2 * HypercubeRamsey.S04.locR β γ n : ℝ) / n) * n +
            2 * (n : ℝ) ^ γ - (n : ℝ) * Real.log 2) := by
          rw [hcard, mul_assoc, hExpId]
          ring
    _ ≤ 2 * (n : ℝ) * Real.exp (-(Real.log 2 / 2) * n) := by
      gcongr
    _ ≤ 2 * (n : ℝ) ^ (2 : ℝ) * Real.exp (-(Real.log 2 / 2) * n) := by
      gcongr
    _ < 1 := by nlinarith [hpoly']
  ).le
  rw [hcard] at hfinal
  convert hfinal using 1 <;> norm_num [Nat.cast_mul] <;> ring

set_option maxHeartbeats 1000000 in
private theorem even_near_small (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      2 * HypercubeRamsey.S04.locR β γ n ≤ n / 2 ∧
      (n : ℝ) * Real.exp
          (Real.binEntropy (((2 * HypercubeRamsey.S04.locR β γ n : ℕ) : ℝ) / n) * n) /
          (2 : ℝ) ^ (n - 1) *
          Real.exp ((Real.log 2 - HypercubeRamsey.S04.c2 *
            HypercubeRamsey.S04.aStar β γ n / 2) * n) ≤ 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have hωlt := HypercubeRamsey.S04.omega4_lt hβ hβγ
  let ζ := HypercubeRamsey.S04.zetaH β γ
  let δ := ζ / 16
  let α := (ζ / 4) * (1 - δ)
  let h := HypercubeRamsey.h4 β γ
  let c := HypercubeRamsey.S04.c2
  have hζ : 0 < ζ := by
    dsimp [ζ, HypercubeRamsey.S04.zetaH, HypercubeRamsey.S04.b0H,
      HypercubeRamsey.S04.bH]
    positivity
  have hζlt : ζ < 1 := by
    have hzetaEq : ζ = HypercubeRamsey.omega4 β γ / 2400 := by
      dsimp [ζ, HypercubeRamsey.S04.zetaH, HypercubeRamsey.S04.b0H,
        HypercubeRamsey.S04.bH]
      ring
    rw [hzetaEq]
    linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by dsimp [δ]; linarith
  have hα : 0 < α := by
    dsimp [α, δ]
    have h1δ : 0 < 1 - ζ / 16 := by linarith [hζlt]
    exact mul_pos (by positivity) h1δ
  have hhsmall : h < ζ / 100 := by
    have hzetaEq : ζ = HypercubeRamsey.omega4 β γ / 2400 := by
      dsimp [ζ, HypercubeRamsey.S04.zetaH, HypercubeRamsey.S04.b0H,
        HypercubeRamsey.S04.bH]
      ring
    rw [hzetaEq]
    dsimp [h, HypercubeRamsey.h4]
    nlinarith [hω]
  have hgap : 0 < α - h := by
    dsimp [α, δ]
    nlinarith [hζlt, hhsmall]
  have hgap1 : 0 < 1 - h := by
    have : h < 1 := lt_trans hhsmall (by linarith : ζ / 100 < 1)
    linarith
  have hc : 0 < c := by dsimp [c, HypercubeRamsey.S04.c2, HypercubeRamsey.S04.c1]; norm_num
  have hC : 0 < δ⁻¹ + 1 := by positivity
  obtain ⟨nRadius, hRadius⟩ := odd_near_small β γ hβ hβγ hγ
  obtain ⟨nRate, hRate⟩ := locR_ratio_le_rpow β γ hβ hβγ hγ
  obtain ⟨nConst, hConst⟩ := eventually_rpow_gt_const (α - h) (4 * (δ⁻¹ + 1) / c)
    hgap
  obtain ⟨nExp, hExp⟩ := eventually_nat_mul_rpow_exp_small (1 - h) (c / 4) (1 / 2)
    hgap1 (by positivity) (by norm_num)
  refine ⟨max (max (max nRadius nRate) nConst) (max nExp 1), ?_⟩
  intro n hn
  have hnRadius : nRadius ≤ n := by omega
  have hnRate : nRate ≤ n := by omega
  have hnConst : nConst ≤ n := by omega
  have hnExp : nExp ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hsmallOdd := hRadius n hnRadius
  have hRnat : 2 * HypercubeRamsey.S04.locR β γ n ≤ n / 2 := hsmallOdd.1
  let R : ℕ := 2 * HypercubeRamsey.S04.locR β γ n
  let x : ℝ := (R : ℝ) / n
  have hxRate : x ≤ (n : ℝ) ^ (-(ζ / 4)) := by
    simpa [x, R, ζ] using hRate n hnRate
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    have hnat : R ≤ n / 2 := by simpa [R] using hRnat
    have htwo : 2 * R ≤ n := by omega
    have htwoR : 2 * (R : ℝ) ≤ (n : ℝ) := by exact_mod_cast htwo
    dsimp [x]
    rw [div_le_iff₀ hnpos]
    nlinarith
  have hbin := binEntropy_upper_rpow hx0 hx1 hδ hδhalf
  have hpow : ((n : ℝ) ^ (-(ζ / 4))) ^ (1 - δ) =
      (n : ℝ) ^ (-α) := by
    calc
      ((n : ℝ) ^ (-(ζ / 4))) ^ (1 - δ) =
          (n : ℝ) ^ ((-(ζ / 4)) * (1 - δ)) :=
        (Real.rpow_mul hnpos.le _ _).symm
      _ = (n : ℝ) ^ (-α) := by congr 1 <;> dsimp [α] <;> ring
  have hH : Real.binEntropy x ≤ (δ⁻¹ + 1) * (n : ℝ) ^ (-α) := by
    have hpowExp : 0 ≤ 1 - δ := by linarith [hδhalf]
    have hpowBase : x ^ (1 - δ) ≤ ((n : ℝ) ^ (-(ζ / 4))) ^ (1 - δ) :=
      Real.rpow_le_rpow hx0 hxRate hpowExp
    calc
      Real.binEntropy x ≤ (δ⁻¹ + 1) * x ^ (1 - δ) := hbin
      _ ≤ (δ⁻¹ + 1) * ((n : ℝ) ^ (-(ζ / 4))) ^ (1 - δ) :=
        mul_le_mul_of_nonneg_left hpowBase hC.le
      _ = (δ⁻¹ + 1) * (n : ℝ) ^ (-α) := by rw [hpow]
  have hpowHn : (n : ℝ) ^ (-α) * n = (n : ℝ) ^ (1 - α) := by
    calc
      (n : ℝ) ^ (-α) * n = (n : ℝ) ^ (-α) * (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((-α) + 1) := (Real.rpow_add hnpos (-α) 1).symm
      _ = (n : ℝ) ^ (1 - α) := by congr 1 <;> ring
  have hHn : Real.binEntropy x * n ≤ (δ⁻¹ + 1) * (n : ℝ) ^ (1 - α) := by
    calc
      Real.binEntropy x * n ≤ ((δ⁻¹ + 1) * (n : ℝ) ^ (-α)) * n :=
        mul_le_mul_of_nonneg_right hH (by positivity)
      _ = (δ⁻¹ + 1) * (n : ℝ) ^ (1 - α) := by
        calc
          ((δ⁻¹ + 1) * (n : ℝ) ^ (-α)) * n =
              (δ⁻¹ + 1) * ((n : ℝ) ^ (-α) * n) := by ring
          _ = (δ⁻¹ + 1) * (n : ℝ) ^ (1 - α) := by rw [hpowHn]
  have hConstLarge := hConst n hnConst
  have hConstMul : (δ⁻¹ + 1) < c / 4 * (n : ℝ) ^ (α - h) := by
    have hCross : 4 * (δ⁻¹ + 1) < (n : ℝ) ^ (α - h) * c :=
      (div_lt_iff₀ hc).1 hConstLarge
    rw [mul_comm _ c] at hCross
    nlinarith [hCross]
  have hpowSplit : (n : ℝ) ^ (1 - h) =
      (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (α - h) := by
    calc
      (n : ℝ) ^ (1 - h) = (n : ℝ) ^ ((1 - α) + (α - h)) := by congr 1 <;> ring
      _ = (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (α - h) := by
        rw [Real.rpow_add hnpos]
  have hHtarget : Real.binEntropy x * n ≤ c / 4 * (n : ℝ) ^ (1 - h) := by
    calc
      Real.binEntropy x * n ≤ (δ⁻¹ + 1) * (n : ℝ) ^ (1 - α) := hHn
      _ ≤ (c / 4 * (n : ℝ) ^ (α - h)) * (n : ℝ) ^ (1 - α) :=
        mul_le_mul_of_nonneg_right hConstMul.le (Real.rpow_nonneg hnpos.le _)
      _ = c / 4 * (n : ℝ) ^ (1 - h) := by rw [hpowSplit]; ring
  have haStar : HypercubeRamsey.S04.aStar β γ n * n =
      (n : ℝ) ^ (1 - h) := by
    change (n : ℝ) ^ (-HypercubeRamsey.h4 β γ) * (n : ℝ) =
      (n : ℝ) ^ (1 - HypercubeRamsey.h4 β γ)
    calc
      (n : ℝ) ^ (-HypercubeRamsey.h4 β γ) * (n : ℝ) =
          (n : ℝ) ^ (-HypercubeRamsey.h4 β γ) * (n : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((-HypercubeRamsey.h4 β γ) + 1) :=
        (Real.rpow_add hnpos (-HypercubeRamsey.h4 β γ) 1).symm
      _ = (n : ℝ) ^ (1 - HypercubeRamsey.h4 β γ) := by congr 1 <;> ring
  have hstarTerm : c * HypercubeRamsey.S04.aStar β γ n / 2 * n =
      c / 2 * (n : ℝ) ^ (1 - h) := by
    calc
      c * HypercubeRamsey.S04.aStar β γ n / 2 * n =
          c / 2 * (HypercubeRamsey.S04.aStar β γ n * n) := by ring
      _ = c / 2 * (n : ℝ) ^ (1 - h) := by rw [haStar]
  have hExpSmall : Real.binEntropy x * n -
      c * HypercubeRamsey.S04.aStar β γ n / 2 * n ≤ -(c / 4) * (n : ℝ) ^ (1 - h) := by
    calc
      Real.binEntropy x * n - c * HypercubeRamsey.S04.aStar β γ n / 2 * n =
          Real.binEntropy x * n - c / 2 * (n : ℝ) ^ (1 - h) := by rw [hstarTerm]
      _ ≤ c / 4 * (n : ℝ) ^ (1 - h) - c / 2 * (n : ℝ) ^ (1 - h) :=
        sub_le_sub_right hHtarget _
      _ = -(c / 4) * (n : ℝ) ^ (1 - h) := by ring
  have hcastSub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have hh := congrArg (fun k : ℕ => (k : ℝ)) (Nat.sub_add_cancel hn1)
    push_cast at hh
    linarith
  have hden : (2 : ℝ) ^ (n - 1) = Real.exp (((n - 1 : ℕ) : ℝ) * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hExpId :
      (Real.exp (Real.binEntropy x * n) / (2 : ℝ) ^ (n - 1)) *
          Real.exp ((Real.log 2 - c * HypercubeRamsey.S04.aStar β γ n / 2) * n) =
        2 * Real.exp (Real.binEntropy x * n - c * HypercubeRamsey.S04.aStar β γ n / 2 * n) := by
    rw [hden, ← Real.exp_sub, ← Real.exp_add]
    have hshift : Real.binEntropy x * n -
          ((n - 1 : ℕ) : ℝ) * Real.log 2 +
            (Real.log 2 - c * HypercubeRamsey.S04.aStar β γ n / 2) * n =
        Real.log 2 + (Real.binEntropy x * n - c * HypercubeRamsey.S04.aStar β γ n / 2 * n) := by
      rw [hcastSub]
      ring
    rw [hshift, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hsmallExp := hExp n hnExp
  have hsmall : (n : ℝ) * Real.exp (Real.binEntropy x * n) /
        (2 : ℝ) ^ (n - 1) *
        Real.exp ((Real.log 2 - c * HypercubeRamsey.S04.aStar β γ n / 2) * n) ≤ 1 := by
    have hExpIdN : (n : ℝ) * Real.exp (Real.binEntropy x * n) / (2 : ℝ) ^ (n - 1) *
        Real.exp ((Real.log 2 - c * HypercubeRamsey.S04.aStar β γ n / 2) * n) =
      2 * (n : ℝ) * Real.exp (Real.binEntropy x * n -
        c * HypercubeRamsey.S04.aStar β γ n / 2 * n) := by
      calc
        _ = (n : ℝ) * ((Real.exp (Real.binEntropy x * n) / (2 : ℝ) ^ (n - 1)) *
            Real.exp ((Real.log 2 - c * HypercubeRamsey.S04.aStar β γ n / 2) * n)) := by ring
        _ = (n : ℝ) * (2 * Real.exp (Real.binEntropy x * n -
            c * HypercubeRamsey.S04.aStar β γ n / 2 * n)) := by rw [hExpId]
        _ = 2 * (n : ℝ) * Real.exp (Real.binEntropy x * n -
            c * HypercubeRamsey.S04.aStar β γ n / 2 * n) := by ring
    exact (calc
      (n : ℝ) * Real.exp (Real.binEntropy x * n) / (2 : ℝ) ^ (n - 1) *
          Real.exp ((Real.log 2 - c * HypercubeRamsey.S04.aStar β γ n / 2) * n) =
        2 * (n : ℝ) * Real.exp
          (Real.binEntropy x * n - c * HypercubeRamsey.S04.aStar β γ n / 2 * n) := by
            exact hExpIdN
      _ ≤ 2 * (n : ℝ) * Real.exp (-(c / 4) * (n : ℝ) ^ (1 - h)) := by
        gcongr
      _ < 1 := by
        calc
          2 * (n : ℝ) * Real.exp (-(c / 4) * (n : ℝ) ^ (1 - h)) =
              2 * ((n : ℝ) * Real.exp (-(c / 4) * (n : ℝ) ^ (1 - h))) := by ring
          _ < 2 * (1 / 2 : ℝ) :=
            mul_lt_mul_of_pos_left hsmallExp (by norm_num)
          _ = 1 := by norm_num
    ).le
  have hnearBound := hRadius n hnRadius
  exact ⟨hnearBound.1, hsmall⟩

set_option maxHeartbeats 1500000 in
theorem even_load_prob_proof (β γ K : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hγ : γ < 1) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n ≥ n₀, ∀ N : ℕ,
      HypercubeRamsey.LargeHost C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour}
        {X Y : Finset (Fin N)}
        (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
        (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
        (q : HypercubeRamsey.S04.XProf M tag) (q' : HypercubeRamsey.S04.YProf M tag)
        (J : HypercubeRamsey.S04.Prep M tag →
          HypercubeRamsey.FinProb (HypercubeRamsey.S04.OddRole n → Fin N)),
        HypercubeRamsey.S04.TagBal M tag (2 * K) →
        HypercubeRamsey.S04.ProfOK M tag q q' →
        HypercubeRamsey.S04.EvenFactor M tag q q' →
        HypercubeRamsey.S04.EvenClock M tag →
        HypercubeRamsey.S04.EvenRowFacts M tag →
        (∀ ω, HypercubeRamsey.S04.SPre M tag ω →
          HypercubeRamsey.S04.InjOK M tag ω (J ω)) →
        ∑ ω, (HypercubeRamsey.S04.prepLaw M tag q q').w ω *
            (if HypercubeRamsey.S04.SPre M tag ω then
              (J ω).pr (fun f => ∃ x, 1 < HypercubeRamsey.S04.evenCol M tag ω f x)
             else 0) ≤ 1 / 10 := by
  classical
  obtain ⟨nNear, hNear⟩ := even_near_small β γ hβ hβγ hγ
  obtain ⟨nTail, hTail⟩ := eventually_union_tail_small
  let C₀ : ℝ := 4 * (16 * K + 1)
  refine ⟨max (max nNear nTail) 1, C₀, ?_⟩
  intro n hn N hHost E G X Y M tag q q' J hTag hProf hFactor hClock hRows hInj
  have hnMax : max nNear nTail ≤ n := le_trans (le_max_left (max nNear nTail) 1) hn
  have hnNear : nNear ≤ n := le_trans (le_max_left nNear nTail) hnMax
  have hnTail : nTail ≤ n := le_trans (le_max_right nNear nTail) hnMax
  have hn1 : 1 ≤ n := le_trans (le_max_right (max nNear nTail) 1) hn
  have hn0 : 0 < n := by omega
  letI : Nonempty (HypercubeRamsey.S04.EvenRole n) := by
    exact ⟨⟨fun _ => false, by simp [HypercubeRamsey.IsEvenRole]⟩⟩
  let Ω := HypercubeRamsey.S04.Prep M tag
  let F := HypercubeRamsey.S04.OddRole n → Fin N
  let P₀ : HypercubeRamsey.FinProb Ω := HypercubeRamsey.S04.prepLaw M tag q q'
  let P : HypercubeRamsey.FinProb (Ω × F) := HypercubeRamsey.FinProb.bind P₀ J
  haveI : Nonempty Ω := lane_nonempty_of_finProb P₀
  haveI : Nonempty (Ω × F) := lane_nonempty_of_finProb P
  let U := HypercubeRamsey.S04.EvenRole n
  let good : Ω → Prop := fun ω => HypercubeRamsey.S04.SPre M tag ω
  let succ : Finset (Ω × F) := Finset.univ.filter fun z => good z.1
  let Z : U → Fin N → Ω × F → ℝ := fun a x z =>
    (N : ℝ) * HypercubeRamsey.S04.evenRowAt M tag z.1 a
      (HypercubeRamsey.S04.nbrLabels z.2 a) x
  let L : ℝ := Real.exp
    ((Real.log 2 - HypercubeRamsey.S04.c2 * HypercubeRamsey.S04.aStar β γ n / 2) * n)
  let R : ℕ := 2 * HypercubeRamsey.S04.locR β γ n
  let near : U → Finset U := evenNearSet R
  let H : ℝ := Real.binEntropy ((R : ℝ) / n)
  let f : ℝ := Real.exp (H * n) / (Fintype.card U : ℝ)
  let d : U → Fin N → ℝ :=
    fun a x => (N : ℝ) * HypercubeRamsey.S04.rawEven M tag q q' a x
  let average : Fin N → Ω × F → ℝ :=
    fun x z => (Fintype.card U : ℝ)⁻¹ * ∑ a, Z a x z
  have hU : (Fintype.card U : ℝ) = (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast evenRole_card_eq hn0
  have hUpos : 0 < (Fintype.card U : ℝ) := by rw [hU]; positivity
  have hsmall0 := hNear n hnNear
  have hRadius : R ≤ n / 2 := by simpa [R] using hsmall0.1
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hself : ∀ a : U, a ∈ near a := by
    intro a
    simp [near, evenNearSet, HypercubeRamsey.S04.ballV, _root_.hammingDist]
  have hnear : ∀ a : U, ((near a).card : ℝ) ≤ f * Fintype.card U := by
    intro a
    have hnat := evenNearSet_card_le (R := R) a
    have hball := ballV_volume_bound hn0 hRadius a.1
    have hcast : ((near a).card : ℝ) ≤ Real.exp (H * n) := by
      calc
        ((near a).card : ℝ) ≤ (HypercubeRamsey.S04.ballV a.1 R).card := by
          exact_mod_cast hnat
        _ ≤ Real.exp (H * n) := by simpa [H] using hball
    calc
      ((near a).card : ℝ) ≤ Real.exp (H * n) := hcast
      _ = f * (Fintype.card U : ℝ) := by
        dsimp [f]
        field_simp [ne_of_gt hUpos]
  have hrow0 (ω : Ω) (a : U) (y : Fin n → Fin N) (x : Fin N) :
      0 ≤ HypercubeRamsey.S04.evenRowAt M tag ω a y x :=
    (hRows ω a y).1 x
  have hMean0 (ω : Ω) (a : U) (x : Fin N) :
      0 ≤ HypercubeRamsey.S04.evenMean M tag ω a x :=
    evenMean_nonneg M tag hRows ω a x
  have hZ0 : ∀ a x z, 0 ≤ Z a x z := by
    intro a x z
    dsimp [Z]
    exact mul_nonneg (by positivity) (hrow0 z.1 a
      (HypercubeRamsey.S04.nbrLabels z.2 a) x)
  have hZL : ∀ a x z, z ∈ succ → Z a x z ≤ L := by
    intro a x z hz
    have hfacts := hRows z.1 a (HypercubeRamsey.S04.nbrLabels z.2 a)
    dsimp [Z, L]
    exact hfacts.2.2.2.2 x
  have hd : ∀ a x, 0 ≤ d a x := by
    intro a x
    dsimp [d, HypercubeRamsey.S04.rawEven]
    unfold HypercubeRamsey.FinProb.expect
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (P₀.nonneg ω) (hMean0 ω a x)
  have hmean : ∀ x, (Fintype.card U : ℝ)⁻¹ * ∑ a, d a x ≤ 16 * K := by
    intro x
    have hsum : ∑ a : U, d a x ≤
        8 * ∑ a : U, (N : ℝ) * (M.μ (tag (HypercubeRamsey.S04.key β γ n a.1))).w x := by
      dsimp [d]
      calc
        ∑ a : U, (N : ℝ) * HypercubeRamsey.S04.rawEven M tag q q' a x =
            (N : ℝ) * ∑ a : U, HypercubeRamsey.S04.rawEven M tag q q' a x := by
          rw [← Finset.mul_sum]
        _ ≤ (N : ℝ) *
              (8 * ∑ a : U, (M.μ (tag (HypercubeRamsey.S04.key β γ n a.1))).w x) :=
          mul_le_mul_of_nonneg_left (hProf.even x) (by positivity)
        _ = 8 * ∑ a : U, (N : ℝ) *
              (M.μ (tag (HypercubeRamsey.S04.key β γ n a.1))).w x := by
          calc
            (N : ℝ) * (8 * ∑ a : U,
                (M.μ (tag (HypercubeRamsey.S04.key β γ n a.1))).w x) =
                8 * ((N : ℝ) * ∑ a : U,
                  (M.μ (tag (HypercubeRamsey.S04.key β γ n a.1))).w x) := by ring
            _ = 8 * ∑ a : U, (N : ℝ) *
                  (M.μ (tag (HypercubeRamsey.S04.key β γ n a.1))).w x := by
              rw [Finset.mul_sum]
    calc
      (Fintype.card U : ℝ)⁻¹ * ∑ a : U, d a x ≤
          (Fintype.card U : ℝ)⁻¹ *
            (8 * ∑ a : U, (N : ℝ) *
              (M.μ (tag (HypercubeRamsey.S04.key β γ n a.1))).w x) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hUpos.le)
      _ = 8 * ((Fintype.card U : ℝ)⁻¹ *
            ∑ a : U, (N : ℝ) *
              (M.μ (tag (HypercubeRamsey.S04.key β γ n a.1))).w x) := by ring
      _ ≤ 8 * (2 * K) := mul_le_mul_of_nonneg_left (hTag.1 x) (by norm_num)
      _ = 16 * K := by ring
  have hsmall : (n : ℝ) * f * L ≤ 1 := by
    have h := hsmall0.2
    dsimp [f, L, H, R] at h ⊢
    rw [hU]
    convert h using 1 <;> norm_num [Nat.cast_mul] <;> ring
  have hlabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
    rw [Fintype.card_fin]
    exact_mod_cast hHost.2
  have hD0 : (0 : ℝ) ≤ 16 * K := mul_nonneg (by norm_num) hK.le
  have hjoint : ∀ (x : Fin N) (m : ℕ), m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ z ∈ succ, P.w z * ∏ i, Z (s i) x z ≤
          (2 : ℝ) ^ m * ∏ i, d (s i) x := by
    intro x m hm s hsepNear
    let g : Ω → F → ℝ := fun ω f =>
      ∏ i, (N : ℝ) * HypercubeRamsey.S04.evenRowAt M tag ω (s i)
        (HypercubeRamsey.S04.nbrLabels f (s i)) x
    let meanProd : Ω → ℝ := fun ω =>
      ∏ i, (N : ℝ) * HypercubeRamsey.S04.evenMean M tag ω (s i) x
    have hmeanProd0 (ω : Ω) : 0 ≤ meanProd ω := by
      dsimp [meanProd]
      apply Finset.prod_nonneg
      intro i hi
      exact mul_nonneg (by positivity) (hMean0 ω (s i) x)
    have hsep : HypercubeRamsey.S04.Sep β γ (fun i => (s i).1) := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hij' | hji'
      · have hnot := hsepNear j i hij'
        have hlarge : R < _root_.hammingDist (s i).1 (s j).1 := by
          by_contra hle
          have hle' : _root_.hammingDist (s i).1 (s j).1 ≤ R := le_of_not_gt hle
          exact hnot ((evenNearSet_mem_iff (R := R) (s i) (s j)).2 hle')
        simpa only [R] using hlarge
      · have hnot := hsepNear i j hji'
        have hlarge : R < _root_.hammingDist (s i).1 (s j).1 := by
          by_contra hle
          have hle' : _root_.hammingDist (s i).1 (s j).1 ≤ R := le_of_not_gt hle
          have hle'' : _root_.hammingDist (s j).1 (s i).1 ≤ R := by
            rwa [_root_.hammingDist_comm]
          exact hnot ((evenNearSet_mem_iff (R := R) (s j) (s i)).2 hle'')
        simpa only [R] using hlarge
    have hsplit :
        succ.sum (fun z => P.w z * ∏ i, Z (s i) x z) =
          ∑ ω, if good ω then P₀.w ω * (J ω).expect (g ω) else 0 := by
      simpa only [P, succ, Z, g] using bind_filter_expect P₀ J good g
    have hclockAt (ω : Ω) (hs : good ω) :
        (J ω).expect (g ω) ≤ 2 * meanProd ω := by
      have h := hClock ω (J ω) hs (hInj ω hs) x m s hm hsep
      simpa [g, meanProd] using h
    have hmeanFactor : P₀.expect meanProd ≤ ∏ i, d (s i) x := by
      simpa [meanProd, d, P₀] using hFactor x m s hsep
    have hrawBound :
        succ.sum (fun z => P.w z * ∏ i, Z (s i) x z) ≤ 2 * ∏ i, d (s i) x := by
      rw [hsplit]
      calc
        (∑ ω, if good ω then P₀.w ω * (J ω).expect (g ω) else 0) ≤
            ∑ ω, P₀.w ω * (2 * meanProd ω) := by
          apply Finset.sum_le_sum
          intro ω hω
          by_cases hs : good ω
          · simp only [hs, ↓reduceIte]
            exact mul_le_mul_of_nonneg_left (hclockAt ω hs) (P₀.nonneg ω)
          · simp only [hs, ↓reduceIte]
            exact mul_nonneg (P₀.nonneg ω)
              (mul_nonneg (by norm_num) (hmeanProd0 ω))
        _ = 2 * P₀.expect meanProd := by
          unfold HypercubeRamsey.FinProb.expect
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω hω
          ring
        _ ≤ 2 * ∏ i, d (s i) x :=
          mul_le_mul_of_nonneg_left hmeanFactor (by norm_num)
    by_cases hm0 : m = 0
    · subst m
      have hgOne (ω : Ω) : g ω = fun _ => (1 : ℝ) := by
        funext f
        simp [g]
      have hgExpect (ω : Ω) : (J ω).expect (g ω) = 1 := by
        rw [hgOne ω]
        exact HypercubeRamsey.FinProb.expect_const (J ω) 1
      have hmassEq : (∑ ω, if good ω then P₀.w ω *
          (J ω).expect (g ω) else 0) = P₀.pr good := by
        calc
          (∑ ω, if good ω then P₀.w ω * (J ω).expect (g ω) else 0) =
              ∑ ω, if good ω then P₀.w ω else 0 := by
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hs : good ω
            · simp only [hs, ↓reduceIte]
              rw [hgExpect]
              ring
            · simp [hs]
          _ = P₀.pr good := by
            unfold HypercubeRamsey.FinProb.pr
            rfl
      have hprle : P₀.pr good ≤ 1 := by
        have hnot := HypercubeRamsey.S04.pr_nonneg P₀ (fun ω => ¬ good ω)
        have hadd := HypercubeRamsey.S04.pr_add_pr_not P₀ good
        linarith
      have hMass : (∑ ω, if good ω then P₀.w ω *
          (J ω).expect (g ω) else 0) ≤ 1 := hmassEq.trans_le hprle
      rw [hsplit]
      simpa using hMass
    · have hm1 : 1 ≤ m := by omega
      have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ m := by
        have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hmReal
        simpa only [Real.rpow_one, Real.rpow_natCast] using hp
      have hdprod : 0 ≤ ∏ i, d (s i) x :=
        Finset.prod_nonneg fun i hi => hd (s i) x
      exact hrawBound.trans (mul_le_mul_of_nonneg_right hpow hdprod)
  have hscatRaw := HypercubeRamsey.scatteredMoments_union_labels
    (Ω := Ω × F) (U := U) (Label := Fin N)
    (P := P) (succ := succ) (Z := Z) hZ0
    (L := L) hL hZL (near := near) hself (f := f) hf hnear
    (n := n) hn0 (K := 2) (D₀ := 16 * K) (by norm_num) hD0
    (d := d) hd hmean hjoint hsmall hlabels
  have hscat : (∑ z, if z ∈ succ ∧ ∃ x, 8 * (16 * K + 1) < average x z
      then P.w z else 0) ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    convert hscatRaw using 1 <;> simp [average, mul_assoc] <;> ring
  have hratio : 2 * C₀ ≤ (N : ℝ) / (Fintype.card U : ℝ) := by
    have hpowNat : 2 ^ n = 2 * 2 ^ (n - 1) := by
      calc
        2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn1]
        _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (n - 1) := by omega
    have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by exact_mod_cast hpowNat
    apply (le_div_iff₀ hUpos).2
    rw [hU]
    calc
      2 * C₀ * (2 : ℝ) ^ (n - 1) = C₀ * (2 : ℝ) ^ n := by rw [hpow]; ring
      _ ≤ (N : ℝ) := hHost.1
  have havg (z : Ω × F) (x : Fin N) : average x z =
      ((N : ℝ) / (Fintype.card U : ℝ)) *
        HypercubeRamsey.S04.evenCol M tag z.1 z.2 x := by
    have hsum : ∑ a : U, Z a x z = (N : ℝ) *
        HypercubeRamsey.S04.evenCol M tag z.1 z.2 x := by
      dsimp [Z]
      rw [HypercubeRamsey.S04.evenCol, ← Finset.mul_sum]
    dsimp [average]
    rw [hsum, div_eq_mul_inv]
    ring
  have hbadTo (z : Ω × F) (hgood : good z.1)
      (hbad : ∃ x, 1 < HypercubeRamsey.S04.evenCol M tag z.1 z.2 x) :
      ∃ x, 8 * (16 * K + 1) < average x z := by
    obtain ⟨x, hx⟩ := hbad
    have hratioPos : 0 < (N : ℝ) / (Fintype.card U : ℝ) :=
      lt_of_lt_of_le (by dsimp [C₀]; positivity) hratio
    have hbase : 8 * (16 * K + 1) ≤ (N : ℝ) / (Fintype.card U : ℝ) := by
      dsimp [C₀] at hratio
      nlinarith
    have hlt := mul_lt_mul_of_pos_left hx hratioPos
    have hlt' : (N : ℝ) / (Fintype.card U : ℝ) <
        ((N : ℝ) / (Fintype.card U : ℝ)) *
          HypercubeRamsey.S04.evenCol M tag z.1 z.2 x := by
      simpa only [mul_one] using hlt
    refine ⟨x, ?_⟩
    rw [havg z x]
    exact hbase.trans_lt hlt'
  let gBad : Ω → F → ℝ := fun ω f =>
    if ∃ x, 1 < HypercubeRamsey.S04.evenCol M tag ω f x then 1 else 0
  have hPrIndicator (ω : Ω) :
      (J ω).pr (fun f => ∃ x, 1 < HypercubeRamsey.S04.evenCol M tag ω f x) =
        (J ω).expect (gBad ω) := by
    classical
    unfold HypercubeRamsey.FinProb.pr HypercubeRamsey.FinProb.expect
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hb : ∃ x, 1 < HypercubeRamsey.S04.evenCol M tag ω f x
    · simp [gBad, hb]
    · simp [gBad, hb]
  have hdesiredEq :
      (∑ ω, P₀.w ω * (if good ω then
        (J ω).pr (fun f => ∃ x, 1 < HypercubeRamsey.S04.evenCol M tag ω f x) else 0)) =
        (succ.sum fun z => P.w z * gBad z.1 z.2) := by
    have hbind := bind_filter_expect P₀ J good gBad
    calc
      (∑ ω, P₀.w ω * (if good ω then
          (J ω).pr (fun f => ∃ x, 1 < HypercubeRamsey.S04.evenCol M tag ω f x) else 0)) =
          ∑ ω, if good ω then P₀.w ω * (J ω).expect (gBad ω) else 0 := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hs : good ω
        · simp [hs, hPrIndicator ω]
        · simp [hs]
      _ = succ.sum (fun z => P.w z * gBad z.1 z.2) := by
        simpa [succ, P] using hbind.symm
  have hpairBound :
      (succ.sum fun z => P.w z * gBad z.1 z.2) ≤
        ∑ z, if z ∈ succ ∧ ∃ x, 8 * (16 * K + 1) < average x z then P.w z else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z hz
    by_cases hs : good z.1
    · by_cases hb : ∃ x, 1 < HypercubeRamsey.S04.evenCol M tag z.1 z.2 x
      · have he := hbadTo z hs hb
        simp [succ, gBad, hs, hb, he]
      · simp [succ, gBad, hs, hb]
        split_ifs
        · exact P.nonneg z
        · exact le_rfl
    · simp [succ, gBad, hs]
  have hprob :
      (∑ ω, P₀.w ω * (if good ω then
        (J ω).pr (fun f => ∃ x, 1 < HypercubeRamsey.S04.evenCol M tag ω f x) else 0)) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    rw [hdesiredEq]
    exact hpairBound.trans hscat
  exact hprob.trans (hTail n hnTail)

set_option maxHeartbeats 1000000 in
theorem odd_load_prob_proof (β γ K : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hγ : γ < 1) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n ≥ n₀, ∀ N : ℕ,
      HypercubeRamsey.LargeHost C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : HypercubeRamsey.Colour}
        {X Y : Finset (Fin N)}
        (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
        (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
        (q : HypercubeRamsey.S04.XProf M tag) (q' : HypercubeRamsey.S04.YProf M tag),
        HypercubeRamsey.S04.TagBal M tag (2 * K) →
        HypercubeRamsey.S04.ProfOK M tag q q' →
        HypercubeRamsey.S04.OddFactor M tag q q' →
        HypercubeRamsey.S04.OddCap M tag →
        (HypercubeRamsey.S04.prepLaw M tag q q').pr
          (fun ω => ∃ y, 1 / 10 < HypercubeRamsey.S04.oddCol M tag ω y) ≤ 1 / 10 := by
  classical
  obtain ⟨nLoad, hLoad⟩ := odd_near_small β γ hβ hβγ hγ
  obtain ⟨nTail, hTail⟩ := eventually_union_tail_small
  let C₀ : ℝ := 20 * (4 * K + 1)
  refine ⟨max (max nLoad nTail) 1, C₀, ?_⟩
  intro n hn N hHost E G X Y M tag q q' hTag hProf hFactor hCap
  have hnMax : max nLoad nTail ≤ n :=
    le_trans (le_max_left (max nLoad nTail) 1) hn
  have hnLoad : nLoad ≤ n := le_trans (le_max_left _ _) hnMax
  have hnTail : nTail ≤ n := le_trans (le_max_right _ _) hnMax
  have hn1 : 1 ≤ n := le_trans (le_max_right (max nLoad nTail) 1) hn
  have hn0 : 0 < n := by omega
  letI : Nonempty (HypercubeRamsey.S04.OddRole n) := by
    let e : HypercubeRamsey.S04.EvenRole n :=
      ⟨fun _ => false, by simp [HypercubeRamsey.IsEvenRole]⟩
    exact ⟨HypercubeRamsey.S04.oddNbr e ⟨0, by omega⟩⟩
  let P : HypercubeRamsey.FinProb (HypercubeRamsey.S04.Prep M tag) :=
    HypercubeRamsey.S04.prepLaw M tag q q'
  have hPne : Nonempty (HypercubeRamsey.S04.Prep M tag) := by
    by_contra hne
    haveI : IsEmpty (HypercubeRamsey.S04.Prep M tag) := ⟨fun ω => hne ⟨ω⟩⟩
    have hzero : (∑ ω : HypercubeRamsey.S04.Prep M tag, P.w ω) = 0 := by simp
    rw [P.sum_eq_one] at hzero
    norm_num at hzero
  letI := hPne
  let U := HypercubeRamsey.S04.OddRole n
  let Z : U → Fin N → HypercubeRamsey.S04.Prep M tag → ℝ :=
    fun u y ω => (N : ℝ) * HypercubeRamsey.S04.oddRow M tag ω u y
  let L : ℝ := Real.exp (2 * (n : ℝ) ^ γ)
  let R : ℕ := 2 * HypercubeRamsey.S04.locR β γ n
  let near : U → Finset U := oddNearSet R
  let H : ℝ := Real.binEntropy ((R : ℝ) / n)
  let f : ℝ := Real.exp (H * n) / (Fintype.card U : ℝ)
  let d : U → Fin N → ℝ :=
    fun u y => (N : ℝ) * HypercubeRamsey.S04.rawOdd M tag q q' u y
  let average : Fin N → HypercubeRamsey.S04.Prep M tag → ℝ :=
    fun y ω => (Fintype.card U : ℝ)⁻¹ * ∑ u, Z u y ω
  have hU : (Fintype.card U : ℝ) = (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast oddRole_card_eq hn0
  have hUpos : 0 < (Fintype.card U : ℝ) := by rw [hU]; positivity
  have hsmall0 := hLoad n hnLoad
  have hRadius : R ≤ n / 2 := by simpa [R] using hsmall0.1
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hself : ∀ u : U, u ∈ near u := by
    intro u
    simp [near, oddNearSet, HypercubeRamsey.S04.ballV, _root_.hammingDist]
  have hnear : ∀ u : U, ((near u).card : ℝ) ≤ f * Fintype.card U := by
    intro u
    have hnat := oddNearSet_card_le (R := R) u
    have hball := ballV_volume_bound hn0 hRadius u.1
    have hcast : ((near u).card : ℝ) ≤ Real.exp (H * n) := by
      calc
        ((near u).card : ℝ) ≤ (HypercubeRamsey.S04.ballV u.1 R).card := by
          exact_mod_cast hnat
        _ ≤ Real.exp (H * n) := by simpa [H] using hball
    calc
      ((near u).card : ℝ) ≤ Real.exp (H * n) := hcast
      _ = f * (Fintype.card U : ℝ) := by
        dsimp [f]
        field_simp [ne_of_gt hUpos]
  have hZ0 : ∀ u y ω, 0 ≤ Z u y ω := by
    intro u y ω
    dsimp [Z]
    exact mul_nonneg (by positivity) (oddRow_nonneg M tag ω u y)
  have hZL : ∀ u y ω, ω ∈ Finset.univ → Z u y ω ≤ L := by
    intro u y ω _
    dsimp [Z, L]
    exact hCap ω u y
  have hd : ∀ u y, 0 ≤ d u y := by
    intro u y
    dsimp [d]
    apply mul_nonneg (by positivity)
    unfold HypercubeRamsey.S04.rawOdd HypercubeRamsey.FinProb.expect
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (P.nonneg ω) (oddRow_nonneg M tag ω u y)
  have hmean : ∀ y, (Fintype.card U : ℝ)⁻¹ * ∑ u, d u y ≤ 4 * K := by
    intro y
    have hterm (u : U) : d u y ≤ 2 * (N : ℝ) *
        (M.ν (tag (HypercubeRamsey.S04.key β γ n u.1))).w y := by
      dsimp [d]
      have hp := hProf.odd u y
      have hmul := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ (N : ℝ))
      nlinarith
    have hsum : ∑ u : U, d u y ≤
        2 * ∑ u : U, (N : ℝ) * (M.ν (tag (HypercubeRamsey.S04.key β γ n u.1))).w y := by
      calc
        ∑ u : U, d u y ≤
            ∑ u : U, 2 * (N : ℝ) * (M.ν (tag (HypercubeRamsey.S04.key β γ n u.1))).w y :=
          Finset.sum_le_sum fun u _ => hterm u
        _ = 2 * ∑ u : U, (N : ℝ) *
              (M.ν (tag (HypercubeRamsey.S04.key β γ n u.1))).w y := by
          calc
            _ = ∑ u : U, 2 * ((N : ℝ) *
                  (M.ν (tag (HypercubeRamsey.S04.key β γ n u.1))).w y) := by
              apply Finset.sum_congr rfl
              intro u hu
              ring
            _ = _ := by rw [Finset.mul_sum]
    calc
      (Fintype.card U : ℝ)⁻¹ * ∑ u : U, d u y ≤
          (Fintype.card U : ℝ)⁻¹ *
            (2 * ∑ u : U, (N : ℝ) *
              (M.ν (tag (HypercubeRamsey.S04.key β γ n u.1))).w y) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hUpos.le)
      _ = 2 * ((Fintype.card U : ℝ)⁻¹ *
            ∑ u : U, (N : ℝ) *
              (M.ν (tag (HypercubeRamsey.S04.key β γ n u.1))).w y) := by ring
      _ ≤ 2 * (2 * K) := mul_le_mul_of_nonneg_left (hTag.2 y) (by norm_num)
      _ = 4 * K := by ring
  have hjoint : ∀ y (m : ℕ), m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ Finset.univ, P.w ω * ∏ i, Z (s i) y ω ≤
          (1 : ℝ) ^ m * ∏ i, d (s i) y := by
    intro y m hm s hsepNear
    have hsep : HypercubeRamsey.S04.Sep β γ (fun i => (s i).1) := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hij' | hji'
      · have hnot := hsepNear j i hij'
        have hlarge : R < _root_.hammingDist (s i).1 (s j).1 := by
          by_contra hle
          have hle' : _root_.hammingDist (s i).1 (s j).1 ≤ R := le_of_not_gt hle
          exact hnot ((oddNearSet_mem_iff (R := R) (s i) (s j)).2 hle')
        simpa only [R] using hlarge
      · have hnot := hsepNear i j hji'
        have hlarge : R < _root_.hammingDist (s i).1 (s j).1 := by
          by_contra hle
          have hle' : _root_.hammingDist (s i).1 (s j).1 ≤ R := le_of_not_gt hle
          have hle'' : _root_.hammingDist (s j).1 (s i).1 ≤ R := by
            rwa [_root_.hammingDist_comm]
          exact hnot ((oddNearSet_mem_iff (R := R) (s j) (s i)).2 hle'')
        simpa only [R] using hlarge
    have hfactor := hFactor y m s hsep
    change (HypercubeRamsey.S04.prepLaw M tag q q').expect
        (fun ω => ∏ i, (N : ℝ) * HypercubeRamsey.S04.oddRow M tag ω (s i) y) ≤
      (1 : ℝ) ^ m * ∏ i, (N : ℝ) *
        HypercubeRamsey.S04.rawOdd M tag q q' (s i) y
    simpa only [one_pow, one_mul] using hfactor
  have hsmall : (n : ℝ) * f * L ≤ 1 := by
    have h := hsmall0.2
    dsimp [f, L, H, R] at h ⊢
    rw [hU]
    convert h using 1 <;> norm_num [Nat.cast_mul] <;> ring
  have hlabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
    rw [Fintype.card_fin]
    exact_mod_cast hHost.2
  have hD0 : (0 : ℝ) ≤ 4 * K := mul_nonneg (by norm_num) hK.le
  have hscatRaw := HypercubeRamsey.scatteredMoments_union_labels
    (Ω := HypercubeRamsey.S04.Prep M tag)
    (U := HypercubeRamsey.S04.OddRole n) (Label := Fin N)
    (P := P) (succ := Finset.univ) (Z := Z) hZ0
    (L := L) hL hZL (near := near) hself (f := f) hf hnear
    (n := n) hn0 (K := 1) (D₀ := 4 * K) (by norm_num) hD0
    (d := d) hd hmean hjoint hsmall hlabels
  have hscat : (∑ ω, if ω ∈ Finset.univ ∧ ∃ y, 4 * (4 * K + 1) < average y ω
      then P.w ω else 0) ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    change (∑ ω, if ω ∈ Finset.univ ∧ ∃ y,
        4 * (4 * K + 1) < (Fintype.card (HypercubeRamsey.S04.OddRole n) : ℝ)⁻¹ *
          ∑ u : HypercubeRamsey.S04.OddRole n, Z u y ω
      then P.w ω else 0) ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n
    simpa only [mul_one] using hscatRaw
  have hratio : 2 * C₀ ≤ (N : ℝ) / (Fintype.card U : ℝ) := by
    have hpowNat : 2 ^ n = 2 * 2 ^ (n - 1) := by
      calc
        2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn1]
        _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (n - 1) := by omega
    have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by exact_mod_cast hpowNat
    apply (le_div_iff₀ hUpos).2
    rw [hU]
    calc
      2 * C₀ * (2 : ℝ) ^ (n - 1) = C₀ * (2 : ℝ) ^ n := by rw [hpow]; ring
      _ ≤ (N : ℝ) := hHost.1
  have havg (ω : HypercubeRamsey.S04.Prep M tag) (y : Fin N) :
      average y ω = ((N : ℝ) / (Fintype.card U : ℝ)) *
        HypercubeRamsey.S04.oddCol M tag ω y := by
    have hsum : ∑ u : U, Z u y ω = (N : ℝ) *
        HypercubeRamsey.S04.oddCol M tag ω y := by
      dsimp [Z]
      rw [HypercubeRamsey.S04.oddCol, ← Finset.mul_sum]
    dsimp [average]
    rw [hsum, div_eq_mul_inv]
    ring
  have hbadTo (ω : HypercubeRamsey.S04.Prep M tag)
      (hbad : ∃ y, 1 / 10 < HypercubeRamsey.S04.oddCol M tag ω y) :
      ∃ y, 4 * (4 * K + 1) < average y ω := by
    obtain ⟨y, hy⟩ := hbad
    have hratioPos : 0 < (N : ℝ) / (Fintype.card U : ℝ) :=
      lt_of_lt_of_le (by dsimp [C₀]; positivity) hratio
    have hbase : 4 * (4 * K + 1) ≤
        ((N : ℝ) / (Fintype.card U : ℝ)) * (1 / 10 : ℝ) := by
      dsimp [C₀] at hratio
      nlinarith
    have hlt := mul_lt_mul_of_pos_left hy hratioPos
    refine ⟨y, ?_⟩
    rw [havg ω y]
    exact hbase.trans_lt hlt
  let event : HypercubeRamsey.S04.Prep M tag → Prop :=
    fun ω => ∃ y, 4 * (4 * K + 1) <
      (Fintype.card (HypercubeRamsey.S04.OddRole n) : ℝ)⁻¹ *
        ∑ u : HypercubeRamsey.S04.OddRole n, Z u y ω
  have htailP : P.pr event ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    classical
    have hEq : P.pr event =
        ∑ ω, if ω ∈ Finset.univ ∧ event ω then P.w ω else 0 := by
      unfold HypercubeRamsey.FinProb.pr
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases he : event ω <;> simp [he]
    rw [hEq]
    exact hscat
  have hmono : P.pr (fun ω => ∃ y, 1 / 10 < HypercubeRamsey.S04.oddCol M tag ω y) ≤
      P.pr event := HypercubeRamsey.S04.pr_mono P (fun ω hbad => by
        obtain ⟨y, hy⟩ := hbadTo ω hbad
        exact ⟨y, by simpa [average, U] using hy⟩)
  have hprob := hmono.trans htailP
  change P.pr (fun ω => ∃ y, 1 / 10 < HypercubeRamsey.S04.oddCol M tag ω y) ≤ 1 / 10
  exact hprob.trans (hTail n hnTail)

private theorem predGateWeight_nonneg
    {β γ : ℝ} {G : HypercubeRamsey.Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (ω : HypercubeRamsey.S04.Prep M tag)
    (a : HypercubeRamsey.S04.EvenRole n) (c : HypercubeRamsey.S04.Loc β γ n) :
    0 ≤ predGateWeight M tag a c ω := by
  classical
  unfold predGateWeight
  apply Finset.sum_nonneg
  intro y hy
  apply mul_nonneg
  · apply mul_nonneg
    · split_ifs <;> norm_num
    · apply Finset.prod_nonneg
      intro j hj
      exact oddRow_nonneg M tag ω (HypercubeRamsey.S04.oddNbr a j) (y j)
  · split_ifs <;> norm_num

private theorem pred_fail_pair_bound
    {β γ : ℝ} {G : HypercubeRamsey.Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
    (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
    (hGeo : HypercubeRamsey.S04.GeoCons M tag)
    (ω : HypercubeRamsey.S04.Prep M tag)
    (hSPre : HypercubeRamsey.S04.SPre M tag ω)
    (J : HypercubeRamsey.FinProb (HypercubeRamsey.S04.OddRole n → Fin N))
    (hInj : HypercubeRamsey.S04.InjOK M tag ω J)
    (a : HypercubeRamsey.S04.EvenRole n)
    (c : HypercubeRamsey.S04.Loc β γ n) :
    J.pr (fun f => HypercubeRamsey.S04.sel M tag ω a.1 = some c ∧
      ¬ HypercubeRamsey.S04.PredOK M tag ω a c
        (HypercubeRamsey.S04.nbrLabels f a)) ≤
      2 * predGateWeight M tag a c ω := by
  classical
  let P : HypercubeRamsey.S04.OddRole n → HypercubeRamsey.FinProb (Fin N) :=
    fun u => HypercubeRamsey.S04.oddDraw M tag ω u
  let S := nbrSet a
  let failAt : (Fin n → Fin N) → Prop :=
    fun y => HypercubeRamsey.S04.sel M tag ω a.1 = some c ∧
      ¬ HypercubeRamsey.S04.PredOK M tag ω a c y
  let g : (HypercubeRamsey.S04.OddRole n → Fin N) → ℝ :=
    fun f => if failAt (HypercubeRamsey.S04.nbrLabels f a) then 1 else 0
  let gy : (Fin n → Fin N) → ℝ := fun y => if failAt y then 1 else 0
  let hgeo := hGeo ω hSPre.1
  have hgood (u : HypercubeRamsey.S04.OddRole n) : HypercubeRamsey.S04.OddOK M tag ω u :=
    hgeo.2 u
  have hrow (u : HypercubeRamsey.S04.OddRole n) (y : Fin N) :
      HypercubeRamsey.S04.oddRow M tag ω u y = (P u).w y := by
    simp [P, HypercubeRamsey.S04.oddRow, hgood u]
  have hScardNat : S.card ≤ n := by
    dsimp [S, nbrSet]
    calc
      (Finset.univ.image (HypercubeRamsey.S04.oddNbr a)).card ≤
          (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have hnSq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hScard : (S.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc
      (S.card : ℝ) ≤ n := by exact_mod_cast hScardNat
      _ ≤ (n : ℝ) ^ 2 := hnSq
  have hjoint : ∀ (S' : Finset (HypercubeRamsey.S04.OddRole n))
      (o : HypercubeRamsey.S04.OddRole n → Fin N), (S'.card : ℝ) ≤ (n : ℝ) ^ 2 →
      J.pr (fun f => ∀ u ∈ S', f u = o u) ≤
        2 * ∏ u ∈ S', (P u).w (o u) := by
    intro S' o hcard
    simpa only [hrow] using hInj.2 S' o hcard
  have hdep : HypercubeRamsey.FinProb.DependsOn g S := by
    intro f f' hagree
    have hlabels : HypercubeRamsey.S04.nbrLabels f a =
        HypercubeRamsey.S04.nbrLabels f' a := by
      funext j
      exact hagree (HypercubeRamsey.S04.oddNbr a j) (by
        dsimp [S, nbrSet]
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    simp [g, hlabels]
  have hg0 (f : HypercubeRamsey.S04.OddRole n → Fin N) : 0 ≤ g f := by
    dsimp [g]
    split_ifs <;> norm_num
  have hcomp := joint_expect_le_product P J S ((n : ℝ) ^ 2) hScard hjoint g hg0 hdep
  have hpr : J.pr (fun f => failAt (HypercubeRamsey.S04.nbrLabels f a)) = J.expect g := by
    unfold HypercubeRamsey.FinProb.pr HypercubeRamsey.FinProb.expect
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hfail : failAt (HypercubeRamsey.S04.nbrLabels f a)
    · simp [g, hfail]
    · simp [g, hfail]
  have hselected_local :
      HypercubeRamsey.S04.sel M tag ω a.1 = some c →
        HypercubeRamsey.S04.EvLocal M tag ω a c := by
    intro hsel
    obtain ⟨c₀, hc₀⟩ := hgeo.1 a
    have heq : c = c₀ := Option.some.inj (hsel.symm.trans hc₀.sel_eq)
    subst c
    exact hc₀
  have hgateInd (y : Fin n → Fin N) :
      gy y ≤
        (if HypercubeRamsey.S04.EvLocal M tag ω a c then 1 else 0) *
          (if ¬ HypercubeRamsey.S04.PredOK M tag ω a c y then 1 else 0) := by
    by_cases hsel : HypercubeRamsey.S04.sel M tag ω a.1 = some c
    · have hev := hselected_local hsel
      simp [gy, failAt, hsel, hev]
    · simp [gy, failAt, hsel]
      split_ifs <;> norm_num
  let Q : HypercubeRamsey.FinProb (Fin n → Fin N) :=
    HypercubeRamsey.FinProb.pi (fun j : Fin n =>
      HypercubeRamsey.S04.oddDraw M tag ω (HypercubeRamsey.S04.oddNbr a j))
  have hQle : Q.expect gy ≤ predGateWeight M tag a c ω := by
    unfold HypercubeRamsey.FinProb.expect predGateWeight
    apply Finset.sum_le_sum
    intro y hy
    have hweight : Q.w y =
        ∏ j, HypercubeRamsey.S04.oddRow M tag ω
          (HypercubeRamsey.S04.oddNbr a j) (y j) := by
      simp [Q, HypercubeRamsey.FinProb.pi, P, hrow]
    rw [hweight]
    have hprod0 : 0 ≤ ∏ j, HypercubeRamsey.S04.oddRow M tag ω
        (HypercubeRamsey.S04.oddNbr a j) (y j) := by
      apply Finset.prod_nonneg
      intro j hj
      exact oddRow_nonneg M tag ω (HypercubeRamsey.S04.oddNbr a j) (y j)
    calc
      (∏ j, HypercubeRamsey.S04.oddRow M tag ω
          (HypercubeRamsey.S04.oddNbr a j) (y j)) * gy y ≤
        (∏ j, HypercubeRamsey.S04.oddRow M tag ω
          (HypercubeRamsey.S04.oddNbr a j) (y j)) *
          ((if HypercubeRamsey.S04.EvLocal M tag ω a c then 1 else 0) *
            (if ¬ HypercubeRamsey.S04.PredOK M tag ω a c y then 1 else 0)) :=
          mul_le_mul_of_nonneg_left (hgateInd y) hprod0
      _ = (if HypercubeRamsey.S04.EvLocal M tag ω a c then 1 else 0) *
          (∏ j, HypercubeRamsey.S04.oddRow M tag ω
            (HypercubeRamsey.S04.oddNbr a j) (y j)) *
          (if ¬ HypercubeRamsey.S04.PredOK M tag ω a c y then 1 else 0) := by ring
  have hodd := odd_neighbor_expect M tag ω a gy
  have hPi : (HypercubeRamsey.FinProb.pi P).expect g = Q.expect gy := by
    simpa [P, g, gy, Q, HypercubeRamsey.S04.oddDrawLaw] using hodd
  calc
    J.pr (fun f => HypercubeRamsey.S04.sel M tag ω a.1 = some c ∧
        ¬ HypercubeRamsey.S04.PredOK M tag ω a c
          (HypercubeRamsey.S04.nbrLabels f a)) = J.expect g := by
            simpa [failAt] using hpr
    _ ≤ 2 * (HypercubeRamsey.FinProb.pi P).expect g := hcomp
    _ = 2 * Q.expect gy := by rw [hPi]
    _ ≤ 2 * predGateWeight M tag a c ω :=
      mul_le_mul_of_nonneg_left hQle (by norm_num)

theorem pred_fail_prob_proof (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {G : HypercubeRamsey.Colour} {X Y : Finset (Fin N)}
      (M : HypercubeRamsey.S04.Menu4 β γ G n N E X Y)
      (tag : HypercubeRamsey.S04.Key β γ n → M.ι)
      (q : HypercubeRamsey.S04.XProf M tag) (q' : HypercubeRamsey.S04.YProf M tag)
      (J : HypercubeRamsey.S04.Prep M tag →
        HypercubeRamsey.FinProb (HypercubeRamsey.S04.OddRole n → Fin N)),
      HypercubeRamsey.S04.GeoCons M tag → HypercubeRamsey.S04.RefIndep M tag →
      HypercubeRamsey.S04.Resample M tag q q' →
      (∀ ω, HypercubeRamsey.S04.SPre M tag ω →
        HypercubeRamsey.S04.InjOK M tag ω (J ω)) →
      ∑ ω, (HypercubeRamsey.S04.prepLaw M tag q q').w ω *
          (if HypercubeRamsey.S04.SPre M tag ω then
            (J ω).pr (fun f => ∃ a, HypercubeRamsey.S04.PredFail M tag ω a
              (HypercubeRamsey.S04.nbrLabels f a)) else 0) ≤ 1 / 10 := by
  classical
  obtain ⟨n₀, hTail⟩ := pred_fail_union_tail_small β γ hβ hβγ hγ
  refine ⟨n₀, ?_⟩
  intro n hn N E G X Y M tag q q' J hGeo hRef hResample hInj
  let P : HypercubeRamsey.FinProb (HypercubeRamsey.S04.Prep M tag) :=
    HypercubeRamsey.S04.prepLaw M tag q q'
  let I := HypercubeRamsey.S04.EvenRole n × HypercubeRamsey.S04.Loc β γ n
  let pairBad : HypercubeRamsey.S04.Prep M tag → I →
      (HypercubeRamsey.S04.OddRole n → Fin N) → Prop :=
    fun ω p f => HypercubeRamsey.S04.sel M tag ω p.1.1 = some p.2 ∧
      ¬ HypercubeRamsey.S04.PredOK M tag ω p.1 p.2
        (HypercubeRamsey.S04.nbrLabels f p.1)
  let bad : HypercubeRamsey.S04.Prep M tag →
      (HypercubeRamsey.S04.OddRole n → Fin N) → Prop :=
    fun ω f => ∃ a, HypercubeRamsey.S04.PredFail M tag ω a
      (HypercubeRamsey.S04.nbrLabels f a)
  have hpoint (ω : HypercubeRamsey.S04.Prep M tag) :
      (if HypercubeRamsey.S04.SPre M tag ω then (J ω).pr (bad ω) else 0) ≤
        2 * ∑ p : I, predGateWeight M tag p.1 p.2 ω := by
    by_cases hs : HypercubeRamsey.S04.SPre M tag ω
    · simp only [if_pos hs]
      have hmono : (J ω).pr (bad ω) ≤
          (J ω).pr (fun f => ∃ p : I, pairBad ω p f) :=
        HypercubeRamsey.S04.pr_mono (J ω) (by
          intro f hbad
          change ∃ a, ∃ c,
            HypercubeRamsey.S04.sel M tag ω a.1 = some c ∧
            ¬ HypercubeRamsey.S04.PredOK M tag ω a c
              (HypercubeRamsey.S04.nbrLabels f a) at hbad
          rcases hbad with ⟨a, c, hsel, hfail⟩
          exact ⟨(a, c), hsel, hfail⟩)
      have hUnion := pr_fintype_union (J ω) (pairBad ω)
      calc
        (J ω).pr (bad ω) ≤ (J ω).pr (fun f => ∃ p : I, pairBad ω p f) := hmono
        _ ≤ ∑ p : I, (J ω).pr (pairBad ω p) := hUnion
        _ ≤ ∑ p : I, 2 * predGateWeight M tag p.1 p.2 ω := by
          apply Finset.sum_le_sum
          intro p hp
          exact pred_fail_pair_bound M tag hGeo ω hs (J ω) (hInj ω hs) p.1 p.2
        _ = 2 * ∑ p : I, predGateWeight M tag p.1 p.2 ω := by
          rw [← Finset.mul_sum]
    · simp only [if_neg hs]
      have hsum0 : 0 ≤ ∑ p : I, predGateWeight M tag p.1 p.2 ω := by
        apply Finset.sum_nonneg
        intro p hp
        exact predGateWeight_nonneg M tag ω p.1 p.2
      exact mul_nonneg (by norm_num) hsum0
  have hsumExpect :
      P.expect (fun ω => ∑ p : I, predGateWeight M tag p.1 p.2 ω) =
        ∑ p : I, P.expect (fun ω => predGateWeight M tag p.1 p.2 ω) := by
    unfold HypercubeRamsey.FinProb.expect
    calc
      (∑ ω, P.w ω * (∑ p : I, predGateWeight M tag p.1 p.2 ω)) =
          ∑ ω, ∑ p : I, P.w ω * predGateWeight M tag p.1 p.2 ω := by
        apply Finset.sum_congr rfl
        intro ω hω
        simpa using (Finset.mul_sum (s := (Finset.univ : Finset I))
          (f := fun p : I => predGateWeight M tag p.1 p.2 ω) (a := P.w ω))
      _ = ∑ p : I, ∑ ω, P.w ω * predGateWeight M tag p.1 p.2 ω := by
        rw [Finset.sum_comm]
  have hbound :
      P.expect (fun ω => 2 * ∑ p : I, predGateWeight M tag p.1 p.2 ω) ≤
        2 * (Fintype.card I : ℝ) * HypercubeRamsey.S04.eps4 β γ n := by
    calc
      P.expect (fun ω => 2 * ∑ p : I, predGateWeight M tag p.1 p.2 ω) =
          2 * P.expect (fun ω => ∑ p : I, predGateWeight M tag p.1 p.2 ω) :=
        HypercubeRamsey.FinProb.expect_smul P 2 _
      _ = 2 * ∑ p : I, P.expect (fun ω => predGateWeight M tag p.1 p.2 ω) := by
        rw [hsumExpect]
      _ ≤ 2 * ∑ p : I, HypercubeRamsey.S04.eps4 β γ n := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro p hp
        exact predGateWeight_expect_le_eps M tag q q' hRef hResample p.1 p.2
      _ = 2 * (Fintype.card I : ℝ) * HypercubeRamsey.S04.eps4 β γ n := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hmain :
      P.expect (fun ω =>
        if HypercubeRamsey.S04.SPre M tag ω then (J ω).pr (bad ω) else 0) ≤
          1 / 10 := by
    calc
      P.expect (fun ω =>
          if HypercubeRamsey.S04.SPre M tag ω then (J ω).pr (bad ω) else 0) ≤
          P.expect (fun ω => 2 * ∑ p : I, predGateWeight M tag p.1 p.2 ω) :=
        HypercubeRamsey.FinProb.expect_mono P hpoint
      _ ≤ 2 * (Fintype.card I : ℝ) * HypercubeRamsey.S04.eps4 β γ n := hbound
      _ ≤ 1 / 10 := by simpa [I] using hTail n hn
  change P.expect (fun ω =>
    if HypercubeRamsey.S04.SPre M tag ω then (J ω).pr
      (fun f => ∃ a, HypercubeRamsey.S04.PredFail M tag ω a
        (HypercubeRamsey.S04.nbrLabels f a)) else 0) ≤ 1 / 10
  exact hmain

end HypercubeRamsey.Lane_q_s04_load
