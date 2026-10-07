import HypercubeRamsey.S04.CoreLemmas
import HypercubeRamsey.S03.NearProductInjection
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
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
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
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnn
    have hbound : (2 * HypercubeRamsey.S04.locR β γ n : ℝ) ≤ (n : ℝ) ^ (1 - δ) := by
      simpa [δ] using hn
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
    simpa only [average, mul_one] using hscatRaw
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
    fun ω => ∃ y, 4 * (4 * K + 1) < average y ω
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
      P.pr event := HypercubeRamsey.S04.pr_mono P (fun ω hbad => hbadTo ω hbad)
  have hprob := hmono.trans htailP
  change P.pr (fun ω => ∃ y, 1 / 10 < HypercubeRamsey.S04.oddCol M tag ω y) ≤ 1 / 10
  exact hprob.trans (hTail n hnTail)

end HypercubeRamsey.Lane_q_s04_load
