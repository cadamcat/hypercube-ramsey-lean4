import HypercubeRamsey.S08.L81.AnchorNodes

/-!
# Lane q-s08-odd helpers for the odd hidden-moment node

These helpers are kept in a lane namespace so the other Section 8 lanes can
continue editing their exported nodes independently.
-/

noncomputable section

namespace HypercubeRamsey.Lane_q_s08_odd

open Classical
open scoped BigOperators

private theorem finProb_ext
    {α : Type*} [Fintype α] {P Q : FinProb α}
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P with
  | mk pw hp hs =>
    cases Q with
    | mk qw hq hqs =>
      have hw : pw = qw := funext h
      subst qw
      rfl

private theorem keyDist_symm {η₀ : ℝ} {n : ℕ}
    (g u : _root_.HypercubeRamsey.S08.Key η₀ n) :
    _root_.HypercubeRamsey.S08.keyDist g u = _root_.HypercubeRamsey.S08.keyDist u g := by
  unfold _root_.HypercubeRamsey.S08.keyDist
  apply Finset.sum_congr rfl
  intro r hr
  exact Nat.dist_comm _ _

private theorem keyDist_triangle {η₀ : ℝ} {n : ℕ}
    (g u v : _root_.HypercubeRamsey.S08.Key η₀ n) :
    _root_.HypercubeRamsey.S08.keyDist g v ≤
      _root_.HypercubeRamsey.S08.keyDist g u + _root_.HypercubeRamsey.S08.keyDist u v := by
  unfold _root_.HypercubeRamsey.S08.keyDist
  calc
    (∑ r, Nat.dist (g r).val (v r).val) ≤
        ∑ r, (Nat.dist (g r).val (u r).val + Nat.dist (u r).val (v r).val) := by
      apply Finset.sum_le_sum
      intro r hr
      exact Nat.dist.triangle_inequality _ _ _
    _ = _ := by rw [Finset.sum_add_distrib]

private theorem keyDist_le_of_mem_keyBall {η₀ : ℝ} {n : ℕ}
    (g u : _root_.HypercubeRamsey.S08.Key η₀ n) (R : ℕ)
    (hu : u ∈ _root_.HypercubeRamsey.S08.keyBall g R) :
    _root_.HypercubeRamsey.S08.keyDist g u ≤ R := (Finset.mem_filter.mp hu).2

theorem pi_expect_finprod_of_disjoint
    {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (f : J → (∀ i, Ω i) → ℝ) (S : J → Finset ι)
    (hdep : ∀ j, FinProb.DependsOn (f j) (S j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (T : Finset J) :
    (FinProb.pi P).expect (fun ω => ∏ j ∈ T, f j ω) =
      ∏ j ∈ T, (FinProb.pi P).expect (f j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [FinProb.expect_const]
  | @insert j T hj ih =>
      have hprodDep : FinProb.DependsOn (fun ω => ∏ i ∈ T, f i ω) (T.biUnion S) := by
        intro ω ω' hω
        apply Finset.prod_congr rfl
        intro i hi
        exact hdep i ω ω' (by
          intro k hk
          exact hω k (Finset.mem_biUnion.mpr ⟨i, hi, hk⟩))
      have hscope : Disjoint (T.biUnion S) (S j) := by
        apply Finset.disjoint_left.mpr
        intro k hkT hkj
        obtain ⟨i, hiT, hki⟩ := Finset.mem_biUnion.mp hkT
        have hij : i ≠ j := by
          intro heq
          subst i
          exact hj hiT
        exact (Finset.disjoint_left.mp (hdisj i j hij)) hki hkj
      have hm := FinProb.pi_expect_mul_of_disjoint P
        (fun ω => ∏ i ∈ T, f i ω) (f j) (T.biUnion S) (S j) hprodDep (hdep j) hscope
      calc
        (FinProb.pi P).expect (fun ω => ∏ i ∈ insert j T, f i ω) =
            (FinProb.pi P).expect (fun ω => (∏ i ∈ T, f i ω) * f j ω) := by
          congr 1
          funext ω
          rw [Finset.prod_insert hj]
          ring
        _ = (FinProb.pi P).expect (fun ω => ∏ i ∈ T, f i ω) *
              (FinProb.pi P).expect (f j) := hm
        _ = (∏ i ∈ T, (FinProb.pi P).expect (f i)) *
              (FinProb.pi P).expect (f j) := by rw [ih]
        _ = ∏ i ∈ insert j T, (FinProb.pi P).expect (f i) := by
          rw [Finset.prod_insert hj]
          ring

theorem pi_expect_singleton_eq
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → FinProb α) (i : ι) (f : (ι → α) → ℝ) (ω₀ : ι → α)
    (hf : FinProb.DependsOn f {i}) :
    (FinProb.pi P).expect f = (P i).expect (fun a => f (Function.update ω₀ i a)) := by
  classical
  let S : Finset ι := {i}
  let J := {j // j ∈ S}
  letI : Unique J := ⟨⟨i, by simp [S]⟩, fun j => by
    apply Subtype.ext
    exact Finset.mem_singleton.mp j.2⟩
  let j₀ : J := default
  let g : (∀ j : J, α) → ℝ := fun a => f (Function.update ω₀ i (a j₀))
  have hpoint (ω : ι → α) : f ω = g (fun j => ω j.1) := by
    apply hf ω (Function.update ω₀ i (ω i))
    intro k hk
    have hki : k = i := Finset.mem_singleton.mp hk
    subst k
    simp [g, j₀, S, J]
  have hm := FinProb.pi_marginal_expect P S g
  calc
    (FinProb.pi P).expect f = (FinProb.pi P).expect (fun ω => g (fun j => ω j.1)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro ω hω
      rw [hpoint]
    _ = (FinProb.pi (fun j : J => P j.1)).expect g := hm
    _ = (P i).expect (fun a => f (Function.update ω₀ i a)) := by
      let e : (∀ j : J, α) ≃ α := Equiv.piUnique fun j : J => α
      change (∑ x : (∀ j : J, α),
        (∏ j : J, (P j.1).w (x j)) * g x) = _
      rw [← Equiv.sum_comp e.symm]
      simp [e, g, j₀, J, S, FinProb.expect, FinProb.pi]

theorem expect_congr
    {α : Type*} [Fintype α] (P : FinProb α) {f g : α → ℝ}
    (h : ∀ a, f a = g a) : P.expect f = P.expect g := by
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro a ha
  rw [h a]

theorem glue_update
    {V α : Type*} [DecidableEq V] (U : Finset V) (ω : ∀ v, α)
    (a : ∀ v : U, α) (i : V) (hi : i ∈ U) (x : α) :
    _root_.HypercubeRamsey.S08.glue U ω (Function.update a ⟨i, hi⟩ x) =
      Function.update (_root_.HypercubeRamsey.S08.glue U ω a) i x := by
  funext v
  by_cases hvi : v = i
  · subst v
    simp [_root_.HypercubeRamsey.S08.glue, hi]
  · by_cases hv : v ∈ U
    · simp [_root_.HypercubeRamsey.S08.glue, hv, Function.update, hvi]
    · simp [_root_.HypercubeRamsey.S08.glue, hv, Function.update, hvi]

namespace CtxHelpers

open HypercubeRamsey.S08
open OAI.HypercubeRamsey

namespace Ctx

variable {η₀ β p : ℝ} {h : ℕ} (D : HypercubeRamsey.S08.Ctx η₀ β p h)

abbrev TATKey := ((D.Loc → D.M.ι) × (D.Loc → Bool)) × (hdP η₀ D.n).Ties

local instance : Fintype D.KeyT := by infer_instance
local instance : Fintype (TATKey D) := by
  unfold TATKey
  infer_instance

def TATDependsOn (f : D.TAT → ℝ) (s : Finset D.KeyT) : Prop :=
  ∀ z z', (∀ g ∈ s, z.1.1 g = z'.1.1 g) →
    (∀ g ∈ s, z.1.2 g = z'.1.2 g) → (∀ g ∈ s, z.2 g = z'.2 g) → f z = f z'

def oddNormP0 (q : D.Pre) (W : D.Anch) (c : D.CellT) (y : Fin D.N) : ℝ :=
  (D.N : ℝ) * D.p0 q W c y / (98 / 100)

def oddCrossAnchorSet (c : D.CellT) : Finset D.CellT :=
  Finset.univ.image fun u : D.CrossSub c.1 => (u.1, c.2)

theorem oddNormP0_dep_anchors (hLoc : D.P0Local) (q : D.Pre)
    (c : D.CellT) (y : Fin D.N) :
    FinProb.DependsOn (fun W => oddNormP0 D q W c y) (oddCrossAnchorSet D c) := by
  intro W W' hWW
  have hcross : ∀ u ∈ crossKeys c.1, W (u, c.2) = W' (u, c.2) := by
    intro u hu
    apply hWW
    unfold oddCrossAnchorSet
    apply Finset.mem_image.mpr
    exact ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩
  have hp0 := hLoc q q W W' c
    (by intro g hg; rfl)
    (by intro g hg; exact ⟨rfl, rfl⟩)
    (by intro g hg; exact ⟨rfl, rfl⟩)
    hcross
  simp [oddNormP0, hp0]

theorem oddCrossAnchorSet_disjoint {J : Type*} [Fintype J]
    (c : J → D.CellT)
    (hsep : ∀ i j, i ≠ j → 8 < keyDist (c i).1 (c j).1) :
    ∀ i j, i ≠ j → Disjoint (oddCrossAnchorSet D (c i)) (oddCrossAnchorSet D (c j)) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  obtain ⟨ui, hui, heui⟩ := Finset.mem_image.mp hei
  obtain ⟨uj, huj, heuj⟩ := Finset.mem_image.mp hej
  have hkey : ui.1 = uj.1 := congrArg Prod.fst (heui.trans heuj.symm)
  have hdi : keyDist (c i).1 ui.1 = 1 := (Finset.mem_filter.mp ui.2).2
  have hdj : keyDist (c j).1 uj.1 = 1 := (Finset.mem_filter.mp uj.2).2
  have hclose : keyDist (c i).1 (c j).1 ≤ 2 := by
    calc
      keyDist (c i).1 (c j).1 ≤ keyDist (c i).1 ui.1 + keyDist ui.1 (c j).1 :=
        keyDist_triangle _ _ _
      _ = 1 + 1 := by rw [hdi, hkey, keyDist_symm, hdj]
      _ = 2 := by norm_num
  have := hsep i j hij
  omega

theorem oddRawAnchors_expect_finprod_of_separated
    (hLoc : D.P0Local) (q : D.Pre) (y : Fin D.N)
    {J : Type*} [Fintype J] (c : J → D.CellT)
    (hsep : ∀ i j, i ≠ j → 8 < keyDist (c i).1 (c j).1) (T : Finset J) :
    (D.rawAnchors q).expect (fun W => ∏ j ∈ T, oddNormP0 D q W (c j) y) =
      ∏ j ∈ T, (D.rawAnchors q).expect (fun W => oddNormP0 D q W (c j) y) := by
  rw [_root_.HypercubeRamsey.S08.Ctx.rawAnchors]
  exact pi_expect_finprod_of_disjoint
    (fun e => D.Usel q e)
    (fun j W => oddNormP0 D q W (c j) y)
    (fun j => oddCrossAnchorSet D (c j))
    (fun j => oddNormP0_dep_anchors D hLoc q (c j) y)
    (oddCrossAnchorSet_disjoint D c hsep) T

def oddAnchorMean (Θ : D.Hist) (P : D.Pos) (z : D.TAT)
    (c : D.CellT) (y : Fin D.N) : ℝ :=
  (D.rawAnchors ((Θ, P), z)).expect
    (fun W => oddNormP0 D ((Θ, P), z) W c y)

private theorem keyBall_mono {g k : D.KeyT} {r R : ℕ}
    (hr : r ≤ R) (hk : k ∈ keyBall g r) : k ∈ keyBall g R := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, (keyDist_le_of_mem_keyBall g k r hk).trans hr⟩

private theorem keyBall_add_of_dist {g u k : D.KeyT} {r R : ℕ}
    (hgu : keyDist g u ≤ r) (huk : keyDist u k ≤ R) :
    k ∈ keyBall g (r + R) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  calc
    keyDist g k ≤ keyDist g u + keyDist u k := keyDist_triangle _ _ _
    _ ≤ r + R := Nat.add_le_add hgu huk

theorem oddAnchorMean_tat_dep (hLoc : D.P0Local) (hSel : D.SelLocal)
    (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (y : Fin D.N) :
    TATDependsOn D (fun z => oddAnchorMean D Θ P z c y) (keyBall c.1 3) := by
  classical
  intro z z' htag hact htie
  let q : D.Pre := ((Θ, P), z)
  let q' : D.Pre := ((Θ, P), z')
  let A := oddCrossAnchorSet D c
  have hP0row (W : D.Anch) :
      oddNormP0 D q W c y = oddNormP0 D q' W c y := by
    have hp0 := hLoc q q' W W c
      (by intro g hg; rfl)
      (by
        intro g hg
        exact ⟨rfl, htag g hg⟩)
      (by
        intro g hg
        refine ⟨hact g (keyBall_mono D (by omega) hg), htie g (keyBall_mono D (by omega) hg)⟩)
      (by intro u hu; rfl)
    simp [oddNormP0, q, q', hp0]
  have hUsel : ∀ e : D.CellT, e ∈ A → D.Usel q e = D.Usel q' e := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    have hudist : keyDist c.1 u.1 = 1 := (Finset.mem_filter.mp u.2).2
    have huball : u.1 ∈ keyBall c.1 3 := by
      exact keyBall_mono D (by omega) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hudist.le⟩)
    have hsel_eq := hSel q q' (u.1, c.2)
      (by intro g hg; rfl)
      (by
        intro g hg ℓ hℓ
        have hgb : g ∈ keyBall c.1 3 :=
          keyBall_add_of_dist D hudist.le (keyDist_le_of_mem_keyBall u.1 g 2 hg)
        exact ⟨rfl, congrFun (htag g hgb) ℓ⟩)
      (by
        intro ℓ hℓ
        exact ⟨congrFun (hact u.1 huball) ℓ, congrFun (htie u.1 huball) ℓ⟩)
    have htagU : z.1.1 u.1 = z'.1.1 u.1 := htag u.1 huball
    have hselTag : D.selTag q (u.1, c.2) = D.selTag q' (u.1, c.2) := by
      simp [_root_.HypercubeRamsey.S08.Ctx.selTag, q, q', hsel_eq, htagU]
    simp [_root_.HypercubeRamsey.S08.Ctx.Usel, q, q', hselTag]
  have hdepq := oddNormP0_dep_anchors D hLoc q c y
  have hdepq' := oddNormP0_dep_anchors D hLoc q' c y
  have hMargQ := FinProb.pi_expect_depends (fun e : D.CellT => D.Usel q e) A
    (fun W => oddNormP0 D q W c y) (fun _ => y) hdepq
  have hMargQ' := FinProb.pi_expect_depends (fun e : D.CellT => D.Usel q' e) A
    (fun W => oddNormP0 D q' W c y) (fun _ => y) hdepq'
  change (FinProb.pi (fun e : D.CellT => D.Usel q e)).expect
      (fun W => oddNormP0 D q W c y) =
    (FinProb.pi (fun e : D.CellT => D.Usel q' e)).expect
      (fun W => oddNormP0 D q' W c y)
  rw [hMargQ, hMargQ']
  have hLaw : (fun e : {e : D.CellT // e ∈ A} => D.Usel q e.1) =
      (fun e : {e : D.CellT // e ∈ A} => D.Usel q' e.1) := by
    funext e
    exact hUsel e.1 e.2
  rw [hLaw]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply hP0row

private theorem anchorU_eq_on_local_history
    (Θ Θ' : D.Hist) (g : D.KeyT) (i : D.M.ι)
    (hΘ : ∀ u ∈ insert g (crossKeys g), Θ u = Θ' u) :
    D.anchorU Θ g i = D.anchorU Θ' g i := by
  have hcross (x : Fin D.N) : D.crossHit Θ g x = D.crossHit Θ' g x := by
    apply propext
    constructor
    · intro hx u hu
      have htu := hΘ u (Finset.mem_insert.mpr (Or.inr hu))
      simpa [htu] using hx u hu
    · intro hx u hu
      have htu := hΘ u (Finset.mem_insert.mpr (Or.inr hu))
      simpa [htu] using hx u hu
  have hown (x : Fin D.N) : D.ownHit Θ g x = D.ownHit Θ' g x := by
    unfold _root_.HypercubeRamsey.S08.Ctx.ownHit
    rw [hcross x]
    congr 1
    exact congrArg (fun θ => D.hitsAll x θ)
      (hΘ g (Finset.mem_insert_self g (crossKeys g)))
  unfold _root_.HypercubeRamsey.S08.Ctx.anchorU _root_.HypercubeRamsey.S08.normOr
  apply finProb_ext
  intro x
  simp_rw [hown]

private theorem tilt_eq_on_local_history
    (Θ Θ' : D.Hist) (g : D.KeyT)
    (hΘ : ∀ u ∈ insert g (crossKeys g), Θ u = Θ' u) :
    D.tilt Θ g = D.tilt Θ' g := by
  have hcross (x : Fin D.N) : D.crossHit Θ g x = D.crossHit Θ' g x := by
    apply propext
    constructor
    · intro hx u hu
      simpa [hΘ u (Finset.mem_insert.mpr (Or.inr hu))] using hx u hu
    · intro hx u hu
      simpa [hΘ u (Finset.mem_insert.mpr (Or.inr hu))] using hx u hu
  have hown (x : Fin D.N) : D.ownHit Θ g x = D.ownHit Θ' g x := by
    unfold _root_.HypercubeRamsey.S08.Ctx.ownHit
    rw [hcross x]
    congr 1
    exact congrArg (fun θ => D.hitsAll x θ)
      (hΘ g (Finset.mem_insert_self g (crossKeys g)))
  have hminus (i : D.M.ι) : D.dMinus Θ g i = D.dMinus Θ' g i := by
    unfold _root_.HypercubeRamsey.S08.Ctx.dMinus
    apply Finset.sum_congr rfl
    intro x hx
    rw [hcross x]
  have hplus (i : D.M.ι) : D.dPlus Θ g i = D.dPlus Θ' g i := by
    unfold _root_.HypercubeRamsey.S08.Ctx.dPlus
    apply Finset.sum_congr rfl
    intro x hx
    rw [hown x]
  have hgate (i : D.M.ι) : D.GateOpen Θ g i = D.GateOpen Θ' g i := by
    unfold _root_.HypercubeRamsey.S08.Ctx.GateOpen
    rw [hminus, hplus]
  have hpost (i : D.M.ι) : D.postW (Θ g) i = D.postW (Θ' g) i := by
    rw [hΘ g (Finset.mem_insert_self g (crossKeys g))]
  have htiltW (i : D.M.ι) : D.tiltW Θ g i = D.tiltW Θ' g i := by
    simp [_root_.HypercubeRamsey.S08.Ctx.tiltW, hpost i, hminus i, hgate i]
  unfold _root_.HypercubeRamsey.S08.Ctx.tilt
  have hfun : (fun i => D.tiltW Θ g i) = (fun i => D.tiltW Θ' g i) :=
    funext htiltW
  apply finProb_ext
  intro i
  simp [hfun]

set_option maxHeartbeats 1000000 in
theorem oddAnchorMean_hidden_dep (hLoc : D.P0Local) (hSel : D.SelLocal)
    (Θ Θ' : D.Hist) (P : D.Pos) (z : D.TAT) (c : D.CellT) (y : Fin D.N)
    (hΘ : ∀ g ∈ keyBall c.1 4, Θ g = Θ' g) :
    oddAnchorMean D Θ P z c y = oddAnchorMean D Θ' P z c y := by
  classical
  let q : D.Pre := ((Θ, P), z)
  let q' : D.Pre := ((Θ', P), z)
  let A := oddCrossAnchorSet D c
  have hrow (W : D.Anch) :
      oddNormP0 D q W c y = oddNormP0 D q' W c y := by
    have hp0 := hLoc q q' W W c
      (by intro g hg; exact hΘ g hg)
      (by intro g hg; exact ⟨rfl, rfl⟩)
      (by intro g hg; exact ⟨rfl, rfl⟩)
      (by intro u hu; rfl)
    simp [oddNormP0, q, q', hp0]
  have hUsel : ∀ e : D.CellT, e ∈ A → D.Usel q e = D.Usel q' e := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    have hudist : keyDist c.1 u.1 = 1 := (Finset.mem_filter.mp u.2).2
    have huBall3 : ∀ g ∈ keyBall u.1 3, g ∈ keyBall c.1 4 := by
      intro g hg
      exact keyBall_add_of_dist D hudist.le (keyDist_le_of_mem_keyBall u.1 g 3 hg)
    have hsel_eq := hSel q q' (u.1, c.2)
      (by
        intro g hg
        exact hΘ g (huBall3 g hg))
      (by intro g hg ℓ hℓ; exact ⟨rfl, rfl⟩)
      (by intro ℓ hℓ; exact ⟨rfl, rfl⟩)
    have htagU : z.1.1 u.1 = z.1.1 u.1 := rfl
    have hselTag : D.selTag q (u.1, c.2) = D.selTag q' (u.1, c.2) := by
      simp [_root_.HypercubeRamsey.S08.Ctx.selTag, q, q', hsel_eq, htagU]
    have hAnchorU : ∀ i, D.anchorU Θ u.1 i = D.anchorU Θ' u.1 i := by
      intro i
      apply anchorU_eq_on_local_history
      intro v hv
      have hvBall : v ∈ keyBall c.1 4 := by
        rcases Finset.mem_insert.mp hv with hEq | hvCross
        · subst v
          exact keyBall_mono D (by omega) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hudist.le⟩)
        · have hvDist : keyDist u.1 v ≤ 1 := le_of_eq (Finset.mem_filter.mp hvCross).2
          exact keyBall_mono D (by omega) (keyBall_add_of_dist D hudist.le hvDist)
      exact hΘ v hvBall
    simp [_root_.HypercubeRamsey.S08.Ctx.Usel, q, q', hselTag, hAnchorU]
  have hdepq := oddNormP0_dep_anchors D hLoc q c y
  have hdepq' := oddNormP0_dep_anchors D hLoc q' c y
  have hMargQ := FinProb.pi_expect_depends (fun e : D.CellT => D.Usel q e) A
    (fun W => oddNormP0 D q W c y) (fun _ => y) hdepq
  have hMargQ' := FinProb.pi_expect_depends (fun e : D.CellT => D.Usel q' e) A
    (fun W => oddNormP0 D q' W c y) (fun _ => y) hdepq'
  change (FinProb.pi (fun e : D.CellT => D.Usel q e)).expect
      (fun W => oddNormP0 D q W c y) =
    (FinProb.pi (fun e : D.CellT => D.Usel q' e)).expect
      (fun W => oddNormP0 D q' W c y)
  rw [hMargQ, hMargQ']
  have hLaw : (fun e : {e : D.CellT // e ∈ A} => D.Usel q e.1) =
      (fun e : {e : D.CellT // e ∈ A} => D.Usel q' e.1) := by
    funext e
    exact hUsel e.1 e.2
  rw [hLaw]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply hrow

private theorem oddKeyBall3_disjoint {J : Type*} [Fintype J]
    (g : J → D.KeyT)
    (hsep : ∀ i j, i ≠ j → 8 < keyDist (g i) (g j)) :
    ∀ i j, i ≠ j → Disjoint (keyBall (g i) 3) (keyBall (g j) 3) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro k hik hjk
  have hik' := keyDist_le_of_mem_keyBall (g i) k 3 hik
  have hjk' := keyDist_le_of_mem_keyBall (g j) k 3 hjk
  have hclose : keyDist (g i) (g j) ≤ 6 := by
    calc
      keyDist (g i) (g j) ≤ keyDist (g i) k + keyDist k (g j) :=
        keyDist_triangle _ _ _
      _ = keyDist (g i) k + keyDist (g j) k := by rw [keyDist_symm k (g j)]
      _ ≤ 3 + 3 := Nat.add_le_add hik' hjk'
      _ = 6 := by norm_num
  have hfar := hsep i j hij
  omega

theorem oddKeyBall4_disjoint {J : Type*} [Fintype J]
    (g : J → D.KeyT)
    (hsep : ∀ i j, i ≠ j → 8 < keyDist (g i) (g j)) :
    ∀ i j, i ≠ j → Disjoint (keyBall (g i) 4) (keyBall (g j) 4) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro k hik hjk
  have hik' := keyDist_le_of_mem_keyBall (g i) k 4 hik
  have hjk' := keyDist_le_of_mem_keyBall (g j) k 4 hjk
  have hclose : keyDist (g i) (g j) ≤ 8 := by
    calc
      keyDist (g i) (g j) ≤ keyDist (g i) k + keyDist k (g j) :=
        keyDist_triangle _ _ _
      _ = keyDist (g i) k + keyDist (g j) k := by rw [keyDist_symm k (g j)]
      _ ≤ 4 + 4 := Nat.add_le_add hik' hjk'
      _ = 8 := by norm_num
  have hfar := hsep i j hij
  omega

def oddRawMean (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (y : Fin D.N) : ℝ :=
  (D.rawLaw Θ P).expect (fun z => oddNormP0 D ((Θ, P), z.1) z.2 c y)

theorem oddRawMean_scale (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (y : Fin D.N) :
    oddRawMean D Θ P c y = ((D.N : ℝ) / (98 / 100)) *
      (D.rawLaw Θ P).expect (fun z => D.p0 ((Θ, P), z.1) z.2 c y) := by
  unfold oddRawMean
  have hfun : (fun z : D.TAT × D.Anch => oddNormP0 D ((Θ, P), z.1) z.2 c y) =
      fun z : D.TAT × D.Anch =>
        ((D.N : ℝ) / (98 / 100)) * D.p0 ((Θ, P), z.1) z.2 c y := by
    funext z
    unfold oddNormP0
    ring
  rw [hfun, FinProb.expect_smul]

theorem oddRawMean_nonneg (hP0 : D.P0Law) (Θ : D.Hist) (P : D.Pos)
    (c : D.CellT) (y : Fin D.N) : 0 ≤ oddRawMean D Θ P c y := by
  unfold oddRawMean FinProb.expect
  apply Finset.sum_nonneg
  intro z hz
  apply mul_nonneg ((D.rawLaw Θ P).nonneg z)
  unfold oddNormP0
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
    ((hP0 ((Θ, P), z.1) z.2 c).1 y)) (by norm_num)


def packTAT (z : D.TAT) : D.KeyT → TATKey D :=
  fun g => ((z.1.1 g, z.1.2 g), z.2 g)

def unpackTAT (z : D.KeyT → TATKey D) : D.TAT :=
  ((fun g => (z g).1.1, fun g => (z g).1.2), fun g => (z g).2)

def tatEquiv : D.TAT ≃ (D.KeyT → TATKey D) where
  toFun := packTAT D
  invFun := unpackTAT D
  left_inv := by
    intro z
    rcases z with ⟨⟨t, a⟩, r⟩
    rfl
  right_inv := by
    intro z
    funext g
    simp [packTAT, unpackTAT]

def tatKeyLaw (Θ : D.Hist) (g : D.KeyT) : FinProb (TATKey D) :=
  ((FinProb.pi fun _ : D.Loc => D.tilt Θ g).prod (hdP η₀ D.n).actLaw).prod
    (hdP η₀ D.n).tieLaw

noncomputable def tatKeyPi (Θ : D.Hist) : FinProb (D.KeyT → TATKey D) where
  w z := ∏ k, (tatKeyLaw D Θ k).w (z k)
  nonneg z := Finset.prod_nonneg fun k _ => (tatKeyLaw D Θ k).nonneg (z k)
  sum_eq_one := by
    classical
    letI : ∀ k : D.KeyT, Fintype (TATKey D) := fun _ => instFintypeTATKey D
    rw [← Fintype.prod_sum]
    have hsum : ∀ k : D.KeyT, ∑ a, (tatKeyLaw D Θ k).w a = 1 :=
      fun k => (tatKeyLaw D Θ k).sum_eq_one
    simp_rw [hsum]
    simp

theorem tatKeyPi_eq_pi (Θ : D.Hist) :
    tatKeyPi D Θ =
      @FinProb.pi D.KeyT inferInstance inferInstance (fun _ => TATKey D)
        (fun _ => instFintypeTATKey D) (tatKeyLaw D Θ) := by
  classical
  letI : ∀ k : D.KeyT, Fintype (TATKey D) := fun _ => instFintypeTATKey D
  apply finProb_ext
  intro z
  rfl

theorem rawTAT_weight (Θ : D.Hist) (z : D.TAT) :
    (D.rawTAT Θ).w z =
      (tatKeyPi D Θ).w (packTAT D z) := by
  letI : Fintype D.KeyT := inferInstance
  letI : Fintype D.Loc := inferInstance
  letI : Fintype D.M.ι := inferInstance
  letI : Fintype (hdP η₀ D.n).Ties := inferInstance
  letI : Fintype (TATKey D) := by unfold TATKey; infer_instance
  letI : ∀ k : D.KeyT, Fintype (TATKey D) := fun _ => inferInstance
  simp [_root_.HypercubeRamsey.S08.Ctx.rawTAT,
    _root_.HypercubeRamsey.S08.Ctx.tagLawAll,
    _root_.HypercubeRamsey.S08.Ctx.actLaw,
    _root_.HypercubeRamsey.S08.Ctx.tieLaw, tatKeyLaw, packTAT, tatKeyPi,
    FinProb.pi, FinProb.prod, Finset.prod_mul_distrib, mul_assoc]

theorem rawTAT_expect_pack (Θ : D.Hist) (f : D.TAT → ℝ) :
    (D.rawTAT Θ).expect f =
      (tatKeyPi D Θ).expect (fun z => f (unpackTAT D z)) := by
  classical
  letI : Fintype D.KeyT := inferInstance
  letI : Fintype D.Loc := inferInstance
  letI : Fintype D.M.ι := inferInstance
  letI : Fintype (hdP η₀ D.n).Ties := inferInstance
  letI : Fintype (TATKey D) := by unfold TATKey; infer_instance
  letI : ∀ k : D.KeyT, Fintype (TATKey D) := fun _ => inferInstance
  let e := tatEquiv D
  rw [FinProb.expect]
  rw [← Equiv.sum_comp e.symm
    (fun z => (D.rawTAT Θ).w z * f z)]
  apply Finset.sum_congr rfl
  intro z hz
  rw [rawTAT_weight D Θ (e.symm z)]
  have hpack : packTAT D (e.symm z) = z := e.right_inv z
  rw [hpack]
  simp [e, tatEquiv, packTAT, unpackTAT, tatKeyPi]

theorem rawTAT_expect_finprod_of_disjoint
    (Θ : D.Hist) {J : Type*} [Fintype J]
    (f : J → D.TAT → ℝ) (S : J → Finset D.KeyT)
    (hdep : ∀ j, TATDependsOn D (f j) (S j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (T : Finset J) :
    (D.rawTAT Θ).expect (fun z => ∏ j ∈ T, f j z) =
      ∏ j ∈ T, (D.rawTAT Θ).expect (f j) := by
  letI : Fintype D.KeyT := inferInstance
  letI : Fintype D.Loc := inferInstance
  letI : Fintype D.M.ι := inferInstance
  letI : Fintype (hdP η₀ D.n).Ties := inferInstance
  letI : Fintype (TATKey D) := by unfold TATKey; infer_instance
  letI : ∀ k : D.KeyT, Fintype (TATKey D) := fun _ => inferInstance
  letI : Fintype (D.KeyT → TATKey D) := Pi.instFintype
  rw [rawTAT_expect_pack D Θ]
  let f' : J → (D.KeyT → TATKey D) → ℝ := fun j z => f j (unpackTAT D z)
  rw [tatKeyPi_eq_pi D Θ]
  have hdep' : ∀ j, FinProb.DependsOn (f' j) (S j) := by
    intro j z z' hzz
    apply hdep j
    · intro g hg
      exact congrArg (fun a : TATKey D => a.1.1) (hzz g hg)
    · intro g hg
      exact congrArg (fun a : TATKey D => a.1.2) (hzz g hg)
    · intro g hg
      exact congrArg (fun a : TATKey D => a.2) (hzz g hg)
  have hm := pi_expect_finprod_of_disjoint (tatKeyLaw D Θ) f' S hdep' hdisj T
  rw [hm]
  apply Finset.prod_congr rfl
  intro j hj
  rw [rawTAT_expect_pack D Θ (f j)]
  rw [tatKeyPi_eq_pi D Θ]

theorem oddRawLaw_expect_finprod_of_separated
    (hLoc : D.P0Local) (hSel : D.SelLocal)
    (Θ : D.Hist) (P : D.Pos) (y : Fin D.N)
    {J : Type*} [Fintype J] (c : J → D.CellT)
    (hsep : ∀ i j, i ≠ j → 8 < keyDist (c i).1 (c j).1) (T : Finset J) :
    (D.rawLaw Θ P).expect (fun z => ∏ j ∈ T, oddNormP0 D ((Θ, P), z.1) z.2 (c j) y) =
      ∏ j ∈ T, oddRawMean D Θ P (c j) y := by
  classical
  have hAnchor (z : D.TAT) :
      (D.rawAnchors ((Θ, P), z)).expect
        (fun W => ∏ j ∈ T, oddNormP0 D ((Θ, P), z) W (c j) y) =
      ∏ j ∈ T, oddAnchorMean D Θ P z (c j) y := by
    simpa [oddAnchorMean] using
      oddRawAnchors_expect_finprod_of_separated D hLoc ((Θ, P), z) y c hsep T
  have hExpand :
      (D.rawLaw Θ P).expect
          (fun z => ∏ j ∈ T, oddNormP0 D ((Θ, P), z.1) z.2 (c j) y) =
        (D.rawTAT Θ).expect (fun z => ∏ j ∈ T, oddAnchorMean D Θ P z (c j) y) := by
    change (FinProb.bind (D.rawTAT Θ) (fun z => D.rawAnchors ((Θ, P), z))).expect
      (fun z => ∏ j ∈ T, oddNormP0 D ((Θ, P), z.1) z.2 (c j) y) = _
    calc
      _ = ∑ z, (D.rawTAT Θ).w z *
            (D.rawAnchors ((Θ, P), z)).expect
              (fun W => ∏ j ∈ T, oddNormP0 D ((Θ, P), z) W (c j) y) :=
        FinProb.bind_expect (D.rawTAT Θ) (fun z => D.rawAnchors ((Θ, P), z))
          (fun z W => ∏ j ∈ T, oddNormP0 D ((Θ, P), z) W (c j) y)
      _ = _ := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro z hz
        simpa [FinProb.expect, oddAnchorMean] using
          congrArg (fun a => (D.rawTAT Θ).w z * a) (hAnchor z)
  rw [hExpand]
  rw [rawTAT_expect_finprod_of_disjoint D Θ
    (fun j z => oddAnchorMean D Θ P z (c j) y)
    (fun j => keyBall (c j).1 3)
    (fun j => oddAnchorMean_tat_dep D hLoc hSel Θ P (c j) y)
    (oddKeyBall3_disjoint D (fun j => (c j).1) hsep) T]
  apply Finset.prod_congr rfl
  intro j hj
  have hB := FinProb.bind_expect (D.rawTAT Θ)
    (fun z => D.rawAnchors ((Θ, P), z))
    (fun z W => oddNormP0 D ((Θ, P), z) W (c j) y)
  calc
    (D.rawTAT Θ).expect
        (fun z => oddAnchorMean D Θ P z (c j) y) =
      ∑ z, (D.rawTAT Θ).w z *
        (D.rawAnchors ((Θ, P), z)).expect
          (fun W => oddNormP0 D ((Θ, P), z) W (c j) y) := by
        unfold FinProb.expect oddAnchorMean
        rfl
    _ = (D.rawLaw Θ P).expect
        (fun z => oddNormP0 D ((Θ, P), z.1) z.2 (c j) y) := by
        simpa [_root_.HypercubeRamsey.S08.Ctx.rawLaw] using hB.symm

private theorem nonempty_of_law {α : Type*} [Fintype α] (P : FinProb α) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := ⟨fun a => h ⟨a⟩⟩
  have hsum : (∑ a, P.w a) = 0 := by simp
  rw [P.sum_eq_one] at hsum
  norm_num at hsum

theorem rawTAT_expect_local_eq
    (Θ Θ' : D.Hist) (S : Finset D.KeyT)
    (f g : D.TAT → ℝ)
    (hdepF : TATDependsOn D f S) (hdepG : TATDependsOn D g S)
    (hlaw : ∀ k ∈ S, tatKeyLaw D Θ k = tatKeyLaw D Θ' k)
    (hpoint : ∀ z, f z = g z) :
    (D.rawTAT Θ).expect f = (D.rawTAT Θ').expect g := by
  classical
  let f' : (D.KeyT → TATKey D) → ℝ := fun z => f (unpackTAT D z)
  let g' : (D.KeyT → TATKey D) → ℝ := fun z => g (unpackTAT D z)
  have hdepF' : FinProb.DependsOn f' S := by
    intro z z' hzz
    apply hdepF
    · intro k hk
      exact congrArg (fun a : TATKey D => a.1.1) (hzz k hk)
    · intro k hk
      exact congrArg (fun a : TATKey D => a.1.2) (hzz k hk)
    · intro k hk
      exact congrArg (fun a : TATKey D => a.2) (hzz k hk)
  have hdepG' : FinProb.DependsOn g' S := by
    intro z z' hzz
    exact hdepG (unpackTAT D z) (unpackTAT D z')
      (by intro k hk; exact congrArg (fun a : TATKey D => a.1.1) (hzz k hk))
      (by intro k hk; exact congrArg (fun a : TATKey D => a.1.2) (hzz k hk))
      (by intro k hk; exact congrArg (fun a : TATKey D => a.2) (hzz k hk))
  letI : Fintype D.KeyT := inferInstance
  letI : Fintype (TATKey D) := by
    unfold TATKey
    infer_instance
  letI : ∀ k : D.KeyT, Fintype (TATKey D) := fun _ => inferInstance
  letI : Fintype (D.KeyT → TATKey D) := Pi.instFintype
  let ω₀ : D.KeyT → TATKey D := fun k => Classical.choice (nonempty_of_law (tatKeyLaw D Θ k))
  have hmF := FinProb.pi_expect_depends (tatKeyLaw D Θ) S f' ω₀ hdepF'
  have hmG := FinProb.pi_expect_depends (tatKeyLaw D Θ') S g' ω₀ hdepG'
  rw [rawTAT_expect_pack D Θ, rawTAT_expect_pack D Θ']
  rw [tatKeyPi_eq_pi D Θ, tatKeyPi_eq_pi D Θ']
  rw [hmF, hmG]
  have hLaw : (fun k : {k : D.KeyT // k ∈ S} => tatKeyLaw D Θ k.1) =
      (fun k : {k : D.KeyT // k ∈ S} => tatKeyLaw D Θ' k.1) := by
    funext k
    exact hlaw k.1 k.2
  rw [hLaw]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  exact hpoint (unpackTAT D
    ((Equiv.piEquivPiSubtypeProd (fun k : D.KeyT => k ∈ S) (fun _ => TATKey D)).symm
      (a, fun k : {k : D.KeyT // k ∉ S} => ω₀ k.1)))

set_option maxHeartbeats 1000000 in
theorem oddRawMean_hidden_dep (hLoc : D.P0Local) (hSel : D.SelLocal)
    (Θ Θ' : D.Hist) (P : D.Pos) (c : D.CellT) (y : Fin D.N)
    (hΘ : ∀ g ∈ keyBall c.1 4, Θ g = Θ' g) :
    oddRawMean D Θ P c y = oddRawMean D Θ' P c y := by
  classical
  let S := keyBall c.1 3
  have hdepF : TATDependsOn D (fun z => oddAnchorMean D Θ P z c y) S :=
    oddAnchorMean_tat_dep D hLoc hSel Θ P c y
  have hdepG : TATDependsOn D (fun z => oddAnchorMean D Θ' P z c y) S :=
    oddAnchorMean_tat_dep D hLoc hSel Θ' P c y
  have hlaw : ∀ k ∈ S, tatKeyLaw D Θ k = tatKeyLaw D Θ' k := by
    intro k hk
    have hnear : ∀ v ∈ insert k (crossKeys k), Θ v = Θ' v := by
      intro v hv
      rcases Finset.mem_insert.mp hv with hEq | hvCross
      · subst v
        change k ∈ keyBall c.1 3 at hk
        exact hΘ k (keyBall_mono D (by omega) hk)
      · have hkv : keyDist k v ≤ 1 := (Finset.mem_filter.mp hvCross).2.le
        have hkvBall := keyBall_add_of_dist D (keyDist_le_of_mem_keyBall c.1 k 3 hk) hkv
        exact hΘ v hkvBall
    have htilt := tilt_eq_on_local_history D Θ Θ' k hnear
    simp [tatKeyLaw, htilt]
  have hpoint : ∀ z, oddAnchorMean D Θ P z c y = oddAnchorMean D Θ' P z c y := by
    intro z
    apply oddAnchorMean_hidden_dep D hLoc hSel Θ Θ' P z c y hΘ
  have hraw := rawTAT_expect_local_eq D Θ Θ' S
    (fun z => oddAnchorMean D Θ P z c y)
    (fun z => oddAnchorMean D Θ' P z c y) hdepF hdepG hlaw hpoint
  have hExpandOne (H : D.Hist) :
      (D.rawLaw H P).expect
        (fun z => oddNormP0 D ((H, P), z.1) z.2 c y) =
      (D.rawTAT H).expect (fun z => oddAnchorMean D H P z c y) := by
    change (FinProb.bind (D.rawTAT H) (fun z => D.rawAnchors ((H, P), z))).expect
      (fun z => oddNormP0 D ((H, P), z.1) z.2 c y) = _
    calc
      _ = ∑ z, (D.rawTAT H).w z *
            (D.rawAnchors ((H, P), z)).expect
              (fun W => oddNormP0 D ((H, P), z) W c y) :=
        FinProb.bind_expect (D.rawTAT H) (fun z => D.rawAnchors ((H, P), z))
          (fun z W => oddNormP0 D ((H, P), z) W c y)
      _ = _ := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro z hz
        rfl
  calc
    oddRawMean D Θ P c y = (D.rawTAT Θ).expect (fun z => oddAnchorMean D Θ P z c y) := by
      simpa [oddRawMean] using hExpandOne Θ
    _ = (D.rawTAT Θ').expect (fun z => oddAnchorMean D Θ' P z c y) := hraw
    _ = oddRawMean D Θ' P c y := by
      simpa [oddRawMean] using (hExpandOne Θ').symm

end Ctx

end CtxHelpers
end HypercubeRamsey.Lane_q_s08_odd

end
