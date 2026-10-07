import HypercubeRamsey.S08.L81.SelectionNodes
import HypercubeRamsey.S03.Clock.Leaves_p_clock_r2

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

namespace Lane_q_s08_post

theorem pi_pr_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (S : Finset ι)
    (a : ∀ i : {i // i ∈ S}, Ω i.1) :
    (FinProb.pi P).pr (fun ω => ∀ i : {i // i ∈ S}, ω i.1 = a i) =
      ∏ i : {i // i ∈ S}, (P i.1).w (a i) := by
  classical
  let proj : (∀ i, Ω i) → (∀ i : {i // i ∈ S}, Ω i.1) := fun ω i => ω i.1
  have hpr :
      (FinProb.pi P).pr (fun ω => ∀ i : {i // i ∈ S}, ω i.1 = a i) =
        (FinProb.map (FinProb.pi P) proj).w a := by
    unfold FinProb.pr FinProb.map
    apply Finset.sum_congr rfl
    intro ω hω
    have hiff : (∀ i : {i // i ∈ S}, ω i.1 = a i) ↔ proj ω = a := by
      constructor
      · intro h
        funext i
        exact h i
      · intro h i
        exact congrFun h i
    by_cases hfix : ∀ i : {i // i ∈ S}, ω i.1 = a i
    · have heq : proj ω = a := by
        exact hiff.mp hfix
      simp only [if_pos hfix, if_pos heq]
    · have hneq : proj ω ≠ a := by
        intro heq
        exact hfix (hiff.mpr heq)
      simp only [if_neg hfix, if_neg hneq]
  rw [hpr, FinProb.pi_marginal]
  simp [FinProb.pi]

theorem pi_pr_le_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (S : Finset ι)
    (a : ∀ i : {i // i ∈ S}, Ω i.1) (A : (∀ i, Ω i) → Prop)
    (hA : ∀ ω, A ω → ∀ i : {i // i ∈ S}, ω i.1 = a i) :
    (FinProb.pi P).pr A ≤ ∏ i : {i // i ∈ S}, (P i.1).w (a i) := by
  classical
  calc
    (FinProb.pi P).pr A ≤
        (FinProb.pi P).pr (fun ω => ∀ i : {i // i ∈ S}, ω i.1 = a i) := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro ω hω
      by_cases h : A ω
      · have hc : ∀ i : {i // i ∈ S}, ω i.1 = a i := hA ω h
        simp [h, hc]
      · simp only [if_neg h]
        by_cases hc : ∀ i : {i // i ∈ S}, ω i.1 = a i
        · simp only [if_pos hc]
          exact (FinProb.pi P).nonneg ω
        · simp only [if_neg hc]
          norm_num
    _ = ∏ i : {i // i ∈ S}, (P i.1).w (a i) :=
      pi_pr_cylinder P S a

private theorem pr_mono_early {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A B : Ω → Prop)
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω
    · simp [hA, hB, P.nonneg ω]
    · simp [hA, hB]

theorem pi_pi_pr_le_fixed {G L I : Type*} [Fintype G] [DecidableEq G]
    [Fintype L] [DecidableEq L] [Fintype I]
    (P : G → L → FinProb I) (S : Finset (G × L)) (v : G × L → I)
    (A : (G → L → I) → Prop)
    (hA : ∀ t, A t → ∀ s ∈ S, t s.1 s.2 = v s) :
    (FinProb.pi (fun g => FinProb.pi (P g))).pr A ≤
      ∏ s ∈ S, (P s.1 s.2).w (v s) := by
  classical
  let fiber (g : G) : Finset L := (S.filter fun x => x.1 = g).image Prod.snd
  let Row (g : G) (t : L → I) : Prop := ∀ l : fiber g, t l.1 = v (g, l.1)
  let Rows (t : G → L → I) : Prop := ∀ g, Row g (t g)
  let Prow : G → FinProb (L → I) := fun g => FinProb.pi (P g)
  have mem_fiber (g : G) (l : L) (hl : l ∈ fiber g) : (g, l) ∈ S := by
    rcases Finset.mem_image.mp hl with ⟨x, hx, hxl⟩
    have hx' := Finset.mem_filter.mp hx
    have hpair : (g, l) = x := by
      apply Prod.ext
      · exact hx'.2.symm
      · exact hxl.symm
    simpa [hpair] using hx'.1
  have hsub : ∀ t, A t → Rows t := by
    intro t ht g l
    rcases Finset.mem_image.mp l.2 with ⟨x, hx, hxl⟩
    have hx' := Finset.mem_filter.mp hx
    have hpair : (g, l.1) = x := by
      apply Prod.ext
      · exact hx'.2.symm
      · exact hxl.symm
    have hv := hA t ht (g, l.1) (by simpa [hpair] using hx'.1)
    simpa [hpair] using hv
  have hOuter :
      (FinProb.pi Prow).pr A ≤ (FinProb.pi Prow).pr (fun t => Rows t) := by
    exact pr_mono_early (FinProb.pi Prow) A Rows hsub
  have hfactor :
      (FinProb.pi Prow).pr (fun t => Rows t) = ∏ g, (Prow g).pr (Row g) :=
    FinProb.pi_pr_forall Prow Row
  let Fiber := Σ g : G, fiber g
  let toS : Fiber → {x : G × L // x ∈ S} := fun z =>
    ⟨(z.1, z.2.1), mem_fiber z.1 z.2.1 z.2.2⟩
  have hinj : Function.Injective toS := by
    intro z z' hzz
    have hval : (z.1, z.2.1) = (z'.1, z'.2.1) := by
      have hv := congrArg Subtype.val hzz
      change (z.1, z.2.1) = (z'.1, z'.2.1) at hv
      exact hv
    have hg : z.1 = z'.1 := congrArg Prod.fst hval
    have hl : z.2.1 = z'.2.1 := congrArg Prod.snd hval
    cases z with
    | mk g l =>
      cases z' with
      | mk g' l' =>
        dsimp at hg hl
        subst g'
        have heq : l = l' := by
          apply Subtype.ext
          exact hl
        subst l'
        rfl
  have hsurj : Function.Surjective toS := by
    intro x
    let g := x.1.1
    let l := x.1.2
    have hl : l ∈ fiber g := by
      apply Finset.mem_image.mpr
      refine ⟨x.1, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨x.2, rfl⟩
    refine ⟨⟨g, ⟨l, hl⟩⟩, ?_⟩
    apply Subtype.ext
    simp [toS, g, l]
  let e : Fiber ≃ {x : G × L // x ∈ S} := Equiv.ofBijective toS ⟨hinj, hsurj⟩
  have hprod :
      (∏ g, ∏ l : fiber g, (P g l.1).w (v (g, l.1))) =
        ∏ s ∈ S, (P s.1 s.2).w (v s) := by
    rw [← Fintype.prod_sigma']
    calc
      (∏ z : Fiber, (P z.1 z.2.1).w (v (z.1, z.2.1))) =
          ∏ s : {x : G × L // x ∈ S}, (P s.1.1 s.1.2).w (v s.1) := by
            exact Fintype.prod_equiv e
              (fun z => (P z.1 z.2.1).w (v (z.1, z.2.1)))
              (fun s => (P s.1.1 s.1.2).w (v s.1))
              (fun z => by simp [e, Equiv.ofBijective, toS])
      _ = ∏ s ∈ S, (P s.1 s.2).w (v s) := by
            change (∏ s : S, (P s.1.1 s.1.2).w (v s.1)) = _
            exact Finset.prod_coe_sort S
              (fun x : G × L => (P x.1 x.2).w (v x))
  have hrows : ∀ g, (Prow g).pr (Row g) ≤
      ∏ l : fiber g, (P g l.1).w (v (g, l.1)) := by
    intro g
    exact Lane_q_s08_post.pi_pr_le_fixed (P g) (fiber g)
      (fun l => v (g, l.1)) (Row g) (fun t ht l => ht l)
  calc
    _ ≤ (FinProb.pi Prow).pr (fun t => Rows t) := hOuter
    _ = ∏ g, (Prow g).pr (Row g) := hfactor
    _ ≤ ∏ g, ∏ l : fiber g, (P g l.1).w (v (g, l.1)) := by
          apply Finset.prod_le_prod₀
          · intro g hg
            exact pr_nonneg (Prow g) (Row g)
          · intro g hg
            exact hrows g
    _ = ∏ s ∈ S, (P s.1 s.2).w (v s) := hprod

theorem pi_pr_le_fixed_image {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α]
    (P : ι → FinProb α) (S : Finset κ) (f : κ → ι)
    (hf : Set.InjOn f S) (v : κ → α) (A : (ι → α) → Prop)
    (hA : ∀ x, A x → ∀ k ∈ S, x (f k) = v k) :
    (FinProb.pi P).pr A ≤ ∏ k ∈ S, (P (f k)).w (v k) := by
  classical
  let T : Finset ι := S.image f
  let source (i : T) : κ := Classical.choose (Finset.mem_image.mp i.2)
  have hsource (i : T) : source i ∈ S ∧ f (source i) = i.1 :=
    Classical.choose_spec (Finset.mem_image.mp i.2)
  let val (i : T) : α := v (source i)
  have hfixed : ∀ x, A x → ∀ i : T, x i.1 = val i := by
    intro x hx i
    have h := hA x hx (source i) (hsource i).1
    rw [(hsource i).2] at h
    exact h
  have hprob := pi_pr_le_fixed P T val A hfixed
  let F : ι → ℝ := fun i => if hi : i ∈ T then (P i).w (val ⟨i, hi⟩) else 1
  have hprod :
      (∏ i : T, (P i.1).w (val i)) = ∏ k ∈ S, (P (f k)).w (v k) := by
    calc
      (∏ i : T, (P i.1).w (val i)) = ∏ i : T, F i := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [F]
      _ = ∏ i ∈ T, F i := Finset.prod_coe_sort T F
      _ = ∏ k ∈ S, F (f k) := Finset.prod_image hf
      _ = ∏ k ∈ S, (P (f k)).w (v k) := by
        apply Finset.prod_congr rfl
        intro k hk
        have hmem : f k ∈ T := Finset.mem_image.mpr ⟨k, hk, rfl⟩
        let i : T := ⟨f k, hmem⟩
        have hiSource : source i = k := by
          apply hf (hsource i).1 hk
          exact (hsource i).2
        simp [F, hmem, val, i, hiSource]
  exact hprob.trans_eq hprod

private theorem cross_key_ne {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (g : D.KeyT) (u : D.CrossSub g) : u.1 ≠ g := by
  intro heq
  have hone : keyDist g u.1 = 1 := (Finset.mem_filter.mp u.2).2
  have hself : keyDist g g = 0 := by simp [keyDist]
  rw [heq] at hone
  rw [hself] at hone
  norm_num at hone

private theorem keyDist_triangle_aux {η₀ : ℝ} {n : ℕ}
    (a b c : Key η₀ n) : keyDist a c ≤ keyDist a b + keyDist b c := by
  unfold keyDist
  calc
    (∑ r, Nat.dist (a r).val (c r).val) ≤
        ∑ r, (Nat.dist (a r).val (b r).val + Nat.dist (b r).val (c r).val) := by
          apply Finset.sum_le_sum
          intro r hr
          exact Nat.dist.triangle_inequality _ _ _
    _ = (∑ r, Nat.dist (a r).val (b r).val) +
          ∑ r, Nat.dist (b r).val (c r).val := Finset.sum_add_distrib

theorem baseGates_congr {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT)
    (h0 : Θ g = Θ' g)
    (hcross : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.BaseGates Θ g = D.BaseGates Θ' g := by
  classical
  have hcrossHit (x : Fin D.N) : D.crossHit Θ g x = D.crossHit Θ' g x := by
    apply propext
    constructor
    · intro hx u hu
      rw [← hcross u hu]
      exact hx u hu
    · intro hx u hu
      rw [hcross u hu]
      exact hx u hu
  have hownHit (x : Fin D.N) : D.ownHit Θ g x = D.ownHit Θ' g x := by
    simp [Ctx.ownHit, Ctx.hitsAll, hcrossHit, h0]
  have hdMinus (i : D.M.ι) : D.dMinus Θ g i = D.dMinus Θ' g i := by
    unfold Ctx.dMinus
    apply Finset.sum_congr rfl
    intro x hx
    simp [hcrossHit]
  have hdPlus (i : D.M.ι) : D.dPlus Θ g i = D.dPlus Θ' g i := by
    unfold Ctx.dPlus
    apply Finset.sum_congr rfl
    intro x hx
    simp [hownHit]
  have hdOmit (u₀ : D.KeyT) (i : D.M.ι) :
      D.dOmit Θ g u₀ i = D.dOmit Θ' g u₀ i := by
    unfold Ctx.dOmit
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_erase]
    have hiff :
        (∀ u, (u ≠ u₀ ∧ u ∈ crossKeys g) → D.hitsAll x (Θ u)) ↔
          ∀ u, (u ≠ u₀ ∧ u ∈ crossKeys g) → D.hitsAll x (Θ' u) := by
      constructor
      · intro hmiss u hu
        have h := hmiss u hu
        rw [hcross u hu.2] at h
        exact h
      · intro hmiss u hu
        have h := hmiss u hu
        rw [← hcross u hu.2] at h
        exact h
    by_cases hΘ : ∀ u, (u ≠ u₀ ∧ u ∈ crossKeys g) → D.hitsAll x (Θ u)
    · have hΘ' := hiff.mp hΘ
      rw [if_pos hΘ, if_pos hΘ']
    · have hΘ' : ¬ ∀ u, (u ≠ u₀ ∧ u ∈ crossKeys g) → D.hitsAll x (Θ' u) := by
        intro hh
        exact hΘ (hiff.mpr hh)
      rw [if_neg hΘ, if_neg hΘ']
  have hpostW (i : D.M.ι) : D.postW (Θ g) i = D.postW (Θ' g) i := by rw [h0]
  have hgateOpen (i : D.M.ι) : D.GateOpen Θ g i = D.GateOpen Θ' g i := by
    unfold Ctx.GateOpen
    rw [hdMinus, hdPlus]
  have htiltW (i : D.M.ι) : D.tiltW Θ g i = D.tiltW Θ' g i := by
    unfold Ctx.tiltW
    rw [hpostW, hdMinus, hgateOpen]
  have hZG : D.ZG Θ g = D.ZG Θ' g := by
    unfold Ctx.ZG
    apply Finset.sum_congr rfl
    intro i hi
    exact htiltW i
  have hsumPostMinus :
      (∑ i, D.postW (Θ g) i * D.dMinus Θ g i) =
        ∑ i, D.postW (Θ' g) i * D.dMinus Θ' g i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hpostW, hdMinus]
  have hsumLambdaMinus :
      (∑ i, D.M.Λ i * D.dMinus Θ g i) =
        ∑ i, D.M.Λ i * D.dMinus Θ' g i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdMinus]
  have hsumPostOmit : ∀ u₀ ∈ crossKeys g,
      (∑ i, D.postW (Θ g) i * D.dOmit Θ g u₀ i) =
        ∑ i, D.postW (Θ' g) i * D.dOmit Θ' g u₀ i := by
    intro u₀ hu₀
    apply Finset.sum_congr rfl
    intro i hi
    rw [hpostW, hdOmit]
  have hsumLambdaOmit : ∀ u₀ ∈ crossKeys g,
      (∑ i, D.M.Λ i * D.dOmit Θ g u₀ i) =
        ∑ i, D.M.Λ i * D.dOmit Θ' g u₀ i := by
    intro u₀ hu₀
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdOmit]
  have hgate1 : D.Gate1 Θ g = D.Gate1 Θ' g := by
    apply propext
    constructor <;> intro hh i <;> simpa [Ctx.Gate1, hpostW] using hh i
  have hgate2 : D.Gate2 Θ g = D.Gate2 Θ' g := by
    apply propext
    constructor <;> intro hh <;> simpa [Ctx.Gate2, hZG] using hh
  have hgate34 : D.Gate34 Θ g = D.Gate34 Θ' g := by
    apply propext
    unfold Ctx.Gate34
    constructor
    · intro hh
      refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
      · rw [← hsumPostMinus]
        exact hh.1.1
      · rw [← hsumPostMinus]
        exact hh.1.2
      · rw [← hsumLambdaMinus]
        exact hh.2.1.1
      · rw [← hsumLambdaMinus]
        exact hh.2.1.2
      · intro u hu
        have hO := hh.2.2 u hu
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · rw [← hsumPostOmit u hu]
          exact hO.1.1
        · rw [← hsumPostOmit u hu]
          exact hO.1.2
        · rw [← hsumLambdaOmit u hu]
          exact hO.2.1
        · rw [← hsumLambdaOmit u hu]
          exact hO.2.2
    · intro hh
      refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
      · rw [hsumPostMinus]
        exact hh.1.1
      · rw [hsumPostMinus]
        exact hh.1.2
      · rw [hsumLambdaMinus]
        exact hh.2.1.1
      · rw [hsumLambdaMinus]
        exact hh.2.1.2
      · intro u hu
        have hO := hh.2.2 u hu
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · rw [hsumPostOmit u hu]
          exact hO.1.1
        · rw [hsumPostOmit u hu]
          exact hO.1.2
        · rw [hsumLambdaOmit u hu]
          exact hO.2.1
        · rw [hsumLambdaOmit u hu]
          exact hO.2.2
  unfold Ctx.BaseGates
  rw [hgate1, hgate2, hgate34]

theorem candGate_congr_of_radius_two {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT)
    (hΘ : ∀ u ∈ keyBall g 2, Θ u = Θ' u) :
    D.CandGate Θ g = D.CandGate Θ' g := by
  classical
  have hbase (v : D.KeyT) (hv : keyDist g v ≤ 1) :
      D.BaseGates Θ v = D.BaseGates Θ' v := by
    have hv0 : v ∈ keyBall g 2 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hv.trans (by omega)⟩
    have h0 := hΘ v hv0
    have hcross : ∀ w ∈ crossKeys v, Θ w = Θ' w := by
      intro w hw
      have hvw : keyDist v w = 1 := (Finset.mem_filter.mp hw).2
      have hgw : keyDist g w ≤ 2 := by
        have htri := keyDist_triangle_aux g v w
        omega
      exact hΘ w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgw⟩)
    exact baseGates_congr D Θ Θ' v h0 hcross
  have hbaseG : D.BaseGates Θ g = D.BaseGates Θ' g := hbase g (by simp [keyDist])
  have hbaseU (u : D.CrossSub g) : D.BaseGates Θ u.1 = D.BaseGates Θ' u.1 := by
    apply hbase u.1
    exact (Finset.mem_filter.mp u.2).2.le
  apply propext
  unfold Ctx.CandGate
  constructor
  · rintro ⟨hg, hU⟩
    refine ⟨(Iff.of_eq hbaseG).mp hg, ?_⟩
    intro u hu
    exact (Iff.of_eq (hbaseU ⟨u, hu⟩)).mp (hU u hu)
  · rintro ⟨hg, hU⟩
    refine ⟨(Iff.of_eq hbaseG).mpr hg, ?_⟩
    intro u hu
    exact (Iff.of_eq (hbaseU ⟨u, hu⟩)).mpr (hU u hu)

def observedInternalTagCoords {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) (π : D.Pres c.1) : Finset (D.KeyT × D.Loc) :=
  ((Finset.univ.filter fun ℓ : D.Loc => (π.1 ℓ).isSome).image fun ℓ => (c.1, ℓ))

def observedCrossTagCoords {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) (π : D.Pres c.1) : Finset (D.KeyT × D.Loc) :=
  (Finset.univ : Finset (D.CrossSub c.1)).image fun u => (u.1, (π.2 u).1)

def observedTagCoords {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) (π : D.Pres c.1) : Finset (D.KeyT × D.Loc) :=
  observedInternalTagCoords D c π ∪ observedCrossTagCoords D c π

noncomputable def observedTagValue {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) (π : D.Pres c.1)
    (default : D.M.ι) (x : D.KeyT × D.Loc) : D.M.ι :=
  if hg : x.1 = c.1 then (π.1 x.2).getD default else
    if hu : x.1 ∈ crossKeys c.1 then
      let u : D.CrossSub c.1 := ⟨x.1, hu⟩
      if hℓ : x.2 = (π.2 u).1 then (π.2 u).2.1 else default
    else default

theorem observed_tag_weight_product {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) (c : D.CellT) (π : D.Pres c.1)
    (default : D.M.ι) :
    (∏ x ∈ observedTagCoords D c π,
        (D.tilt Θ x.1).w (observedTagValue D c π default x)) =
      (∏ ℓ, (π.1 ℓ).elim 1 (fun i => (D.tilt Θ c.1).w i)) *
        ∏ u : D.CrossSub c.1, (D.tilt Θ u.1).w ((π.2 u).2.1) := by
  classical
  let Sint := observedInternalTagCoords D c π
  let Sloc : Finset D.Loc := Finset.univ.filter fun ℓ => (π.1 ℓ).isSome
  let Scross := observedCrossTagCoords D c π
  have hdisj : Disjoint Sint Scross := by
    apply Finset.disjoint_left.mpr
    intro x hxI hxC
    rcases Finset.mem_image.mp hxI with ⟨ℓ, hℓ, rfl⟩
    rcases Finset.mem_image.mp hxC with ⟨u, hu, hEq⟩
    have hkey : u.1 = c.1 := congrArg Prod.fst hEq
    exact cross_key_ne D c.1 u hkey
  have hIinj : Set.InjOn (fun ℓ : D.Loc => (c.1, ℓ)) (Sloc : Set D.Loc) := by
    intro ℓ hℓ ℓ' hℓ' h
    exact congrArg Prod.snd h
  have hInternal :
      (∏ x ∈ Sint, (D.tilt Θ x.1).w (observedTagValue D c π default x)) =
        ∏ ℓ ∈ Sloc, (D.tilt Θ c.1).w ((π.1 ℓ).getD default) := by
    unfold Sint observedInternalTagCoords
    rw [Finset.prod_image hIinj]
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    simp [observedTagValue, Sloc, hℓ]
  have hCinj : Set.InjOn (fun u : D.CrossSub c.1 => (u.1, (π.2 u).1))
      (Finset.univ : Finset (D.CrossSub c.1)) := by
    intro u hu v hv huv
    apply Subtype.ext
    exact congrArg Prod.fst huv
  have hCross :
      (∏ x ∈ Scross, (D.tilt Θ x.1).w (observedTagValue D c π default x)) =
        ∏ u : D.CrossSub c.1, (D.tilt Θ u.1).w ((π.2 u).2.1) := by
    unfold Scross observedCrossTagCoords
    rw [Finset.prod_image hCinj]
    apply Finset.prod_congr rfl
    intro u hu
    have hne : u.1 ≠ c.1 := cross_key_ne D c.1 u
    simp [observedTagValue, hne]
  have hIntFull :
      (∏ ℓ, (π.1 ℓ).elim 1 (fun i => (D.tilt Θ c.1).w i)) =
        ∏ ℓ ∈ Sloc, (D.tilt Θ c.1).w ((π.1 ℓ).getD default) := by
    calc
      (∏ ℓ, (π.1 ℓ).elim 1 (fun i => (D.tilt Θ c.1).w i)) =
          ∏ ℓ, if (π.1 ℓ).isSome then (D.tilt Θ c.1).w ((π.1 ℓ).getD default) else 1 := by
            apply Finset.prod_congr rfl
            intro ℓ hℓ
            cases ho : π.1 ℓ <;> simp [ho]
      _ = ∏ ℓ ∈ Sloc, (D.tilt Θ c.1).w ((π.1 ℓ).getD default) := by
            rw [← Finset.prod_filter]
  unfold observedTagCoords
  rw [Finset.prod_union hdisj, hInternal, hCross]
  rw [← hIntFull]

theorem pres_cross_id_tag {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (q : D.Pre) (W : D.Anch) (c : D.CellT)
    (π : D.Pres c.1) (hpres : D.presOf q W c = π) (u : D.CrossSub c.1) :
    D.crossId q c u = (π.2 u).1 ∧
      q.2.1.1 u.1 (D.crossId q c u) = (π.2 u).2.1 := by
  have hu := congrFun (congrArg Prod.snd hpres) u
  constructor
  · exact congrArg Prod.fst hu
  · have htag := congrArg Prod.fst (congrArg Prod.snd hu)
    simpa [Ctx.presOf] using htag

theorem pres_cross_anchor {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (q : D.Pre) (W : D.Anch) (c : D.CellT)
    (π : D.Pres c.1) (hpres : D.presOf q W c = π) (u : D.CrossSub c.1) :
    W (u.1, c.2) = (π.2 u).2.2 := by
  have hu := congrFun (congrArg Prod.snd hpres) u
  have ha := congrArg Prod.snd (congrArg Prod.snd hu)
  simpa [Ctx.presOf] using ha

theorem pres_tag_spec {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (q : D.Pre) (W : D.Anch) (c : D.CellT)
    (π : D.Pres c.1) (default : D.M.ι) (hpres : D.presOf q W c = π) :
    ∀ x ∈ observedTagCoords D c π,
      q.2.1.1 x.1 x.2 = observedTagValue D c π default x := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hInt | hCross
  · rcases Finset.mem_image.mp hInt with ⟨ℓ, hℓ, rfl⟩
    have hSome : (π.1 ℓ).isSome := (Finset.mem_filter.mp hℓ).2
    have hfirst := congrFun (congrArg Prod.fst hpres) ℓ
    have hIn : ℓ ∈ D.intIds q c := by
      by_contra hnot
      have hnone : π.1 ℓ = none := by
        simpa [Ctx.presOf, hnot] using hfirst.symm
      simp [hnone] at hSome
    have htag : q.2.1.1 c.1 ℓ = (π.1 ℓ).getD default := by
      have heq : some (q.2.1.1 c.1 ℓ) = π.1 ℓ := by
        simpa [Ctx.presOf, hIn] using hfirst
      cases hopt : π.1 ℓ with
      | none => simp [hopt] at hSome
      | some i =>
          have hi : q.2.1.1 c.1 ℓ = i := by simpa [hopt] using heq
          simp [hopt, hi]
    simp [observedTagValue, htag]
  · rcases Finset.mem_image.mp hCross with ⟨u, hu, hEq⟩
    have hId := (pres_cross_id_tag D q W c π hpres u).1
    have htag := (pres_cross_id_tag D q W c π hpres u).2
    rw [hId] at htag
    have hkeyne : u.1 ≠ c.1 := cross_key_ne D c.1 u
    have hpair : x = (u.1, (π.2 u).1) := hEq.symm
    rw [hpair]
    have hval : observedTagValue D c π default (u.1, (π.2 u).1) = (π.2 u).2.1 := by
      simp [observedTagValue, hkeyne]
    rw [hval]
    exact htag

theorem raw_anchors_cross_presentation_le {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (q : D.Pre) (c : D.CellT) (π : D.Pres c.1)
    (A : D.Anch → Prop)
    (hpres : ∀ W, A W → D.presOf q W c = π)
    (hvalid : ∀ W, A W → D.PresValid q W c) :
    (D.rawAnchors q).pr A ≤
      ∏ u : D.CrossSub c.1,
        (D.anchorU q.1.1 u.1 (π.2 u).2.1).w (π.2 u).2.2 := by
  classical
  by_cases hExists : ∃ W, A W
  · obtain ⟨W₀, hW₀⟩ := hExists
    have hp := hpres W₀ hW₀
    have hv := hvalid W₀ hW₀
    have hselLaw (u : D.CrossSub c.1) :
        D.Usel q (u.1, c.2) = D.anchorU q.1.1 u.1 (π.2 u).2.1 := by
      have hsome : (D.sel q (u.1, c.2)).isSome := hv.2.2.1 u
      have hpair := pres_cross_id_tag D q W₀ c π hp u
      cases hsel : D.sel q (u.1, c.2) with
      | none => simp [hsel] at hsome
      | some ℓ =>
          have hId : ℓ = (π.2 u).1 := by simpa [Ctx.crossId, hsel] using hpair.1
          have htagCandidate : q.2.1.1 u.1 (π.2 u).1 = (π.2 u).2.1 := by
            have htag0 := hpair.2
            rw [hpair.1] at htag0
            exact htag0
          have htag : q.2.1.1 u.1 ℓ = (π.2 u).2.1 := by
            rw [hId]
            exact htagCandidate
          simp [Ctx.Usel, Ctx.selTag, hsel, htag]
    have hfix : ∀ W, A W → ∀ u : D.CrossSub c.1,
        W (u.1, c.2) = (π.2 u).2.2 := by
      intro W hW u
      exact pres_cross_anchor D q W c π (hpres W hW) u
    have hinj : Set.InjOn (fun u : D.CrossSub c.1 => (u.1, c.2))
        (Finset.univ : Finset (D.CrossSub c.1)) := by
      intro u hu v hv huv
      apply Subtype.ext
      exact congrArg Prod.fst huv
    have hbound := pi_pr_le_fixed_image
      (fun e : D.CellT => D.Usel q e)
      (Finset.univ : Finset (D.CrossSub c.1))
      (fun u => (u.1, c.2)) hinj (fun u => (π.2 u).2.2) A
      (fun W hW u hu => hfix W hW u)
    calc
      (D.rawAnchors q).pr A ≤
          ∏ u : D.CrossSub c.1, (D.Usel q (u.1, c.2)).w (π.2 u).2.2 := hbound
      _ = ∏ u : D.CrossSub c.1,
          (D.anchorU q.1.1 u.1 (π.2 u).2.1).w (π.2 u).2.2 := by
            apply Finset.prod_congr rfl
            intro u hu
            rw [hselLaw u]
  · have hzero : (D.rawAnchors q).pr A = 0 := by
      unfold FinProb.pr
      apply Finset.sum_eq_zero
      intro W hW
      have hnot : ¬ A W := fun hA => hExists ⟨W, hA⟩
      simp [hnot]
    rw [hzero]
    exact Finset.prod_nonneg fun u hu => (D.anchorU q.1.1 u.1 (π.2 u).2.1).nonneg _

theorem positive_tilt_gate {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι)
    (hbase : D.BaseGates Θ g) (hpos : 0 < (D.tilt Θ g).w i) :
    D.GateOpen Θ g i := by
  have hAG : 0 < D.AG g := by
    unfold Ctx.AG
    exact inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) _)
  have hZ : 0 < D.ZG Θ g := by
    have hgate := hbase.2.1.1
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 10) hAG) hgate
  have hnum : 0 < D.tiltW Θ g i := by
    unfold Ctx.tilt normOr at hpos
    change 0 < (if (∑ i', D.tiltW Θ g i') = 0 then D.tagLaw.w i else
      D.tiltW Θ g i / ∑ i', D.tiltW Θ g i') at hpos
    have hsumpos : 0 < ∑ i', D.tiltW Θ g i' := by
      simpa [Ctx.ZG] using hZ
    rw [if_neg (ne_of_gt hsumpos)] at hpos
    by_contra hn
    have hle : D.tiltW Θ g i ≤ 0 := le_of_not_gt hn
    have hquot : D.tiltW Θ g i / D.ZG Θ g ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hle hZ.le
    exact (not_le_of_gt hpos) (by simpa [Ctx.ZG] using hquot)
  by_contra hgate
  unfold Ctx.tiltW at hnum
  simp [hgate] at hnum

theorem anchor_miss_le {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (hn : 1 ≤ D.n) (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι)
    (ξ : D.Tup) (j : Fin h)
    (htrue : D.GateOpen Θ g i)
    (hcand : D.GateOpen (Function.update Θ g ξ) g i) :
    (D.anchorU Θ g i).pr (fun x => ¬ Hits D.E D.G x (ξ j)) ≤ D.Δ / (1 - D.Δ) := by
  classical
  have hnR : 0 < (D.n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have hpow : 0 < (D.n : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnR _
  have hΔpos : 0 < D.Δ := Real.exp_pos _
  have hΔlt : D.Δ < 1 := by
    unfold Ctx.Δ
    have hlt : Real.exp (-((D.n : ℝ) ^ (p / 2))) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (neg_neg_of_pos hpow)
    simpa using hlt
  have hfactor : 0 < 1 - D.Δ := sub_pos.mpr hΔlt
  have hcut : 0 < D.cut := Real.exp_pos _
  have hdmpos : 0 < D.dMinus Θ g i := lt_of_lt_of_le hcut htrue.1
  have hdptrue : 0 < D.dPlus Θ g i := by
    have hineq := htrue.2
    have hprod : 0 < (1 - D.Δ) * D.dMinus Θ g i := mul_pos hfactor hdmpos
    exact lt_of_lt_of_le hprod hineq
  have hcross_update (x : Fin D.N) :
      D.crossHit (Function.update Θ g ξ) g x ↔ D.crossHit Θ g x := by
    constructor
    · intro hx u hu
      have hne : u ≠ g := by
        intro heq
        subst u
        have hdist : keyDist g g = 0 := by simp [keyDist]
        have hu' : keyDist g g = 1 := by simpa [crossKeys] using hu
        rw [hdist] at hu'
        norm_num at hu'
      have hval : (Function.update Θ g ξ) u = Θ u := Function.update_of_ne hne ξ Θ
      simpa [hval] using hx u hu
    · intro hx u hu
      have hne : u ≠ g := by
        intro heq
        subst u
        have hdist : keyDist g g = 0 := by simp [keyDist]
        have hu' : keyDist g g = 1 := by simpa [crossKeys] using hu
        rw [hdist] at hu'
        norm_num at hu'
      have hval : (Function.update Θ g ξ) u = Θ u := Function.update_of_ne hne ξ Θ
      simpa [hval] using hx u hu
  have hown_update (x : Fin D.N) :
      D.ownHit (Function.update Θ g ξ) g x ↔ D.crossHit Θ g x ∧ D.hitsAll x ξ := by
    simp [Ctx.ownHit, Ctx.hitsAll, hcross_update, Function.update]
  have hdmEq : D.dMinus (Function.update Θ g ξ) g i = D.dMinus Θ g i := by
    unfold Ctx.dMinus
    apply Finset.sum_congr rfl
    intro x hx
    simp only [hcross_update]
  have hdpCand : (1 - D.Δ) * D.dMinus Θ g i ≤
      D.dPlus (Function.update Θ g ξ) g i := by
    simpa [hdmEq] using hcand.2
  have hmass_miss_le :
      (∑ x, (D.M.μ i).w x *
        if D.crossHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) ≤
        D.dMinus Θ g i - D.dPlus (Function.update Θ g ξ) g i := by
    unfold Ctx.dMinus Ctx.dPlus
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hcross : D.crossHit Θ g x
    · by_cases hall : D.hitsAll x ξ
      · have hj : Hits D.E D.G x (ξ j) := hall j
        simp [hcross, hall, hj, hown_update]
      · have hnotown : ¬ D.ownHit (Function.update Θ g ξ) g x := by
          rw [hown_update]
          simp [hcross, hall]
        by_cases hmiss : ¬ Hits D.E D.G x (ξ j)
        · simp [hcross, hmiss, hnotown, (D.M.μ i).nonneg x]
        · simp [hcross, hmiss, hnotown]
          exact (D.M.μ i).nonneg x
    · have hnotown : ¬ D.ownHit (Function.update Θ g ξ) g x := by
        rw [hown_update]
        simp [hcross]
      simp [hcross, hnotown]
  have hmissmass :
      (∑ x, (D.M.μ i).w x *
        if D.ownHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) ≤
        (∑ x, (D.M.μ i).w x *
          if D.crossHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) := by
    apply Finset.sum_le_sum
    intro x hx
    have hown : D.ownHit Θ g x → D.crossHit Θ g x := fun ho => ho.1
    by_cases hbad : D.ownHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j)
    · have hbad' : D.crossHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) := ⟨hown hbad.1, hbad.2⟩
      simp [hbad, hbad']
    · by_cases hcross : D.crossHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j)
      · have hnotown : ¬ D.ownHit Θ g x := by
          intro ho
          exact hbad ⟨ho, hcross.2⟩
        simp [hbad, hcross, hnotown]
        exact (D.M.μ i).nonneg x
      · simp [hbad, hcross]
  have hnumBound :
      (∑ x, (D.M.μ i).w x *
        if D.ownHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) ≤
        D.Δ * D.dMinus Θ g i := by
    calc
      _ ≤ ∑ x, (D.M.μ i).w x *
            if D.crossHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0 := hmissmass
      _ ≤ D.dMinus Θ g i - D.dPlus (Function.update Θ g ξ) g i := hmass_miss_le
      _ ≤ D.dMinus Θ g i - (1 - D.Δ) * D.dMinus Θ g i := by linarith [hdpCand]
      _ = D.Δ * D.dMinus Θ g i := by ring
  have hprob : (D.anchorU Θ g i).pr (fun x => ¬ Hits D.E D.G x (ξ j)) =
      (∑ x, (D.M.μ i).w x *
        if D.ownHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) /
        D.dPlus Θ g i := by
    have hden : (∑ x, (D.M.μ i).w x * if D.ownHit Θ g x then 1 else 0) =
        D.dPlus Θ g i := rfl
    have hdenpos : 0 < ∑ x, (D.M.μ i).w x * if D.ownHit Θ g x then 1 else 0 := by
      simpa [Ctx.dPlus] using hdptrue
    simp only [FinProb.pr, Ctx.anchorU, normOr]
    simp only [if_neg (ne_of_gt hdenpos)]
    simp_rw [hden]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hm : ¬ Hits D.E D.G x (ξ j) <;>
      by_cases ho : D.ownHit Θ g x <;> simp [hm, ho] <;> ring
  rw [hprob]
  apply (div_le_iff₀ hdptrue).2
  calc
    (∑ x, (D.M.μ i).w x *
      if D.ownHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) ≤
        D.Δ * D.dMinus Θ g i := hnumBound
    _ ≤ (D.Δ / (1 - D.Δ)) * D.dPlus Θ g i := by
      calc
        D.Δ * D.dMinus Θ g i =
            (D.Δ / (1 - D.Δ)) * ((1 - D.Δ) * D.dMinus Θ g i) := by
          field_simp [ne_of_gt hfactor]
        _ ≤ (D.Δ / (1 - D.Δ)) * D.dPlus Θ g i :=
          mul_le_mul_of_nonneg_left htrue.2 (div_nonneg hΔpos.le hfactor.le)

theorem one_sub_prod_le_sum {α : Type*} [Fintype α] (s : Finset α) (a : α → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∏ i ∈ s, (1 - a i) ≤ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hi0 := ha0 i (Finset.mem_insert_self i s)
      have hi1 := ha1 i (Finset.mem_insert_self i s)
      have hs0 : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha0 j (Finset.mem_insert_of_mem hj)
      have hs1 : ∀ j ∈ s, a j ≤ 1 := fun j hj => ha1 j (Finset.mem_insert_of_mem hj)
      have hprod0 : 0 ≤ ∏ j ∈ s, (1 - a j) :=
        Finset.prod_nonneg fun j hj => sub_nonneg.mpr (hs1 j hj)
      have hprod1 : ∏ j ∈ s, (1 - a j) ≤ 1 :=
        Finset.prod_le_one₀ (fun j hj => sub_nonneg.mpr (hs1 j hj))
          (fun j hj => by linarith [hs0 j hj])
      rw [Finset.prod_insert his, Finset.sum_insert his]
      calc
        1 - (1 - a i) * ∏ j ∈ s, (1 - a j) =
            (1 - ∏ j ∈ s, (1 - a j)) + a i * ∏ j ∈ s, (1 - a j) := by ring
        _ ≤ (∑ j ∈ s, a j) + a i := by
          have hmul := mul_le_mul_of_nonneg_left hprod1 hi0
          have hih := ih hs0 hs1
          linarith
        _ = a i + ∑ j ∈ s, a j := by ring

theorem pr_compl {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A + P.pr (fun ω => ¬ A ω) = 1 := by
  classical
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib]
  calc
    (∑ ω, ((if A ω then P.w ω else 0) +
        (@ite ℝ ((fun ω => ¬ A ω) ω)
          (Classical.propDecidable ((fun ω => ¬ A ω) ω)) (P.w ω) 0))) =
        ∑ ω, P.w ω := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : A ω <;> simp [h]
    _ = 1 := P.sum_eq_one

theorem pr_eq_weighted_indicator {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A = ∑ ω, P.w ω *
      (@ite ℝ (A ω) (Classical.propDecidable (A ω)) (1 : ℝ) 0) := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : A ω <;> simp [h]

theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A B : Ω → Prop)
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω
    · simp [hA, hB, P.nonneg ω]
    · simp [hA, hB]

theorem prod_pr_le_left {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α × β → Prop) (B : α → Prop)
    (hAB : ∀ x, A x → B x.1) : (P.prod Q).pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr FinProb.prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hB : B a
  · calc
      (∑ b, if A (a, b) then P.w a * Q.w b else 0) ≤
          ∑ b, P.w a * Q.w b := by
            apply Finset.sum_le_sum
            intro b hb
            by_cases hA : A (a, b)
            · simp [hA]
            · simp only [if_neg hA]
              exact mul_nonneg (P.nonneg a) (Q.nonneg b)
      _ = P.w a := by
            rw [← Finset.mul_sum, Q.sum_eq_one, mul_one]
      _ = if B a then P.w a else 0 := by simp [hB]
  · have hnoA : ∀ b, ¬ A (a, b) := by
      intro b hA
      exact hB (hAB (a, b) hA)
    simp [hB, hnoA]

theorem bind_pr_eq_sum {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (A : α × β → Prop) :
    (FinProb.bind P K).pr A =
      ∑ a, P.w a * (K a).pr (fun b => A (a, b)) := by
  classical
  unfold FinProb.pr FinProb.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b, if A (a, b) then P.w a * (K a).w b else 0) =
        ∑ b, P.w a * (if A (a, b) then (K a).w b else 0) := by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases h : A (a, b) <;> simp [h]
    _ = P.w a * ∑ b, if A (a, b) then (K a).w b else 0 := by
          rw [Finset.mul_sum]
    _ = P.w a * (K a).pr (fun b => A (a, b)) := by rfl

theorem rawTAT_pr_le_tags {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist)
    (A : D.TAT → Prop) (B : D.Tags → Prop)
    (hAB : ∀ z, A z → B z.1.1) :
    (D.rawTAT Θ).pr A ≤ (D.tagLawAll Θ).pr B := by
  calc
    (D.rawTAT Θ).pr A ≤ ((D.tagLawAll Θ).prod D.actLaw).pr (fun x => B x.1) := by
      unfold Ctx.rawTAT
      exact prod_pr_le_left ((D.tagLawAll Θ).prod D.actLaw) D.tieLaw A
        (fun x => B x.1) (fun z hz => hAB z hz)
    _ ≤ (D.tagLawAll Θ).pr B :=
      prod_pr_le_left (D.tagLawAll Θ) D.actLaw (fun x => B x.1) B (fun x hx => hx)

theorem sum_subtype_const {α : Type*} [DecidableEq α] (s : Finset α) (r : ℝ) :
    (∑ x : s, r) = (Fintype.card s : ℝ) * r := by
  classical
  simp [Finset.sum_const, nsmul_eq_mul]

theorem prod_div_cancel {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f g : α → ℝ) (hg : ∀ i ∈ s, g i ≠ 0) :
    (∏ i ∈ s, f i / g i) * (∏ i ∈ s, g i) = ∏ i ∈ s, f i := by
  classical
  have hprod : (∏ i ∈ s, g i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hg
  rw [Finset.prod_div_distrib]
  exact div_mul_cancel₀ _ hprod

theorem pi_pr_not_forall_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} [Fintype α] (P : ι → FinProb α) (A : ι → α → Prop) :
    (FinProb.pi P).pr (fun ω => ¬ ∀ i, A i (ω i)) ≤
      ∑ i, (P i).pr (fun x => ¬ A i x) := by
  classical
  have hcompl : (FinProb.pi P).pr (fun ω => ¬ ∀ i, A i (ω i)) =
      1 - (FinProb.pi P).pr (fun ω => ∀ i, A i (ω i)) := by
    have h := pr_compl (FinProb.pi P) (fun ω => ∀ i, A i (ω i))
    linarith
  have hfactor : (FinProb.pi P).pr (fun ω => ∀ i, A i (ω i)) =
      ∏ i, (P i).pr (A i) := FinProb.pi_pr_forall P A
  have hprod : (∏ i, (P i).pr (A i)) =
      ∏ i, (1 - (P i).pr (fun x => ¬ A i x)) := by
    apply Finset.prod_congr rfl
    intro i hi
    have h := pr_compl (P i) (A i)
    linarith
  have hmiss0 (i : ι) : 0 ≤ (P i).pr (fun x => ¬ A i x) := pr_nonneg _ _
  have hmiss1 (i : ι) : (P i).pr (fun x => ¬ A i x) ≤ 1 := by
    have h := pr_compl (P i) (A i)
    have hnonneg : 0 ≤ (P i).pr (A i) := pr_nonneg _ _
    linarith
  rw [hcompl, hfactor, hprod]
  exact one_sub_prod_le_sum Finset.univ (fun i => (P i).pr (fun x => ¬ A i x))
    (fun i hi => hmiss0 i) (fun i hi => hmiss1 i)

theorem pi_pr_coordinate {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    [DecidableEq Ω] (P : ι → FinProb Ω) (j : ι) (y : Ω) :
    (FinProb.pi P).pr (fun ω => ω j = y) = (P j).w y := by
  classical
  let A : ι → Ω → Prop := fun i x => if i = j then x = y else True
  have hiff (ω : ι → Ω) : (∀ i, A i (ω i)) ↔ ω j = y := by
    constructor
    · intro h
      have hj := h j
      simpa [A] using hj
    · intro h i
      by_cases hi : i = j
      · subst i
        simpa [A] using h
      · simp [A, hi]
  have hpr : (FinProb.pi P).pr (fun ω => ∀ i, A i (ω i)) =
      (FinProb.pi P).pr (fun ω => ω j = y) := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : ω j = y
    · have hall : ∀ i, A i (ω i) := hiff ω |>.2 h
      simp [hall, h]
    · have hnot : ¬ ∀ i, A i (ω i) := fun hall => h (hiff ω |>.1 hall)
      simp [hnot, h]
  have hrow : ∏ i, (P i).pr (A i) = (P j).pr (fun x => x = y) := by
    have htrue (i : ι) : (P i).pr (fun _ : Ω => True) = 1 := by
      unfold FinProb.pr
      simp [ (P i).sum_eq_one ]
    calc
      ∏ i, (P i).pr (A i) = ∏ i, if i = j then (P j).pr (fun x => x = y) else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases h : i = j
        · subst i
          simp [A]
        · simpa [A, h] using htrue i
      _ = (P j).pr (fun x => x = y) := by simp
  have hfactor := FinProb.pi_pr_forall P A
  calc
    (FinProb.pi P).pr (fun ω => ω j = y) =
        (FinProb.pi P).pr (fun ω => ∀ i, A i (ω i)) := hpr.symm
    _ = ∏ i, (P i).pr (A i) := hfactor
    _ = (P j).pr (fun x => x = y) := hrow
    _ = (P j).w y := by
      unfold FinProb.pr
      rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
      · simp
      · intro x hx hxy
        simp [hxy]

theorem map_prod {α β γ δ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ]
    (P : FinProb α) (Q : FinProb β) (f : α → γ) (g : β → δ) :
    FinProb.map (P.prod Q) (fun x => (f x.1, g x.2)) =
      (FinProb.map P f).prod (FinProb.map Q g) := by
  classical
  apply FinProb.ext
  intro z
  change (∑ x : α × β,
      if (f x.1, g x.2) = z then P.w x.1 * Q.w x.2 else 0) =
    (∑ a, if f a = z.1 then P.w a else 0) *
      ∑ b, if g b = z.2 then Q.w b else 0
  rw [Fintype.sum_prod_type]
  have hterm (a : α) (b : β) :
      (if (f a, g b) = z then P.w a * Q.w b else 0) =
        (if f a = z.1 then P.w a else 0) * (if g b = z.2 then Q.w b else 0) := by
    by_cases ha : f a = z.1
    · by_cases hb : g b = z.2
      · simp [ha, hb]
      · have hpair : (f a, g b) ≠ z := by
          intro hh
          exact hb (congrArg Prod.snd hh)
        rw [if_neg hpair]
        simp [ha, hb]
    · by_cases hb : g b = z.2
      · have hpair : (f a, g b) ≠ z := by
          intro hh
          exact ha (congrArg Prod.fst hh)
        rw [if_neg hpair]
        simp [ha, hb]
      · have hpair : (f a, g b) ≠ z := by
          intro hh
          exact ha (congrArg Prod.fst hh)
        rw [if_neg hpair]
        simp [ha, hb]
  calc
    (∑ a, ∑ b, if (f a, g b) = z then P.w a * Q.w b else 0) =
        ∑ a, ∑ b,
          (if f a = z.1 then P.w a else 0) * (if g b = z.2 then Q.w b else 0) := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro b
      exact hterm a b
    _ = (∑ a, if f a = z.1 then P.w a else 0) *
        ∑ b, if g b = z.2 then Q.w b else 0 := by
      rw [Fintype.sum_mul_sum]

theorem map_pi_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (S : Finset ι) :
    FinProb.map (FinProb.pi P) (fun ω (i : {i // i ∈ S}) => ω i.1) =
      FinProb.pi (fun i : {i // i ∈ S} => P i.1) := by
  classical
  apply FinProb.ext
  intro a
  exact FinProb.pi_marginal P S a

theorem map_pi_restrict_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P Q : ∀ i, FinProb (Ω i)) (S : Finset ι)
    (hPQ : ∀ i ∈ S, P i = Q i) :
    FinProb.map (FinProb.pi P) (fun ω (i : {i // i ∈ S}) => ω i.1) =
      FinProb.map (FinProb.pi Q) (fun ω (i : {i // i ∈ S}) => ω i.1) := by
  classical
  rw [map_pi_restrict P S, map_pi_restrict Q S]
  apply FinProb.ext
  intro a
  simp only [FinProb.pi]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun R : FinProb (Ω i.1) => R.w (a i)) (hPQ i.1 i.2)

abbrev LocalTagSample {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) :=
      {g : D.KeyT // g ∈ keyBall c.1 3} → D.Loc → D.M.ι

abbrev LocalActSample {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) :=
      {g : D.KeyT // g ∈ keyBall c.1 1} → D.Loc → Bool

abbrev LocalTieSample {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) :=
      {g : D.KeyT // g ∈ keyBall c.1 1} → (hdP η₀ D.n).Ties

abbrev LocalTATSample {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) :=
      ((LocalTagSample D c × LocalActSample D c) × LocalTieSample D c)

instance localTagSampleFintype {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : Fintype (LocalTagSample D c) := inferInstance

instance localActSampleFintype {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : Fintype (LocalActSample D c) := inferInstance

instance localTieSampleFintype {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : Fintype (LocalTieSample D c) := inferInstance

instance localTATSampleFintype {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : Fintype (LocalTATSample D c) := inferInstance

noncomputable instance localTagSampleDecidableEq {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : DecidableEq (LocalTagSample D c) := by
  dsimp [LocalTagSample]
  letI : DecidableEq (D.Loc → D.M.ι) := Fintype.decidablePiFintype
  exact Fintype.decidablePiFintype

noncomputable instance localActSampleDecidableEq {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : DecidableEq (LocalActSample D c) := by
  dsimp [LocalActSample]
  letI : DecidableEq (D.Loc → Bool) := Fintype.decidablePiFintype
  exact Fintype.decidablePiFintype

noncomputable instance localTieSampleDecidableEq {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : DecidableEq (LocalTieSample D c) := by
  dsimp [LocalTieSample]
  exact Fintype.decidablePiFintype

noncomputable instance localTATSampleDecidableEq {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : DecidableEq (LocalTATSample D c) := by
  dsimp [LocalTATSample]
  exact instDecidableEqProd

def localTagsProj {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : D.Tags → LocalTagSample D c :=
  fun t g => t g.1

def localActsProj {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : D.Acts → LocalActSample D c :=
  fun a g => a g.1

def localTiesProj {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : D.TieAll → LocalTieSample D c :=
  fun τ g => τ g.1

def localTATProj {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : D.TAT → LocalTATSample D c :=
  fun z => ((localTagsProj D c z.1.1, localActsProj D c z.1.2), localTiesProj D c z.2)

def crossCellSet {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : Finset D.CellT :=
  Finset.univ.image fun u : D.CrossSub c.1 => (u.1, c.2)

abbrev LocalAnchorSample {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) :=
      {e : D.CellT // e ∈ crossCellSet D c} → Fin D.N

instance localAnchorSampleFintype {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : Fintype (LocalAnchorSample D c) := inferInstance

noncomputable instance localAnchorSampleDecidableEq {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : DecidableEq (LocalAnchorSample D c) :=
  Fintype.decidablePiFintype

def localAnchorsProj {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) : D.Anch → LocalAnchorSample D c :=
  fun W e => W e.1

def completeLocalTAT {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) (base : D.TAT)
    (t : LocalTATSample D c) : D.TAT :=
  ((fun g ℓ => if hg : g ∈ keyBall c.1 3 then t.1.1 ⟨g, hg⟩ ℓ else base.1.1 g ℓ,
    fun g ℓ => if hg : g ∈ keyBall c.1 1 then t.1.2 ⟨g, hg⟩ ℓ else base.1.2 g ℓ),
    fun g => if hg : g ∈ keyBall c.1 1 then t.2 ⟨g, hg⟩ else base.2 g)

def completeLocalAnchors {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) (base : D.Anch)
    (a : LocalAnchorSample D c) : D.Anch :=
  fun e => if he : e ∈ crossCellSet D c then a ⟨e, he⟩ else base e

theorem localTATProj_completeLocalTAT {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) (base : D.TAT) (t : LocalTATSample D c) :
    localTATProj D c (completeLocalTAT D c base t) = t := by
  classical
  apply Prod.ext
  · apply Prod.ext
    · funext g ℓ
      simp [localTATProj, localTagsProj, completeLocalTAT]
    · funext g ℓ
      simp [localTATProj, localActsProj, completeLocalTAT]
  · funext g
    simp [localTATProj, localTiesProj, completeLocalTAT]

theorem localAnchorsProj_completeLocalAnchors {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) (base : D.Anch) (a : LocalAnchorSample D c) :
    localAnchorsProj D c (completeLocalAnchors D c base a) = a := by
  classical
  funext e
  simp [localAnchorsProj, completeLocalAnchors]

theorem rprime_pr_coordinate {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (j : Fin h) (y : Fin D.N) :
    D.R'.pr (fun ξ => ξ j = y) = ∑ i, D.M.Λ i * (D.M.ν i).w y := by
  classical
  rw [Ctx.R', FinProb.map_pr]
  calc
    (FinProb.bind D.tagLaw (fun i => FinProb.pi fun _ : Fin h => D.M.ν i)).pr
        (fun ix => ix.2 j = y) =
        ∑ i, D.tagLaw.w i *
          (FinProb.pi (fun _ : Fin h => D.M.ν i)).pr (fun ξ => ξ j = y) :=
      Lane_q_s08_post.bind_pr_eq_sum _ _ _
    _ = ∑ i, D.M.Λ i * (D.M.ν i).w y := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Lane_q_s08_post.pi_pr_coordinate]
      rfl

theorem avgMarg_rprime {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hh : 0 < h) (y : Fin D.N) :
    averageCoordinateMarginal D.R' y = ∑ i, D.M.Λ i * (D.M.ν i).w y := by
  classical
  let m : ℝ := ∑ i, D.M.Λ i * (D.M.ν i).w y
  have hcoord (j : Fin h) : D.R'.pr (fun ξ => ξ j = y) = m := by
    rw [Lane_q_s08_post.rprime_pr_coordinate]
  unfold averageCoordinateMarginal
  simp_rw [hcoord]
  have hsum : (∑ j : Fin h, m) = (h : ℝ) * m := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  dsimp [m]
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  field_simp

theorem avgMarg_rprime_le_balanced {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hh : 0 < h) (hN : 0 < D.N)
    (K : ℝ) (hBal : D.M.Balanced (4 * K)) (y : Fin D.N) :
    averageCoordinateMarginal D.R' y ≤ 4 * K / D.N := by
  rw [avgMarg_rprime D hh y]
  have hN' : (0 : ℝ) < D.N := by exact_mod_cast hN
  apply (le_div_iff₀ hN').2
  simpa [mul_comm] using hBal.2 y

theorem tilt_congr_of_local {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT)
    (h0 : Θ g = Θ' g) (hcross : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.tilt Θ g = D.tilt Θ' g := by
  classical
  have hCrossHit (x : Fin D.N) : D.crossHit Θ g x = D.crossHit Θ' g x := by
    apply propext
    constructor
    · intro hx u hu
      rw [← hcross u hu]
      exact hx u hu
    · intro hx u hu
      rw [hcross u hu]
      exact hx u hu
  have hOwnHit (x : Fin D.N) : D.ownHit Θ g x = D.ownHit Θ' g x := by
    simp [Ctx.ownHit, Ctx.hitsAll, hCrossHit, h0]
  have hMinus (i : D.M.ι) : D.dMinus Θ g i = D.dMinus Θ' g i := by
    unfold Ctx.dMinus
    apply Finset.sum_congr rfl
    intro x hx
    simp [hCrossHit]
  have hPlus (i : D.M.ι) : D.dPlus Θ g i = D.dPlus Θ' g i := by
    unfold Ctx.dPlus
    apply Finset.sum_congr rfl
    intro x hx
    simp [hOwnHit]
  have hpost (i : D.M.ι) : D.postW (Θ g) i = D.postW (Θ' g) i := by rw [h0]
  have hgate (i : D.M.ι) : D.GateOpen Θ g i = D.GateOpen Θ' g i := by
    unfold Ctx.GateOpen
    rw [hMinus, hPlus]
  have hweight (i : D.M.ι) : D.tiltW Θ g i = D.tiltW Θ' g i := by
    unfold Ctx.tiltW
    rw [hpost, hMinus, hgate]
  have hZ : D.ZG Θ g = D.ZG Θ' g := by
    unfold Ctx.ZG
    apply Finset.sum_congr rfl
    intro i hi
    exact hweight i
  unfold Ctx.ZG at hZ
  apply FinProb.ext
  intro i
  simp only [Ctx.tilt, normOr]
  rw [hZ, hweight i]

theorem anchorU_congr_of_local {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT) (i : D.M.ι)
    (h0 : Θ g = Θ' g) (hcross : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.anchorU Θ g i = D.anchorU Θ' g i := by
  classical
  have hCrossHit (x : Fin D.N) : D.crossHit Θ g x = D.crossHit Θ' g x := by
    apply propext
    constructor
    · intro hx u hu
      rw [← hcross u hu]
      exact hx u hu
    · intro hx u hu
      rw [hcross u hu]
      exact hx u hu
  have hOwnHit (x : Fin D.N) : D.ownHit Θ g x = D.ownHit Θ' g x := by
    simp [Ctx.ownHit, Ctx.hitsAll, hCrossHit, h0]
  have hweight (x : Fin D.N) :
      (D.M.μ i).w x * (if D.ownHit Θ g x then 1 else 0) =
        (D.M.μ i).w x * (if D.ownHit Θ' g x then 1 else 0) := by
    simp [hOwnHit x]
  have hZ :
      (∑ x, (D.M.μ i).w x * if D.ownHit Θ g x then 1 else 0) =
        ∑ x, (D.M.μ i).w x * if D.ownHit Θ' g x then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hweight x
  apply FinProb.ext
  intro x
  simp only [Ctx.anchorU, normOr]
  rw [hZ, hweight x]

theorem refInt_congr_of_local {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT)
    (hcross : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.refInt Θ g = D.refInt Θ' g := by
  classical
  have hCrossHit (x : Fin D.N) : D.crossHit Θ g x = D.crossHit Θ' g x := by
    apply propext
    constructor
    · intro hx u hu
      rw [← hcross u hu]
      exact hx u hu
    · intro hx u hu
      rw [hcross u hu]
      exact hx u hu
  have hMinus (i : D.M.ι) : D.dMinus Θ g i = D.dMinus Θ' g i := by
    unfold Ctx.dMinus
    apply Finset.sum_congr rfl
    intro x hx
    simp [hCrossHit]
  have hweight (i : D.M.ι) :
      D.M.Λ i * D.dMinus Θ g i = D.M.Λ i * D.dMinus Θ' g i := by rw [hMinus]
  have hZ : (∑ i, D.M.Λ i * D.dMinus Θ g i) =
      ∑ i, D.M.Λ i * D.dMinus Θ' g i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hweight i
  apply FinProb.ext
  intro i
  simp only [Ctx.refInt, normOr]
  rw [hZ, hweight i]

theorem refCross_congr_radius_two {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT) (u : D.CrossSub g)
    (hΘ : ∀ w ∈ keyBall g 2, Θ w = Θ' w) :
    D.refCross Θ g u.1 = D.refCross Θ' g u.1 := by
  classical
  have huDist : keyDist g u.1 ≤ 1 := (Finset.mem_filter.mp u.2).2.le
  have hu : u.1 ∈ keyBall g 2 := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, huDist.trans (by omega)⟩
  have hpost : D.postW (Θ u.1) = D.postW (Θ' u.1) := by rw [hΘ u.1 hu]
  have hOmit (x : Fin D.N) : D.omitHit Θ u.1 g x = D.omitHit Θ' u.1 g x := by
    apply propext
    constructor
    · intro hx w hw
      rcases Finset.mem_erase.mp hw with ⟨_, hwCross⟩
      have htri := keyDist_triangle_aux g u.1 w
      have hgw : keyDist g w ≤ 2 := by
        have huw : keyDist u.1 w = 1 := (Finset.mem_filter.mp hwCross).2
        omega
      have hwBall : w ∈ keyBall g 2 := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hgw⟩
      rw [← hΘ w hwBall]
      exact hx w hw
    · intro hx w hw
      rcases Finset.mem_erase.mp hw with ⟨_, hwCross⟩
      have htri := keyDist_triangle_aux g u.1 w
      have hgw : keyDist g w ≤ 2 := by
        have huw : keyDist u.1 w = 1 := (Finset.mem_filter.mp hwCross).2
        omega
      have hwBall : w ∈ keyBall g 2 := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hgw⟩
      rw [hΘ w hwBall]
      exact hx w hw
  have hweight (q : D.M.ι × Fin D.N) :
      D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
          (if D.omitHit Θ u.1 g q.2 then 1 else 0) =
        D.postW (Θ' u.1) q.1 * (D.M.μ q.1).w q.2 *
          (if D.omitHit Θ' u.1 g q.2 then 1 else 0) := by
    rw [hpost]
    simp [hOmit]
  have hZ :
      (∑ q : D.M.ι × Fin D.N,
        D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
          if D.omitHit Θ u.1 g q.2 then 1 else 0) =
        ∑ q : D.M.ι × Fin D.N,
          D.postW (Θ' u.1) q.1 * (D.M.μ q.1).w q.2 *
            if D.omitHit Θ' u.1 g q.2 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro q hq
    exact hweight q
  apply FinProb.ext
  intro q
  simp only [Ctx.refCross, normOr]
  rw [hZ, hweight q]

theorem refInt_congr_off_target {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT)
    (hAway : ∀ v, v ≠ g → Θ v = Θ' v) :
    D.refInt Θ g = D.refInt Θ' g := by
  apply Lane_q_s08_post.refInt_congr_of_local D Θ Θ' g
  intro u hu
  exact hAway u (cross_key_ne D g ⟨u, hu⟩)

theorem refCross_congr_off_target {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT) (u : D.CrossSub g)
    (hAway : ∀ v, v ≠ g → Θ v = Θ' v) :
    D.refCross Θ g u.1 = D.refCross Θ' g u.1 := by
  classical
  have hu_ne : u.1 ≠ g := cross_key_ne D g u
  have hpost : D.postW (Θ u.1) = D.postW (Θ' u.1) := by
    rw [hAway u.1 hu_ne]
  have hOmit (x : Fin D.N) : D.omitHit Θ u.1 g x = D.omitHit Θ' u.1 g x := by
    apply propext
    constructor
    · intro hx w hw
      rcases Finset.mem_erase.mp hw with ⟨hwne, hwcross⟩
      rw [← hAway w hwne]
      exact hx w hw
    · intro hx w hw
      rcases Finset.mem_erase.mp hw with ⟨hwne, hwcross⟩
      rw [hAway w hwne]
      exact hx w hw
  have hweight (q : D.M.ι × Fin D.N) :
      D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
          (if D.omitHit Θ u.1 g q.2 then 1 else 0) =
        D.postW (Θ' u.1) q.1 * (D.M.μ q.1).w q.2 *
          (if D.omitHit Θ' u.1 g q.2 then 1 else 0) := by
    rw [hpost]
    simp [hOmit]
  have hZ :
      (∑ q : D.M.ι × Fin D.N,
        D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
          if D.omitHit Θ u.1 g q.2 then 1 else 0) =
        ∑ q : D.M.ι × Fin D.N,
          D.postW (Θ' u.1) q.1 * (D.M.μ q.1).w q.2 *
            if D.omitHit Θ' u.1 g q.2 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro q hq
    exact hweight q
  apply FinProb.ext
  intro q
  simp only [Ctx.refCross, normOr]
  rw [hZ, hweight q]

set_option maxHeartbeats 1000000 in
theorem rawTAT_local_projection_congr {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (c : D.CellT)
    (hΘ : ∀ v, keyDist c.1 v ≤ 4 → Θ v = Θ' v) :
    FinProb.map (D.rawTAT Θ) (localTATProj D c) =
      FinProb.map (D.rawTAT Θ') (localTATProj D c) := by
  classical
  letI : Fintype (LocalTagSample D c) := inferInstance
  letI : Fintype (LocalActSample D c) := inferInstance
  letI : Fintype (LocalTieSample D c) := inferInstance
  letI : Fintype (LocalTATSample D c) := inferInstance
  have htag : FinProb.map (D.tagLawAll Θ) (localTagsProj D c) =
      FinProb.map (D.tagLawAll Θ') (localTagsProj D c) := by
    have hslice (g : {g : D.KeyT // g ∈ keyBall c.1 3}) :
        FinProb.pi (fun _ : D.Loc => D.tilt Θ g.1) =
          FinProb.pi (fun _ : D.Loc => D.tilt Θ' g.1) := by
      have hgDist : keyDist c.1 g.1 ≤ 3 := (Finset.mem_filter.mp g.2).2
      have hg4 : keyDist c.1 g.1 ≤ 4 := by omega
      have hg0 : Θ g.1 = Θ' g.1 := hΘ g.1 hg4
      have hcross : ∀ u ∈ crossKeys g.1, Θ u = Θ' u := by
        intro u hu
        have htri := keyDist_triangle_aux c.1 g.1 u
        have hgu : keyDist g.1 u = 1 := (Finset.mem_filter.mp hu).2
        have hcu : keyDist c.1 u ≤ 4 := by omega
        exact hΘ u hcu
      have hlaw := Lane_q_s08_post.tilt_congr_of_local D Θ Θ' g.1 hg0 hcross
      apply FinProb.ext
      intro t
      simp only [FinProb.pi]
      apply Finset.prod_congr rfl
      intro ℓ hℓ
      exact congrArg (fun Q : FinProb D.M.ι => Q.w (t ℓ)) hlaw
    have hleft := Lane_q_s08_post.map_pi_restrict
      (fun g : D.KeyT => FinProb.pi (fun _ : D.Loc => D.tilt Θ g))
      (keyBall c.1 3)
    have hright := Lane_q_s08_post.map_pi_restrict
      (fun g : D.KeyT => FinProb.pi (fun _ : D.Loc => D.tilt Θ' g))
      (keyBall c.1 3)
    calc
      FinProb.map (D.tagLawAll Θ) (localTagsProj D c) =
          FinProb.pi (fun g : {g : D.KeyT // g ∈ keyBall c.1 3} =>
            FinProb.pi (fun _ : D.Loc => D.tilt Θ g.1)) := by
        change FinProb.map (FinProb.pi (fun g : D.KeyT =>
            FinProb.pi (fun _ : D.Loc => D.tilt Θ g)))
          (fun t (g : {g : D.KeyT // g ∈ keyBall c.1 3}) => t g.1) = _
        exact hleft
      _ = FinProb.pi (fun g : {g : D.KeyT // g ∈ keyBall c.1 3} =>
            FinProb.pi (fun _ : D.Loc => D.tilt Θ' g.1)) := by
        apply FinProb.ext
        intro t
        simp only [FinProb.pi]
        apply Finset.prod_congr rfl
        intro g hg
        exact congrArg (fun Q : FinProb (D.Loc → D.M.ι) => Q.w (t g)) (hslice g)
      _ = FinProb.map (D.tagLawAll Θ') (localTagsProj D c) := by
        change _ = FinProb.map (FinProb.pi (fun g : D.KeyT =>
            FinProb.pi (fun _ : D.Loc => D.tilt Θ' g)))
          (fun t (g : {g : D.KeyT // g ∈ keyBall c.1 3}) => t g.1)
        exact hright.symm
  have hta :
      FinProb.map ((D.tagLawAll Θ).prod D.actLaw)
          (fun x => (localTagsProj D c x.1, localActsProj D c x.2)) =
        FinProb.map ((D.tagLawAll Θ').prod D.actLaw)
          (fun x => (localTagsProj D c x.1, localActsProj D c x.2)) := by
    rw [Lane_q_s08_post.map_prod, Lane_q_s08_post.map_prod, htag]
  unfold Ctx.rawTAT
  calc
    FinProb.map (((D.tagLawAll Θ).prod D.actLaw).prod D.tieLaw) (localTATProj D c) =
        (FinProb.map ((D.tagLawAll Θ).prod D.actLaw)
          (fun x => (localTagsProj D c x.1, localActsProj D c x.2))).prod
        (FinProb.map D.tieLaw (localTiesProj D c)) := by
              exact Lane_q_s08_post.map_prod
                ((D.tagLawAll Θ).prod D.actLaw) D.tieLaw
                (fun x => (localTagsProj D c x.1, localActsProj D c x.2))
                (localTiesProj D c)
    _ =
        (FinProb.map ((D.tagLawAll Θ').prod D.actLaw)
          (fun x => (localTagsProj D c x.1, localActsProj D c x.2))).prod
            (FinProb.map D.tieLaw (localTiesProj D c)) := by rw [hta]
    _ = FinProb.map (((D.tagLawAll Θ').prod D.actLaw).prod D.tieLaw)
          (localTATProj D c) := by
            symm
            exact Lane_q_s08_post.map_prod
              ((D.tagLawAll Θ').prod D.actLaw) D.tieLaw
              (fun x => (localTagsProj D c x.1, localActsProj D c x.2))
              (localTiesProj D c)

set_option maxHeartbeats 1000000 in
theorem rawAnchors_cross_projection_congr {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hS : D.SelLocal) (H H' : D.Hist)
    (P P' : D.Pos) (c : D.CellT) (ω ω' : D.TAT)
    (hH : ∀ g, keyDist c.1 g ≤ 4 → H g = H' g)
    (hP : ∀ g, keyDist c.1 g ≤ 3 → P g = P' g)
    (hT : localTATProj D c ω = localTATProj D c ω') :
    FinProb.map (D.rawAnchors ((H, P), ω)) (localAnchorsProj D c) =
      FinProb.map (D.rawAnchors ((H', P'), ω')) (localAnchorsProj D c) := by
  classical
  have hTag (g : D.KeyT) (hg : keyDist c.1 g ≤ 3) : ω.1.1 g = ω'.1.1 g := by
    have hfun := congrArg (fun z : LocalTATSample D c => z.1.1) hT
    have hmem : g ∈ keyBall c.1 3 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ g, hg⟩
    exact congrFun hfun ⟨g, hmem⟩
  have hAct (g : D.KeyT) (hg : keyDist c.1 g ≤ 1) : ω.1.2 g = ω'.1.2 g := by
    have hfun := congrArg (fun z : LocalTATSample D c => z.1.2) hT
    have hmem : g ∈ keyBall c.1 1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ g, hg⟩
    exact congrFun hfun ⟨g, hmem⟩
  have hTie (g : D.KeyT) (hg : keyDist c.1 g ≤ 1) : ω.2 g = ω'.2 g := by
    have hfun := congrArg (fun z : LocalTATSample D c => z.2) hT
    have hmem : g ∈ keyBall c.1 1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ g, hg⟩
    exact congrFun hfun ⟨g, hmem⟩
  have hCoord (e : D.CellT) (he : e ∈ crossCellSet D c) :
      D.Usel ((H, P), ω) e = D.Usel ((H', P'), ω') e := by
    rcases Finset.mem_image.mp he with ⟨u, hu, hcell⟩
    have hcu : keyDist c.1 u.1 = 1 := (Finset.mem_filter.mp u.2).2
    subst e
    have hsel : D.sel ((H, P), ω) (u.1, c.2) =
        D.sel ((H', P'), ω') (u.1, c.2) := by
      apply hS
      · intro g hg
        have htri := keyDist_triangle_aux c.1 u.1 g
        have hgu : keyDist u.1 g ≤ 3 := (Finset.mem_filter.mp hg).2
        have hcg : keyDist c.1 g ≤ 4 := by omega
        exact hH g hcg
      · intro g hg ℓ hℓ
        have htri := keyDist_triangle_aux c.1 u.1 g
        have hgu : keyDist u.1 g ≤ 2 := (Finset.mem_filter.mp hg).2
        have hcg : keyDist c.1 g ≤ 3 := by omega
        exact ⟨congrFun (hP g hcg) ℓ, congrFun (hTag g hcg) ℓ⟩
      · intro ℓ hℓ
        have hkey : keyDist c.1 u.1 ≤ 1 := by simpa [hcu]
        exact ⟨congrFun (hAct u.1 hkey) ℓ, congrFun (hTie u.1 hkey) ℓ⟩
    have hselTag : D.selTag ((H, P), ω) (u.1, c.2) =
        D.selTag ((H', P'), ω') (u.1, c.2) := by
      unfold Ctx.selTag
      rw [hsel, hTag u.1 (by simpa [hcu])]
    have hu0 : H u.1 = H' u.1 := hH u.1 (by simpa [hcu])
    have hcross : ∀ v ∈ crossKeys u.1, H v = H' v := by
      intro v hv
      have htri := keyDist_triangle_aux c.1 u.1 v
      have huv : keyDist u.1 v = 1 := (Finset.mem_filter.mp hv).2
      have hcv : keyDist c.1 v ≤ 4 := by omega
      exact hH v hcv
    unfold Ctx.Usel
    rw [← hselTag]
    cases hs : D.selTag ((H, P), ω) (u.1, c.2) with
    | none => rfl
    | some i => exact Lane_q_s08_post.anchorU_congr_of_local D H H' u.1 i hu0 hcross
  change FinProb.map (FinProb.pi (fun e : D.CellT => D.Usel ((H, P), ω) e))
      (fun W (e : {e : D.CellT // e ∈ crossCellSet D c}) => W e.1) =
    FinProb.map (FinProb.pi (fun e : D.CellT => D.Usel ((H', P'), ω') e))
      (fun W (e : {e : D.CellT // e ∈ crossCellSet D c}) => W e.1)
  exact Lane_q_s08_post.map_pi_restrict_congr
    (fun e : D.CellT => D.Usel ((H, P), ω) e)
    (fun e : D.CellT => D.Usel ((H', P'), ω') e)
    (crossCellSet D c) hCoord

theorem fcand_congr_radius_two {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT) (ξ : D.Tup)
    {J : Type} [Fintype J] (o : D.Obs J g)
    (hΘ : ∀ v, keyDist g v ≤ 2 → Θ v = Θ' v) :
    D.Fcand Θ g ξ o = D.Fcand Θ' g ξ o := by
  classical
  have hBall (v : D.KeyT) (hv : keyDist g v ≤ 2) : v ∈ keyBall g 2 := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ v, hv⟩
  have hUpdate (v : D.KeyT) (hv : keyDist g v ≤ 2) :
      Function.update Θ g ξ v = Function.update Θ' g ξ v := by
    by_cases hvg : v = g
    · subst v
      simp
    · simp [Function.update_of_ne hvg, hΘ v hv]
  have hUpdateBall : ∀ v ∈ keyBall g 2,
      Function.update Θ g ξ v = Function.update Θ' g ξ v := by
    intro v hv
    exact hUpdate v (Finset.mem_filter.mp hv).2
  have hCand := Lane_q_s08_post.candGate_congr_of_radius_two D
    (Function.update Θ g ξ) (Function.update Θ' g ξ) g hUpdateBall
  have hThetaCross : ∀ u ∈ crossKeys g, Θ u = Θ' u := by
    intro u hu
    exact hΘ u ((Finset.mem_filter.mp hu).2.le.trans (by omega))
  have hIntLaw := Lane_q_s08_post.tilt_congr_of_local D
    (Function.update Θ g ξ) (Function.update Θ' g ξ) g (by simp)
    (by
      intro u hu
      exact hUpdate u ((Finset.mem_filter.mp hu).2.le.trans (by omega)))
  have hIntRef := Lane_q_s08_post.refInt_congr_of_local D Θ Θ' g hThetaCross
  have hIntRatio (j : J) :
      D.intRatio Θ g ξ (o.1 j) = D.intRatio Θ' g ξ (o.1 j) := by
    unfold Ctx.intRatio
    rw [hIntLaw, hIntRef]
  have hCrossRatio (u : D.CrossSub g) :
      D.crossRatio Θ g ξ u (o.2 u) = D.crossRatio Θ' g ξ u (o.2 u) := by
    have huDist : keyDist g u.1 ≤ 1 := (Finset.mem_filter.mp u.2).2.le
    have h0 := hUpdate u.1 (huDist.trans (by omega))
    have hCross : ∀ w ∈ crossKeys u.1,
        Function.update Θ g ξ w = Function.update Θ' g ξ w := by
      intro w hw
      have htri := keyDist_triangle_aux g u.1 w
      have hgw : keyDist g w ≤ 2 := by
        have huw : keyDist u.1 w = 1 := (Finset.mem_filter.mp hw).2
        omega
      exact hUpdate w hgw
    have hTilt := Lane_q_s08_post.tilt_congr_of_local D
      (Function.update Θ g ξ) (Function.update Θ' g ξ) u.1 h0 hCross
    have hAnchor := Lane_q_s08_post.anchorU_congr_of_local D
      (Function.update Θ g ξ) (Function.update Θ' g ξ) u.1 (o.2 u).1 h0 hCross
    have hRef := Lane_q_s08_post.refCross_congr_radius_two D Θ Θ' g u
      (fun w hw => hΘ w (Finset.mem_filter.mp hw).2)
    unfold Ctx.crossRatio
    rw [hTilt, hAnchor, hRef]
  unfold Ctx.Fcand
  rw [hCand]
  have hIprod : (∏ j, D.intRatio Θ g ξ (o.1 j)) =
      ∏ j, D.intRatio Θ' g ξ (o.1 j) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact hIntRatio j
  have hCprod : (∏ u, D.crossRatio Θ g ξ u (o.2 u)) =
      ∏ u, D.crossRatio Θ' g ξ u (o.2 u) := by
    apply Finset.prod_congr rfl
    intro u hu
    exact hCrossRatio u
  rw [hIprod, hCprod]

theorem fcand_congr_target_update {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT) (ξ : D.Tup)
    {J : Type} [Fintype J] (o : D.Obs J g)
    (hAway : ∀ v, v ≠ g → Θ v = Θ' v) :
    D.Fcand Θ g ξ o = D.Fcand Θ' g ξ o := by
  classical
  have hUpd : Function.update Θ g ξ = Function.update Θ' g ξ := by
    funext v
    by_cases hvg : v = g
    · subst v
      simp
    · simp [Function.update_of_ne hvg, hAway v hvg]
  have hRefInt := Lane_q_s08_post.refInt_congr_off_target D Θ Θ' g hAway
  have hRefCross (u : D.CrossSub g) :
      D.refCross Θ g u.1 = D.refCross Θ' g u.1 :=
    Lane_q_s08_post.refCross_congr_off_target D Θ Θ' g u hAway
  have hCand : D.CandGate (Function.update Θ g ξ) g =
      D.CandGate (Function.update Θ' g ξ) g := by rw [hUpd]
  have hInt (j : J) : D.intRatio Θ g ξ (o.1 j) = D.intRatio Θ' g ξ (o.1 j) := by
    unfold Ctx.intRatio
    rw [hUpd, hRefInt]
  have hCross (u : D.CrossSub g) :
      D.crossRatio Θ g ξ u (o.2 u) = D.crossRatio Θ' g ξ u (o.2 u) := by
    unfold Ctx.crossRatio
    rw [hUpd, hRefCross u]
  unfold Ctx.Fcand
  rw [hCand]
  have hIprod : (∏ j, D.intRatio Θ g ξ (o.1 j)) =
      ∏ j, D.intRatio Θ' g ξ (o.1 j) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact hInt j
  have hCprod : (∏ u, D.crossRatio Θ g ξ u (o.2 u)) =
      ∏ u, D.crossRatio Θ' g ξ u (o.2 u) := by
    apply Finset.prod_congr rfl
    intro u hu
    exact hCross u
  rw [hIprod, hCprod]

theorem mden_congr_target_update {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT)
    {J : Type} [Fintype J] (o : D.Obs J g)
    (hAway : ∀ v, v ≠ g → Θ v = Θ' v) :
    D.Mden Θ g o = D.Mden Θ' g o := by
  classical
  unfold Ctx.Mden
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [Lane_q_s08_post.fcand_congr_target_update D Θ Θ' g ξ o hAway]

theorem qref_congr_off_target {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT)
    {J : Type} [Fintype J] (o : D.Obs J g)
    (hAway : ∀ v, v ≠ g → Θ v = Θ' v) :
    D.Qref Θ g o = D.Qref Θ' g o := by
  classical
  have hInt := Lane_q_s08_post.refInt_congr_off_target D Θ Θ' g hAway
  have hCross (u : D.CrossSub g) :
      D.refCross Θ g u.1 = D.refCross Θ' g u.1 :=
    Lane_q_s08_post.refCross_congr_off_target D Θ Θ' g u hAway
  unfold Ctx.Qref
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    cases ho : o.1 j with
    | none => rfl
    | some i => exact congrArg (fun R : FinProb D.M.ι => R.w i) hInt
  · apply Finset.prod_congr rfl
    intro u hu
    exact congrArg (fun R : FinProb (D.M.ι × Fin D.N) => R.w (o.2 u)) (hCross u)

theorem normOr_congr {α : Type*} [Fintype α]
    (f g : α → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (P Q : FinProb α) (hPQ : ∀ x, P.w x = Q.w x) (hfg : ∀ x, f x = g x) :
    normOr f hf P = normOr g hg Q := by
  classical
  have hsum : (∑ x, f x) = ∑ x, g x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hfg x
  apply FinProb.ext
  intro x
  by_cases hz : (∑ x, f x) = 0
  · have hz' : (∑ x, g x) = 0 := by rw [← hsum]; exact hz
    simp [normOr, hz, hz', hPQ x]
  · have hz' : (∑ x, g x) ≠ 0 := by
      intro hzero
      apply hz
      rw [hsum]
      exact hzero
    simp [normOr, hz, hz', hfg x, hsum]

theorem gsel_congr_target_update {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (c : D.CellT)
    (P : D.Pos) (ξ : D.Tup) (π : D.Pres c.1)
    (hAway : ∀ v, v ≠ c.1 → Θ v = Θ' v) :
    D.Gsel Θ P c ξ π = D.Gsel Θ' P c ξ π := by
  have hUpd : Function.update Θ c.1 ξ = Function.update Θ' c.1 ξ := by
    funext v
    by_cases hvg : v = c.1
    · subst v
      simp
    · simp [Function.update_of_ne hvg, hAway v hvg]
  have hQ := Lane_q_s08_post.qref_congr_off_target D Θ Θ' c.1 (D.obsOf π) hAway
  unfold Ctx.Gsel
  rw [hUpd, hQ]

set_option maxHeartbeats 1000000 in
theorem selPost_congr_target_update {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (P : D.Pos) (c : D.CellT)
    (π : D.Pres c.1) (hAway : ∀ v, v ≠ c.1 → Θ v = Θ' v) :
    D.selPost Θ P c π = D.selPost Θ' P c π := by
  classical
  have hGsel (ξ : D.Tup) : D.Gsel Θ P c ξ π = D.Gsel Θ' P c ξ π :=
    Lane_q_s08_post.gsel_congr_target_update D Θ Θ' c P ξ π hAway
  have hMad : D.Mad Θ P c π = D.Mad Θ' P c π := by
    unfold Ctx.Mad
    apply Finset.sum_congr rfl
    intro ξ hξ
    exact congrArg (fun x : ℝ => D.R'.w ξ * x) (hGsel ξ)
  have hDen := Lane_q_s08_post.mden_congr_target_update D Θ Θ' c.1
    (D.obsOf π) hAway
  have hFcand (ξ : D.Tup) :
      D.Fcand Θ c.1 ξ (D.obsOf π) = D.Fcand Θ' c.1 ξ (D.obsOf π) :=
    Lane_q_s08_post.fcand_congr_target_update D Θ Θ' c.1 ξ (D.obsOf π) hAway
  have hBase : D.basePost Θ c.1 (D.obsOf π) = D.basePost Θ' c.1 (D.obsOf π) := by
    unfold Ctx.basePost
    exact Lane_q_s08_post.normOr_congr
      (f := fun ξ => D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π))
      (g := fun ξ => D.R'.w ξ * D.Fcand Θ' c.1 ξ (D.obsOf π))
      (hf := fun ξ => mul_nonneg (D.R'.nonneg ξ) (D.Fcand_nonneg Θ c.1 ξ (D.obsOf π)))
      (hg := fun ξ => mul_nonneg (D.R'.nonneg ξ) (D.Fcand_nonneg Θ' c.1 ξ (D.obsOf π)))
      (P := D.R') (Q := D.R') (hPQ := fun ξ => rfl)
      (hfg := fun ξ => congrArg (fun x : ℝ => D.R'.w ξ * x) (hFcand ξ))
  have hSelected :
      normOr (fun ξ => D.R'.w ξ * D.Gsel Θ P c ξ π)
          (fun ξ => mul_nonneg (D.R'.nonneg ξ) (D.Gsel_nonneg Θ P c ξ π))
          (D.basePost Θ' c.1 (D.obsOf π)) =
        normOr (fun ξ => D.R'.w ξ * D.Gsel Θ' P c ξ π)
          (fun ξ => mul_nonneg (D.R'.nonneg ξ) (D.Gsel_nonneg Θ' P c ξ π))
          (D.basePost Θ' c.1 (D.obsOf π)) := by
    exact Lane_q_s08_post.normOr_congr
      (f := fun ξ => D.R'.w ξ * D.Gsel Θ P c ξ π)
      (g := fun ξ => D.R'.w ξ * D.Gsel Θ' P c ξ π)
      (hf := fun ξ => mul_nonneg (D.R'.nonneg ξ) (D.Gsel_nonneg Θ P c ξ π))
      (hg := fun ξ => mul_nonneg (D.R'.nonneg ξ) (D.Gsel_nonneg Θ' P c ξ π))
      (P := D.basePost Θ' c.1 (D.obsOf π)) (Q := D.basePost Θ' c.1 (D.obsOf π))
      (hPQ := fun ξ => rfl)
      (hfg := fun ξ => congrArg (fun x : ℝ => D.R'.w ξ * x) (hGsel ξ))
  have hcond :
      (D.eps0 * D.Mden Θ c.1 (D.obsOf π) ≤ D.Mad Θ P c π) =
        (D.eps0 * D.Mden Θ' c.1 (D.obsOf π) ≤ D.Mad Θ' P c π) := by
    rw [hDen, hMad]
  unfold Ctx.selPost
  simp only [hcond, hBase, hSelected]

theorem p0w_congr_target_update {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) (P : D.Pos) (c : D.CellT)
    (ξ : D.Tup) (π : D.Pres c.1) (y : Fin D.N) :
    D.p0w Θ P c π y = D.p0w (Function.update Θ c.1 ξ) P c π y := by
  have hPost := Lane_q_s08_post.selPost_congr_target_update D Θ
    (Function.update Θ c.1 ξ) P c π (by
      intro v hv
      simpa [Function.update_of_ne hv])
  unfold Ctx.p0w
  rw [hPost]

theorem mden_congr_radius_two {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT)
    {J : Type} [Fintype J] (o : D.Obs J g)
    (hΘ : ∀ v, keyDist g v ≤ 2 → Θ v = Θ' v) :
    D.Mden Θ g o = D.Mden Θ' g o := by
  classical
  unfold Ctx.Mden
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [Lane_q_s08_post.fcand_congr_radius_two D Θ Θ' g ξ o hΘ]

theorem qref_congr_radius_two {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ Θ' : D.Hist) (g : D.KeyT)
    {J : Type} [Fintype J] (o : D.Obs J g)
    (hΘ : ∀ v, keyDist g v ≤ 2 → Θ v = Θ' v) :
    D.Qref Θ g o = D.Qref Θ' g o := by
  classical
  have hcross : ∀ u ∈ crossKeys g, Θ u = Θ' u := by
    intro u hu
    have huDist : keyDist g u ≤ 1 := (Finset.mem_filter.mp hu).2.le
    exact hΘ u (huDist.trans (by omega))
  have hInt := Lane_q_s08_post.refInt_congr_of_local D Θ Θ' g hcross
  have hCross (u : D.CrossSub g) :
      D.refCross Θ g u.1 = D.refCross Θ' g u.1 :=
    Lane_q_s08_post.refCross_congr_radius_two D Θ Θ' g u
      (fun v hv => hΘ v (Finset.mem_filter.mp hv).2)
  unfold Ctx.Qref
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    cases ho : o.1 j with
    | none => rfl
    | some i => exact congrArg (fun R : FinProb D.M.ι => R.w i) hInt
  · apply Finset.prod_congr rfl
    intro u hu
    exact congrArg (fun R : FinProb (D.M.ι × Fin D.N) => R.w (o.2 u)) (hCross u)

set_option maxHeartbeats 1000000 in
theorem presentation_event_congr_local {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hS : D.SelLocal) (H H' : D.Hist)
    (P P' : D.Pos) (c : D.CellT) (ω ω' : D.TAT) (W W' : D.Anch)
    (π : D.Pres c.1)
    (hH : ∀ g, keyDist c.1 g ≤ 4 → H g = H' g)
    (hP : ∀ g, keyDist c.1 g ≤ 3 → P g = P' g)
    (hT : localTATProj D c ω = localTATProj D c ω')
    (hA : localAnchorsProj D c W = localAnchorsProj D c W') :
    (D.PresValid ((H, P), ω) W c ∧
        D.presOf ((H, P), ω) W c = π) ↔
      (D.PresValid ((H', P'), ω') W' c ∧
        D.presOf ((H', P'), ω') W' c = π) := by
  classical
  have hTag (g : D.KeyT) (hg : keyDist c.1 g ≤ 3) : ω.1.1 g = ω'.1.1 g := by
    have hfun := congrArg (fun z : LocalTATSample D c => z.1.1) hT
    have hmem : g ∈ keyBall c.1 3 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ g, hg⟩
    exact congrFun hfun ⟨g, hmem⟩
  have hAct (g : D.KeyT) (hg : keyDist c.1 g ≤ 1) : ω.1.2 g = ω'.1.2 g := by
    have hfun := congrArg (fun z : LocalTATSample D c => z.1.2) hT
    have hmem : g ∈ keyBall c.1 1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ g, hg⟩
    exact congrFun hfun ⟨g, hmem⟩
  have hTie (g : D.KeyT) (hg : keyDist c.1 g ≤ 1) : ω.2 g = ω'.2 g := by
    have hfun := congrArg (fun z : LocalTATSample D c => z.2) hT
    have hmem : g ∈ keyBall c.1 1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ g, hg⟩
    exact congrFun hfun ⟨g, hmem⟩
  have hSelEq (e : D.CellT) (he : keyDist c.1 e.1 ≤ 1) :
      D.sel ((H, P), ω) e = D.sel ((H', P'), ω') e := by
    apply hS
    · intro g hg
      have htri := keyDist_triangle_aux c.1 e.1 g
      have heg : keyDist e.1 g ≤ 3 := (Finset.mem_filter.mp hg).2
      have hcg : keyDist c.1 g ≤ 4 := by omega
      exact hH g hcg
    · intro g hg ℓ hℓ
      have htri := keyDist_triangle_aux c.1 e.1 g
      have heg : keyDist e.1 g ≤ 2 := (Finset.mem_filter.mp hg).2
      have hcg : keyDist c.1 g ≤ 3 := by omega
      exact ⟨congrFun (hP g hcg) ℓ, congrFun (hTag g hcg) ℓ⟩
    · intro ℓ hℓ
      exact ⟨congrFun (hAct e.1 he) ℓ, congrFun (hTie e.1 he) ℓ⟩
  have hOrdSel (b : D.ResT) (hb : b ∈ ordNbrs c.2) :
      D.sel ((H, P), ω) (c.1, b) = D.sel ((H', P'), ω') (c.1, b) := by
    apply hSelEq
    simp [keyDist]
  have hCrossSel (u : D.CrossSub c.1) :
      D.sel ((H, P), ω) (u.1, c.2) = D.sel ((H', P'), ω') (u.1, c.2) := by
    apply hSelEq
    exact (Finset.mem_filter.mp u.2).2.le
  have hIntIds : D.intIds ((H, P), ω) c = D.intIds ((H', P'), ω') c := by
    unfold Ctx.intIds
    ext ℓ
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨b, hb, hℓ⟩
      refine ⟨b, hb, ?_⟩
      rw [hOrdSel b hb] at hℓ
      exact hℓ
    · rintro ⟨b, hb, hℓ⟩
      refine ⟨b, hb, ?_⟩
      rw [← hOrdSel b hb] at hℓ
      exact hℓ
  have hCrossId (u : D.CrossSub c.1) :
      D.crossId ((H, P), ω) c u = D.crossId ((H', P'), ω') c u := by
    unfold Ctx.crossId
    rw [hCrossSel u]
  have hAnchor (u : D.CrossSub c.1) :
      W (u.1, c.2) = W' (u.1, c.2) := by
    have he : (u.1, c.2) ∈ crossCellSet D c :=
      Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
    exact congrFun hA ⟨(u.1, c.2), he⟩
  have hPres : D.presOf ((H, P), ω) W c = D.presOf ((H', P'), ω') W' c := by
    apply Prod.ext
    · funext ℓ
      simp only [Ctx.presOf]
      by_cases hℓ : ℓ ∈ D.intIds ((H, P), ω) c
      · have hℓ' : ℓ ∈ D.intIds ((H', P'), ω') c := by rw [← hIntIds]; exact hℓ
        have hc : keyDist c.1 c.1 ≤ 3 := by simp [keyDist]
        simp [hℓ, hℓ', congrFun (hTag c.1 hc) ℓ]
      · have hℓ' : ℓ ∉ D.intIds ((H', P'), ω') c := by rw [← hIntIds]; exact hℓ
        simp [hℓ, hℓ']
    · funext u
      simp only [Ctx.presOf]
      have hu3 : keyDist c.1 u.1 ≤ 3 := by
        have hu1 : keyDist c.1 u.1 = 1 := (Finset.mem_filter.mp u.2).2
        omega
      change (D.crossId ((H, P), ω) c u,
          ω.1.1 u.1 (D.crossId ((H, P), ω) c u), W (u.1, c.2)) =
        (D.crossId ((H', P'), ω') c u,
          ω'.1.1 u.1 (D.crossId ((H', P'), ω') c u), W' (u.1, c.2))
      rw [hCrossId u, congrFun (hTag u.1 hu3) (D.crossId ((H', P'), ω') c u), hAnchor u]
  have hHidden2 : ∀ g ∈ keyBall c.1 2, H g = H' g := by
    intro g hg
    have hd := (Finset.mem_filter.mp hg).2
    exact hH g (hd.trans (by omega))
  have hHist2 : ∀ g, keyDist c.1 g ≤ 2 → H g = H' g := by
    intro g hg
    have hmem : g ∈ keyBall c.1 2 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ g, hg⟩
    exact hHidden2 g hmem
  have hCandGate :=
    Lane_q_s08_post.candGate_congr_of_radius_two D H H' c.1 hHidden2
  have hPadKey3 (e : D.CellT) (he : PadNbr c e) : e.1 ∈ keyBall c.1 3 := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ e.1
    · rcases he with ⟨hek, hOrd⟩ | ⟨hres, hCross⟩
      · rw [hek]
        simp [keyDist]
      · have hdist := (Finset.mem_filter.mp hCross).2
        exact hdist.le.trans (by omega)
  have hPosCount :
      D.PosCountOK P c = D.PosCountOK P' c := by
    apply propext
    constructor <;> intro hh e he j
    · have hp := hP e.1 ((Finset.mem_filter.mp (hPadKey3 e he)).2)
      have hcount : D.ballCount P' e.1 e.2 j = D.ballCount P e.1 e.2 j := by
        unfold Ctx.ballCount
        rw [hp]
      rw [hcount]
      exact hh e he j
    · have hp := hP e.1 ((Finset.mem_filter.mp (hPadKey3 e he)).2)
      have hcount : D.ballCount P e.1 e.2 j = D.ballCount P' e.1 e.2 j := by
        unfold Ctx.ballCount
        rw [hp]
      rw [hcount]
      exact hh e he j
  have hObs : D.obsOf (D.presOf ((H, P), ω) W c) =
      D.obsOf (D.presOf ((H', P'), ω') W' c) := congrArg D.obsOf hPres
  have hMden :
      D.Mden H c.1 (D.obsOf (D.presOf ((H, P), ω) W c)) =
        D.Mden H' c.1 (D.obsOf (D.presOf ((H', P'), ω') W' c)) := by
    rw [hObs]
    exact Lane_q_s08_post.mden_congr_radius_two D H H' c.1
      (D.obsOf (D.presOf ((H', P'), ω') W' c)) hHist2
  have hOrdValid :
      (∀ b ∈ ordNbrs c.2, (D.sel ((H, P), ω) (c.1, b)).isSome) ↔
        (∀ b ∈ ordNbrs c.2, (D.sel ((H', P'), ω') (c.1, b)).isSome) := by
    constructor
    · intro hh b hb
      rw [← hOrdSel b hb]
      exact hh b hb
    · intro hh b hb
      rw [hOrdSel b hb]
      exact hh b hb
  have hCrossValid :
      (∀ u : D.CrossSub c.1, (D.sel ((H, P), ω) (u.1, c.2)).isSome) ↔
        (∀ u : D.CrossSub c.1, (D.sel ((H', P'), ω') (u.1, c.2)).isSome) := by
    constructor
    · intro hh u
      rw [← hCrossSel u]
      exact hh u
    · intro hh u
      rw [hCrossSel u]
      exact hh u
  have hValidEq : D.PresValid ((H, P), ω) W c = D.PresValid ((H', P'), ω') W' c := by
    apply propext
    unfold Ctx.PresValid
    rw [hCandGate, hOrdValid, hCrossValid, hIntIds, hPosCount, hMden]
  rw [hValidEq, hPres]

def rawPresEvent {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (H : D.Hist) (P : D.Pos) (c : D.CellT)
    (π : D.Pres c.1) (z : D.TAT × D.Anch) : Prop :=
  D.PresValid ((H, P), z.1) z.2 c ∧ D.presOf ((H, P), z.1) z.2 c = π

def localPresEvent {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (H : D.Hist) (P : D.Pos) (c : D.CellT)
    (π : D.Pres c.1) (baseT : D.TAT) (baseW : D.Anch)
    (t : LocalTATSample D c) (a : LocalAnchorSample D c) : Prop :=
  D.PresValid ((H, P), completeLocalTAT D c baseT t)
      (completeLocalAnchors D c baseW a) c ∧
    D.presOf ((H, P), completeLocalTAT D c baseT t)
      (completeLocalAnchors D c baseW a) c = π

theorem rawPresEvent_iff_local {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hS : D.SelLocal) (H : D.Hist) (P : D.Pos)
    (c : D.CellT) (π : D.Pres c.1) (baseT : D.TAT) (baseW : D.Anch)
    (ω : D.TAT) (W : D.Anch) :
    rawPresEvent D H P c π (ω, W) ↔
      localPresEvent D H P c π baseT baseW
        (localTATProj D c ω) (localAnchorsProj D c W) := by
  have hT : localTATProj D c ω =
      localTATProj D c (completeLocalTAT D c baseT (localTATProj D c ω)) :=
    (localTATProj_completeLocalTAT D c baseT (localTATProj D c ω)).symm
  have hA : localAnchorsProj D c W =
      localAnchorsProj D c
        (completeLocalAnchors D c baseW (localAnchorsProj D c W)) :=
    (localAnchorsProj_completeLocalAnchors D c baseW (localAnchorsProj D c W)).symm
  simpa [rawPresEvent, localPresEvent] using
    (presentation_event_congr_local D hS H H P P c ω
      (completeLocalTAT D c baseT (localTATProj D c ω)) W
      (completeLocalAnchors D c baseW (localAnchorsProj D c W)) π
      (by intro g hg; rfl) (by intro g hg; rfl) hT hA)

private theorem pr_congr_local {α : Type*} [Fintype α]
    (Q : FinProb α) (A B : α → Prop)
    (hAB : ∀ x, A x ↔ B x) : Q.pr A = Q.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro x hx
  simp [hAB x]

theorem expect_group_by_fiber {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ] [DecidableEq Ψ]
    (Q : FinProb Ω) (f : Ω → Ψ) (V : Ω → Prop) (w : Ψ → ℝ) :
    Q.expect (fun x => if V x then w (f x) else 0) =
      ∑ y, w y * Q.pr (fun x => V x ∧ f x = y) := by
  classical
  unfold FinProb.expect FinProb.pr
  have hterm (x : Ω) :
    Q.w x * (if V x then w (f x) else 0) =
        ∑ y, w y * (if V x ∧ f x = y then Q.w x else 0) := by
    by_cases hV : V x
    · simp only [hV, if_true, true_and]
      calc
        Q.w x * w (f x) =
            ∑ y, (if f x = y then Q.w x * w y else 0) := by simp
        _ = ∑ y, w y * (if f x = y then Q.w x else 0) := by
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hyx : f x = y <;> simp [hyx, mul_comm]
    · simp [hV]
  calc
    (∑ x, Q.w x * (if V x then w (f x) else 0)) =
        ∑ x, ∑ y, w y * (if V x ∧ f x = y then Q.w x else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hterm x
    _ = ∑ y, w y * ∑ x, if V x ∧ f x = y then Q.w x else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
    _ = ∑ y, w y * Q.pr (fun x => V x ∧ f x = y) := by
      apply Finset.sum_congr rfl
      intro y hy
      apply congrArg (fun r : ℝ => w y * r)
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro x hx
      exact PToolsMisc.ite_decidable_irrel (V x ∧ f x = y)
        (inferInstance : Decidable (V x ∧ f x = y))
        (Classical.propDecidable (V x ∧ f x = y)) _ _

set_option maxHeartbeats 3000000 in
theorem rawLaw_pr_local_expect {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hS : D.SelLocal) (H : D.Hist) (P : D.Pos)
    (c : D.CellT) (π : D.Pres c.1) (baseT : D.TAT) (baseW : D.Anch) :
    (D.rawLaw H P).pr (rawPresEvent D H P c π) =
      (FinProb.map (D.rawTAT H) (localTATProj D c)).expect
        (fun t =>
          (FinProb.map
              (D.rawAnchors ((H, P), completeLocalTAT D c baseT t))
              (localAnchorsProj D c)).pr
            (fun a => localPresEvent D H P c π baseT baseW t a)) := by
  classical
  let f : LocalTATSample D c → ℝ := fun t =>
    (FinProb.map
        (D.rawAnchors ((H, P), completeLocalTAT D c baseT t))
        (localAnchorsProj D c)).pr
      (fun a => localPresEvent D H P c π baseT baseW t a)
  change (D.rawLaw H P).pr (rawPresEvent D H P c π) =
    (FinProb.map (D.rawTAT H) (localTATProj D c)).expect f
  rw [Ctx.rawLaw, Lane_q_s08_post.bind_pr_eq_sum]
  calc
    (∑ ω, (D.rawTAT H).w ω *
        (D.rawAnchors ((H, P), ω)).pr (fun W => rawPresEvent D H P c π (ω, W))) =
      ∑ ω, (D.rawTAT H).w ω * f (localTATProj D c ω) := by
      apply Finset.sum_congr rfl
      intro ω hω
      congr 1
      let t := localTATProj D c ω
      let ω₀ := completeLocalTAT D c baseT t
      have hT : localTATProj D c ω = localTATProj D c ω₀ := by
        dsimp [t, ω₀]
        exact (localTATProj_completeLocalTAT D c baseT (localTATProj D c ω)).symm
      have hLaw :
          FinProb.map (D.rawAnchors ((H, P), ω)) (localAnchorsProj D c) =
            FinProb.map (D.rawAnchors ((H, P), ω₀)) (localAnchorsProj D c) :=
        rawAnchors_cross_projection_congr D hS H H P P c ω ω₀
          (by intro g hg; rfl) (by intro g hg; rfl) hT
      have hEvent := rawPresEvent_iff_local D hS H P c π baseT baseW ω
      calc
        (D.rawAnchors ((H, P), ω)).pr
            (fun W => rawPresEvent D H P c π (ω, W)) =
          (D.rawAnchors ((H, P), ω)).pr
            (fun W => localPresEvent D H P c π baseT baseW
              (localTATProj D c ω) (localAnchorsProj D c W)) :=
                pr_congr_local _ _ _ hEvent
        _ = f (localTATProj D c ω) := by
          rw [(FinProb.map_pr _ _ _).symm]
          dsimp [f]
          rw [hLaw]
    _ = (FinProb.map (D.rawTAT H) (localTATProj D c)).expect f := by
      symm
      exact FinProb.map_expect (D.rawTAT H) (localTATProj D c) f

set_option maxHeartbeats 1000000 in
theorem rawLaw_pr_congr_local {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hS : D.SelLocal) (H H' : D.Hist)
    (P P' : D.Pos) (c : D.CellT) (π : D.Pres c.1)
    (baseT : D.TAT) (baseW : D.Anch)
    (hH : ∀ g, keyDist c.1 g ≤ 4 → H g = H' g)
    (hP : ∀ g, keyDist c.1 g ≤ 3 → P g = P' g) :
    (D.rawLaw H P).pr (rawPresEvent D H P c π) =
      (D.rawLaw H' P').pr (rawPresEvent D H' P' c π) := by
  classical
  rw [rawLaw_pr_local_expect D hS H P c π baseT baseW,
    rawLaw_pr_local_expect D hS H' P' c π baseT baseW]
  have hProj := rawTAT_local_projection_congr D H H' c hH
  simp only [hProj]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro t ht
  have hAt (t : LocalTATSample D c) :
      (FinProb.map
        (D.rawAnchors ((H, P), completeLocalTAT D c baseT t))
        (localAnchorsProj D c)).pr
          (fun a => localPresEvent D H P c π baseT baseW t a) =
      (FinProb.map
        (D.rawAnchors ((H', P'), completeLocalTAT D c baseT t))
        (localAnchorsProj D c)).pr
          (fun a => localPresEvent D H' P' c π baseT baseW t a) := by
    let ω₀ := completeLocalTAT D c baseT t
    have hAnchorLaw :
        FinProb.map (D.rawAnchors ((H, P), ω₀)) (localAnchorsProj D c) =
          FinProb.map (D.rawAnchors ((H', P'), ω₀)) (localAnchorsProj D c) :=
      rawAnchors_cross_projection_congr D hS H H' P P' c ω₀ ω₀ hH hP rfl
    have hEvt (a : LocalAnchorSample D c) :
        localPresEvent D H P c π baseT baseW t a ↔
          localPresEvent D H' P' c π baseT baseW t a := by
      have h := presentation_event_congr_local D hS H H' P P' c ω₀ ω₀
        (completeLocalAnchors D c baseW a) (completeLocalAnchors D c baseW a) π hH hP rfl rfl
      simpa [localPresEvent] using h
    calc
      (FinProb.map (D.rawAnchors ((H, P), ω₀)) (localAnchorsProj D c)).pr
          (fun a => localPresEvent D H P c π baseT baseW t a) =
        (FinProb.map (D.rawAnchors ((H, P), ω₀)) (localAnchorsProj D c)).pr
          (fun a => localPresEvent D H' P' c π baseT baseW t a) :=
            pr_congr_local _ _ _ hEvt
      _ = (FinProb.map (D.rawAnchors ((H', P'), ω₀)) (localAnchorsProj D c)).pr
          (fun a => localPresEvent D H' P' c π baseT baseW t a) := by rw [hAnchorLaw]
  dsimp
  exact congrArg
    (fun x : ℝ => (FinProb.map (D.rawTAT H') (localTATProj D c)).w t * x)
    (hAt t)

set_option maxHeartbeats 1000000 in
theorem gsel_congr_local {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hS : D.SelLocal) (H H' : D.Hist)
    (P P' : D.Pos) (c : D.CellT) (ξ : D.Tup) (π : D.Pres c.1)
    (baseT : D.TAT) (baseW : D.Anch)
    (hH : ∀ g, keyDist c.1 g ≤ 4 → H g = H' g)
    (hP : ∀ g, keyDist c.1 g ≤ 3 → P g = P' g) :
    D.Gsel H P c ξ π = D.Gsel H' P' c ξ π := by
  have hUpd : ∀ g, keyDist c.1 g ≤ 4 →
      Function.update H c.1 ξ g = Function.update H' c.1 ξ g := by
    intro g hg
    by_cases hgc : g = c.1
    · subst g
      simp
    · simp [Function.update_of_ne hgc, hH g hg]
  have hNum := rawLaw_pr_congr_local D hS
    (Function.update H c.1 ξ) (Function.update H' c.1 ξ) P P' c π baseT baseW hUpd hP
  have hDen := Lane_q_s08_post.qref_congr_radius_two D H H' c.1
    (D.obsOf π) (fun g hg => hH g (hg.trans (by omega)))
  change (D.rawLaw (Function.update H c.1 ξ) P).pr
      (rawPresEvent D (Function.update H c.1 ξ) P c π) /
      D.Qref H c.1 (D.obsOf π) =
    (D.rawLaw (Function.update H' c.1 ξ) P').pr
      (rawPresEvent D (Function.update H' c.1 ξ) P' c π) /
      D.Qref H' c.1 (D.obsOf π)
  rw [hNum, hDen]

private theorem cube_ball_one_card (d : ℕ) (a : CubeVertex d) :
    (Finset.univ.filter fun u : CubeVertex d => _root_.hammingDist a u ≤ 1).card ≤ d + 1 := by
  classical
  let B : Finset (CubeVertex d) := Finset.univ.filter fun u => _root_.hammingDist a u ≤ 1
  let diff : CubeVertex d → Finset (Fin d) := fun u =>
    Finset.univ.filter fun i => u i ≠ a i
  let small : Finset (Finset (Fin d)) :=
    insert ∅ ((Finset.univ : Finset (Fin d)).image fun i => ({i} : Finset (Fin d)))
  have hdiff_card (u : CubeVertex d) : (diff u).card = _root_.hammingDist a u := by
    simp [diff, _root_.hammingDist, ne_comm]
  have hdiff_inj : Set.InjOn diff (B : Set (CubeVertex d)) := by
    intro u hu v hv huv
    funext i
    have hi : (u i ≠ a i) ↔ (v i ≠ a i) := by
      have hh := congrArg (fun s : Finset (Fin d) => i ∈ s) huv
      simpa [diff] using hh
    cases ha : a i <;> cases hu' : u i <;> cases hv' : v i <;> simp_all
  have hdiff_small : B.image diff ⊆ small := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
    have hcard : (diff u).card ≤ 1 := by
      rw [hdiff_card]
      simpa [B] using hu
    by_cases hzero : (diff u).card = 0
    · have heq : diff u = ∅ := Finset.card_eq_zero.mp hzero
      simp [small, heq]
    · have hpos : 0 < (diff u).card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr (by
          intro he
          exact hzero (by simpa [he])))
      have hone : (diff u).card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simpa [hi]
  have hsmall_card : small.card ≤ d + 1 := by
    calc
      small.card ≤ ((Finset.univ : Finset (Fin d)).image fun i => ({i} : Finset (Fin d))).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ d + 1 := by
        have himage := Finset.card_image_le (s := (Finset.univ : Finset (Fin d)))
          (f := fun i => ({i} : Finset (Fin d)))
        simpa using Nat.add_le_add_right himage 1
  calc
    B.card = (B.image diff).card :=
      (Finset.card_image_of_injOn hdiff_inj).symm
    _ ≤ small.card := Finset.card_le_card hdiff_small
    _ ≤ d + 1 := hsmall_card

theorem ordCells_card_le_n_add_one {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) :
    (D.ordCells c).card ≤ D.n + 1 := by
  classical
  unfold Ctx.ordCells
  calc
    ((ordNbrs c.2).image fun b => (c.1, b)).card ≤ (ordNbrs c.2).card := Finset.card_image_le
    _ ≤ dC η₀ D.n + 1 := by
      simpa [ordNbrs] using cube_ball_one_card (dC η₀ D.n) c.2
    _ ≤ D.n + 1 := Nat.add_le_add_right (Nat.sub_le _ _) 1

theorem ordHit_iff_product {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) (W : D.Anch)
    (a : ∀ e : D.ordCells c, Fin D.N) (y : Fin D.N) :
    D.OrdHit (glue (D.ordCells c) W a) c y ↔
      ∀ e : D.ordCells c, Hits D.E D.G (a e) y := by
  classical
  change (∀ b ∈ ordNbrs c.2, Hits D.E D.G ((glue (D.ordCells c) W a) (c.1, b)) y) ↔ _
  constructor
  · intro h e
    rcases Finset.mem_image.mp e.2 with ⟨b, hb, hbe⟩
    have hmem : (c.1, b) ∈ D.ordCells c := by
      exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    have heq : e = ⟨(c.1, b), hmem⟩ := by
      apply Subtype.ext
      exact hbe.symm
    rw [heq]
    have hh := h b hb
    simpa [glue, hmem] using hh
  · intro h b hb
    have hmem : (c.1, b) ∈ D.ordCells c := Finset.mem_image.mpr ⟨b, hb, rfl⟩
    let e : D.ordCells c := ⟨(c.1, b), hmem⟩
    have hh := h e
    simpa [glue, e, hmem] using hh

theorem glue_ordCells_eq_on_cross {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (c : D.CellT) (W : D.Anch)
    (a : ∀ e : D.ordCells c, Fin D.N) (u : D.CrossSub c.1) :
    (glue (D.ordCells c) W a) (u.1, c.2) = W (u.1, c.2) := by
  classical
  have hnotmem : (u.1, c.2) ∉ D.ordCells c := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨b, hb, hEq⟩
    have hkey : u.1 = c.1 := by
      simpa using (congrArg Prod.fst hEq).symm
    have hself : keyDist c.1 c.1 = 0 := by simp [keyDist]
    have hu : keyDist c.1 u.1 = 1 := (Finset.mem_filter.mp u.2).2
    rw [hkey] at hu
    rw [hself] at hu
    norm_num at hu
  simp [glue, hnotmem]

theorem keyDist_triangle {η₀ : ℝ} {n : ℕ}
    (a b c : Key η₀ n) : keyDist a c ≤ keyDist a b + keyDist b c := by
  unfold keyDist
  calc
    (∑ r, Nat.dist (a r).val (c r).val) ≤
        ∑ r, (Nat.dist (a r).val (b r).val + Nat.dist (b r).val (c r).val) := by
          apply Finset.sum_le_sum
          intro r hr
          exact Nat.dist.triangle_inequality _ _ _
    _ = (∑ r, Nat.dist (a r).val (b r).val) +
          ∑ r, Nat.dist (b r).val (c r).val := Finset.sum_add_distrib

theorem keyDist_symm {η₀ : ℝ} {n : ℕ} (a b : Key η₀ n) : keyDist a b = keyDist b a := by
  unfold keyDist
  apply Finset.sum_congr rfl
  intro r hr
  exact Nat.dist_comm _ _

theorem presValid_iff_cross_anchors_eq {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hcross : ∀ u : D.CrossSub c.1, W (u.1, c.2) = W' (u.1, c.2)) :
    D.PresValid q W c ↔ D.PresValid q W' c := by
  classical
  have hpres : D.presOf q W c = D.presOf q W' c := by
    apply Prod.ext
    · rfl
    · funext u
      simp only [Ctx.presOf]
      rw [hcross u]
  unfold Ctx.PresValid
  rw [hpres]

theorem p0_eq_of_cross_anchors_eq {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hcross : ∀ u : D.CrossSub c.1, W (u.1, c.2) = W' (u.1, c.2))
    (y : Fin D.N) : D.p0 q W c y = D.p0 q W' c y := by
  classical
  have hpres : D.presOf q W c = D.presOf q W' c := by
    apply Prod.ext
    · rfl
    · funext u
      simp only [Ctx.presOf]
      rw [hcross u]
  have hvalid : D.PresValid q W c ↔ D.PresValid q W' c := by
    unfold Ctx.PresValid
    rw [hpres]
  have hvalidEq : D.PresValid q W c = D.PresValid q W' c := propext hvalid
  unfold Ctx.p0
  rw [hvalidEq, hpres]

theorem p0_eq_on_ordinary_glue {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (q : D.Pre) (W : D.Anch) (c : D.CellT)
    (a : ∀ e : D.ordCells c, Fin D.N) (y : Fin D.N) :
    D.p0 q (glue (D.ordCells c) W a) c y = D.p0 q W c y := by
  symm
  apply p0_eq_of_cross_anchors_eq D q W (glue (D.ordCells c) W a) c
  intro u
  exact (glue_ordCells_eq_on_cross D c W a u).symm

end Lane_q_s08_post

theorem avgMarg_nonneg {N k : ℕ} (Q : FinProb (Fin k → Fin N)) (y : Fin N) :
    0 ≤ averageCoordinateMarginal Q y := by
  unfold averageCoordinateMarginal
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))
  apply Finset.sum_nonneg
  intro j hj
  exact pr_nonneg Q (fun ξ => ξ j = y)

theorem avgMarg_sum_one {N k : ℕ} (Q : FinProb (Fin k → Fin N)) (hk : 0 < k) :
    ∑ y : Fin N, averageCoordinateMarginal Q y = 1 := by
  classical
  have hprob (j : Fin k) (y : Fin N) : Q.pr (fun ξ => ξ j = y) =
      (FinProb.map Q (fun ξ => ξ j)).w y := by
    unfold FinProb.pr FinProb.map
    apply Finset.sum_congr rfl
    intro ξ hξ
    exact PToolsMisc.ite_decidable_irrel (ξ j = y) (Classical.propDecidable _)
      (inferInstance : Decidable (ξ j = y)) _ _
  have hcoord (j : Fin k) : ∑ y : Fin N, Q.pr (fun ξ => ξ j = y) = 1 := by
    calc
      ∑ y : Fin N, Q.pr (fun ξ => ξ j = y) =
          ∑ y : Fin N, (FinProb.map Q (fun ξ => ξ j)).w y := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hprob j y
      _ = 1 := (FinProb.map Q (fun ξ => ξ j)).sum_eq_one
  unfold averageCoordinateMarginal
  rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    (k : ℝ)⁻¹ * ∑ j : Fin k, ∑ y : Fin N, Q.pr (fun ξ => ξ j = y) =
        (k : ℝ)⁻¹ * ∑ j : Fin k, 1 := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          exact hcoord j
    _ = 1 := by simp [hk.ne']

theorem avgMarg_ne_zero_support {N k : ℕ} (Q : FinProb (Fin k → Fin N)) (y : Fin N)
    (hQ : averageCoordinateMarginal Q y ≠ 0) :
    ∃ ξ j, Q.w ξ ≠ 0 ∧ ξ j = y := by
  classical
  have hsum : (∑ j : Fin k, Q.pr (fun ξ => ξ j = y)) ≠ 0 := by
    intro hs
    apply hQ
    simp [averageCoordinateMarginal, hs]
  have hj : ∃ j : Fin k, Q.pr (fun ξ => ξ j = y) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hsum
    apply Finset.sum_eq_zero
    intro j hj
    exact hn j
  obtain ⟨j, hj⟩ := hj
  have hξ : ∃ ξ, ξ j = y ∧ Q.w ξ ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hj
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro ξ hξ
    by_cases hxy : ξ j = y
    · have hw : Q.w ξ = 0 := hn ξ hxy
      simp [hxy, hw]
    · simp [hxy]
  obtain ⟨ξ, hxy, hw⟩ := hξ
  exact ⟨ξ, j, hw, hxy⟩

private theorem basePost_pos_fcand_pos {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) (c : D.CellT) (π : D.Pres c.1) (ξ : D.Tup)
    (hM : 0 < D.Mden Θ c.1 (D.obsOf π))
    (hq : 0 < (D.basePost Θ c.1 (D.obsOf π)).w ξ) :
    0 < D.Fcand Θ c.1 ξ (D.obsOf π) := by
  have hsum : ∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π) =
      D.Mden Θ c.1 (D.obsOf π) := rfl
  have hden : 0 < ∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π) := by
    simpa [hsum] using hM
  change 0 < (if ∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π) = 0 then
      D.R'.w ξ else
      D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) /
        ∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π)) at hq
  rw [if_neg (ne_of_gt hden)] at hq
  have hprod : 0 < D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) := by
    by_contra hnot
    have hle : D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) ≤ 0 := le_of_not_gt hnot
    have hinv : 0 ≤ (∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π))⁻¹ :=
      (inv_pos.mpr hden).le
    have hmul : D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) *
        (∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π))⁻¹ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hinv
    have hpositive : 0 < D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) *
        (∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π))⁻¹ := by
      simpa [div_eq_mul_inv] using hq
    exact (not_le_of_gt hpositive) hmul
  have hR : 0 ≤ D.R'.w ξ := D.R'.nonneg ξ
  have hF : 0 ≤ D.Fcand Θ c.1 ξ (D.obsOf π) := D.Fcand_nonneg Θ c.1 ξ (D.obsOf π)
  by_contra hnot
  have hF' : D.Fcand Θ c.1 ξ (D.obsOf π) ≤ 0 := le_of_not_gt hnot
  have hmul : D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hR hF'
  exact (not_le_of_gt hprod) hmul

theorem selPost_pos_fcand_pos {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (π : D.Pres c.1) (ξ : D.Tup)
    (hM : 0 < D.Mden Θ c.1 (D.obsOf π))
    (hG : D.Gsel Θ P c ξ π ≤ D.Fcand Θ c.1 ξ (D.obsOf π))
    (hq : 0 < (D.selPost Θ P c π).w ξ) :
    0 < D.Fcand Θ c.1 ξ (D.obsOf π) := by
  classical
  have hbase : 0 < (D.basePost Θ c.1 (D.obsOf π)).w ξ →
      0 < D.Fcand Θ c.1 ξ (D.obsOf π) :=
    basePost_pos_fcand_pos D Θ c π ξ hM
  unfold Ctx.selPost at hq
  split_ifs at hq with hadj
  · let f : D.Tup → ℝ := fun ξ' => D.R'.w ξ' * D.Gsel Θ P c ξ' π
    change 0 < (if ∑ ξ', f ξ' = 0 then (D.basePost Θ c.1 (D.obsOf π)).w ξ
      else f ξ / ∑ ξ', f ξ') at hq
    by_cases hsum : ∑ ξ', f ξ' = 0
    · have hqbase : 0 < (D.basePost Θ c.1 (D.obsOf π)).w ξ := by
        simpa [hsum] using hq
      exact hbase hqbase
    · have hsumNonneg : 0 ≤ ∑ ξ', f ξ' := by
        apply Finset.sum_nonneg
        intro ξ' hξ'
        exact mul_nonneg (D.R'.nonneg ξ') (D.Gsel_nonneg Θ P c ξ' π)
      have hsumPos : 0 < ∑ ξ', f ξ' := lt_of_le_of_ne hsumNonneg (Ne.symm hsum)
      have hqdiv : 0 < f ξ / ∑ ξ', f ξ' := by
        simpa [hsum] using hq
      have hprod : 0 < D.R'.w ξ * D.Gsel Θ P c ξ π := by
        by_contra hnot
        have hle : D.R'.w ξ * D.Gsel Θ P c ξ π ≤ 0 := le_of_not_gt hnot
        have hinv : 0 ≤ (∑ ξ', f ξ')⁻¹ := (inv_pos.mpr hsumPos).le
        have hmul : D.R'.w ξ * D.Gsel Θ P c ξ π * (∑ ξ', f ξ')⁻¹ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hle hinv
        have hpositive : 0 < D.R'.w ξ * D.Gsel Θ P c ξ π * (∑ ξ', f ξ')⁻¹ := by
          simpa [div_eq_mul_inv] using hqdiv
        exact (not_le_of_gt hpositive) hmul
      have hGpos : 0 < D.Gsel Θ P c ξ π := by
        have hR : 0 ≤ D.R'.w ξ := D.R'.nonneg ξ
        by_contra hnot
        have hG' : D.Gsel Θ P c ξ π ≤ 0 := le_of_not_gt hnot
        have hmul : D.R'.w ξ * D.Gsel Θ P c ξ π ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR hG'
        exact (not_le_of_gt hprod) hmul
      exact lt_of_lt_of_le hGpos hG
  · exact hbase hq

namespace Lane_q_s08_post

private theorem p0_label_coordinate_gate {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hF : D.FSupport) (hG : D.GselLeF)
    (q : D.Pre) (W : D.Anch) (c : D.CellT) (y : Fin D.N)
    (hvalid : D.PresValid q W c) (hp0 : D.p0 q W c y ≠ 0)
    (ℓ : D.Loc) (hℓ : ℓ ∈ D.intIds q c) :
    ∃ ξ j, ξ j = y ∧
      D.GateOpen (Function.update q.1.1 c.1 ξ) c.1 (q.2.1.1 c.1 ℓ) := by
  classical
  let π : D.Pres c.1 := D.presOf q W c
  let Q : FinProb D.Tup := D.selPost q.1.1 q.1.2 c π
  have hp0w : D.p0w q.1.1 q.1.2 c π y ≠ 0 := by
    intro hz
    apply hp0
    simp [Ctx.p0, hvalid, π, hz]
  have hlight : D.lightMass Q ≠ 0 := by
    intro hz
    apply hp0w
    simp [Ctx.p0w, π, Q, hz]
  have hMarg : averageCoordinateMarginal Q y ≠ 0 := by
    intro hz
    apply hp0w
    simp [Ctx.p0w, π, Q, hlight, hz]
  obtain ⟨ξ, j, hξ, hcoord⟩ := avgMarg_ne_zero_support Q y hMarg
  have hQpos : 0 < Q.w ξ := lt_of_le_of_ne (Q.nonneg ξ) (Ne.symm hξ)
  have hden : D.eps0 ≤ D.Mden q.1.1 c.1 (D.obsOf π) := hvalid.2.2.2.2.2
  have heps : 0 < D.eps0 := Real.exp_pos _
  have hM : 0 < D.Mden q.1.1 c.1 (D.obsOf π) := lt_of_lt_of_le heps hden
  have hGξ : D.Gsel q.1.1 q.1.2 c ξ π ≤ D.Fcand q.1.1 c.1 ξ (D.obsOf π) :=
    hG q.1.1 q.1.2 c ξ π
  have hFcand : 0 < D.Fcand q.1.1 c.1 ξ (D.obsOf π) :=
    selPost_pos_fcand_pos D q.1.1 q.1.2 c π ξ hM hGξ (by simpa [Q] using hQpos)
  have hfs := hF q.1.1 c.1 ξ (D.obsOf π) (ne_of_gt hFcand)
  have hobs : (D.obsOf π).1 ℓ = some (q.2.1.1 c.1 ℓ) := by
    simp [π, Ctx.obsOf, Ctx.presOf, hℓ]
  exact ⟨ξ, j, hcoord, hfs.2 ℓ (q.2.1.1 c.1 ℓ) hobs⟩

theorem selected_anchor_miss_bound {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hn : 1 ≤ D.n) (hF : D.FSupport) (hG : D.GselLeF)
    (q : D.Pre) (W : D.Anch) (c : D.CellT) (hSupp : D.Supp q)
    (hvalid : D.PresValid q W c) (e : D.ordCells c) (y : Fin D.N)
    (hp0 : D.p0 q W c y ≠ 0) :
    (D.Usel q e.1).pr (fun x => ¬ Hits D.E D.G x y) ≤ D.Δ / (1 - D.Δ) := by
  classical
  rcases Finset.mem_image.mp e.2 with ⟨b, hb, hbe⟩
  have hcell : e.1 = (c.1, b) := hbe.symm
  have hselSome : (D.sel q (c.1, b)).isSome := hvalid.2.1 b hb
  cases hsel : D.sel q (c.1, b) with
  | none => simp [hsel] at hselSome
  | some ℓ =>
      have hℓmem : ℓ ∈ D.intIds q c := by
        unfold Ctx.intIds
        rw [Finset.mem_biUnion]
        exact ⟨b, hb, by simp [hsel]⟩
      let i : D.M.ι := q.2.1.1 c.1 ℓ
      have htruePos : 0 < (D.tilt q.1.1 c.1).w i := hSupp.2 c.1 ℓ
      have htrue : D.GateOpen q.1.1 c.1 i :=
        positive_tilt_gate D q.1.1 c.1 i hvalid.1.1 htruePos
      obtain ⟨ξ, j, hcoord, hcand⟩ :=
        p0_label_coordinate_gate D hF hG q W c y hvalid hp0 ℓ hℓmem
      have hU : D.Usel q (c.1, b) = D.anchorU q.1.1 c.1 i := by
        simp [Ctx.Usel, Ctx.selTag, hsel, i]
      rw [hcell, hU, ← hcoord]
      exact anchor_miss_le D hn q.1.1 c.1 i ξ j htrue hcand

end Lane_q_s08_post

end HypercubeRamsey.S08
