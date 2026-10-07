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
