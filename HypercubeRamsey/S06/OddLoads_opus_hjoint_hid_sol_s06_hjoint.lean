import HypercubeRamsey.S06.OddLoads_opus_hjoint_tuples_sol_s06_hjoint

namespace HypercubeRamsey.S06.Lane_sol_s06_hjoint

open OAI.HypercubeRamsey Classical
open scoped BigOperators

noncomputable section

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
  {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

def tupleScope (u : CubeVertex n) : Finset (X.Loc × X.Ty) :=
  Finset.univ.filter fun e => e.2.obs ⊆ signScope X u

theorem locHid_scope (u : CubeVertex n) (D : Finset (X.Loc × X.Ty))
    (hD : ∀ e ∈ D, e.2.obs ⊆ signScope X u) : X.locHid D ⊆ signScope X u := by
  intro ℓ hℓ
  obtain ⟨e, he, hℓ⟩ := Finset.mem_biUnion.mp hℓ
  exact hD e he hℓ

theorem role_target_scope (u : CubeVertex n) : X.tgt (X.g.L.stateOf u) ∈ signScope X u := by
  apply target_scope X u (X.g.L.stateOf u)
  rw [X.facts.sign_eq u, _root_.hammingDist_self]
  exact Nat.zero_le _

theorem short_choices_congr_hid (u : CubeVertex n) (b₀ : X.Base) (C : X.Centre)
    (Z Z' : X.Hid) (hZ : ∀ ℓ ∈ signScope X u, Z ℓ = Z' ℓ) :
    ∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u),
      X.choice (b₀, Z) C X.Rshort a = X.choice (b₀, Z') C X.Rshort a := by
  apply short_choices_congr_tests X u (b₀, Z) (b₀, Z') C C rfl rfl rfl
  intro b hb j D hD
  apply _root_.Lane_q_s06_loads.S3Fail_congr_hid X b₀ Z Z' b D (X.tup C)
  · intro ℓ hℓ
    exact hZ ℓ (locHid_scope X u D (fun e he => descsIn_obs_scope X u b hb _ hD he) hℓ)
  · exact hZ (X.tgt b) (target_scope X u b hb)

theorem oddValid_congr_hid (u : CubeVertex n) (b₀ : X.Base) (C : X.Centre)
    (Z Z' : X.Hid) (hZ : ∀ ℓ ∈ signScope X u, Z ℓ = Z' ℓ) :
    X.OddValid (b₀, Z) C X.Rshort (X.g.L.stateOf u) ↔
      X.OddValid (b₀, Z') C X.Rshort (X.g.L.stateOf u) := by
  have hc := short_choices_congr_hid X u b₀ C Z Z' hZ
  have hd := actDesc_congr_choices X (b₀, Z) (b₀, Z') C C (X.g.L.stateOf u) X.Rshort hc
  have ho : ∀ ℓ ∈ X.locHid (X.actDesc (b₀, Z) C X.Rshort (X.g.L.stateOf u)), Z ℓ = Z' ℓ :=
    fun ℓ hℓ => hZ ℓ (locHid_scope X u _
      (fun e he => actDesc_obs_scope X u (b₀, Z) C X.Rshort he) hℓ)
  have hg := _root_.Lane_q_s06_loads.S3TrueGate_congr_hid X b₀ Z Z' (X.g.L.stateOf u)
    (X.actDesc (b₀, Z) C X.Rshort (X.g.L.stateOf u)) ho
    (hZ _ (role_target_scope X u))
  have htests := _root_.Lane_q_s06_loads.S3Tests_congr_hid X b₀ Z Z' (X.g.L.stateOf u)
    (X.actDesc (b₀, Z) C X.Rshort (X.g.L.stateOf u)) (X.tup C) ho
  have hs : (∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u), (X.choice (b₀, Z) C X.Rshort a).isSome) ↔
      (∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u), (X.choice (b₀, Z') C X.Rshort a).isSome) := by
    apply forall₂_congr
    intro a ha
    rw [hc a ha]
  have hl : (∃ j : Fin X.hp.H, ∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u), ∀ ℓ,
      X.choice (b₀, Z) C X.Rshort a = some ℓ → ℓ.2 ∈ X.levelPair j) ↔
      (∃ j : Fin X.hp.H, ∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u), ∀ ℓ,
      X.choice (b₀, Z') C X.Rshort a = some ℓ → ℓ.2 ∈ X.levelPair j) := by
    apply exists_congr
    intro j
    apply forall₂_congr
    intro a ha
    rw [hc a ha]
  unfold Ctx6.OddValid
  rw [← hd, hg, htests, hs, hl]

theorem presents_congr_hid (u : CubeVertex n) (b₀ : X.Base) (C : X.Centre)
    (Z Z' : X.Hid) (hZ : ∀ ℓ ∈ signScope X u, Z ℓ = Z' ℓ)
    (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc) :
    X.Presents (b₀, Z) C (X.g.L.stateOf u) D o ↔
      X.Presents (b₀, Z') C (X.g.L.stateOf u) D o := by
  have hv := oddValid_congr_hid X u b₀ C Z Z' hZ
  have hd := actDesc_congr_choices X (b₀, Z) (b₀, Z') C C (X.g.L.stateOf u) X.Rshort
    (short_choices_congr_hid X u b₀ C Z Z' hZ)
  unfold Ctx6.Presents
  rw [hv, hd]

theorem presents_congr_data (u : CubeVertex n) (H : X.Hist) (C C' : X.Centre)
    (hp : X.pos C = X.pos C') (ha : X.act C = X.act C') (ht : X.ties C = X.ties C')
    (ho : TupleAgree X u C C') (D : Finset (X.Loc × X.Ty))
    (hD : ∀ e ∈ D, e.2.obs ⊆ signScope X u) (o : X.Data X.Loc) :
    X.Presents H C (X.g.L.stateOf u) D o ↔ X.Presents H C' (X.g.L.stateOf u) D o := by
  have hv := oddValid_congr_data X u H C C' hp ha ht ho
  have hd := actDesc_congr_choices X H H C C' (X.g.L.stateOf u) X.Rshort
    (short_choices_congr_data X u H C C' hp ha ht ho)
  unfold Ctx6.Presents
  rw [hv, hd]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply forall₂_congr
  intro e he
  rw [ho e (hD e he)]

theorem update_scope_agree (u : CubeVertex n) (Z Z' : X.Hid)
    (hZ : ∀ ℓ ∈ signScope X u, Z ℓ = Z' ℓ) (t : X.HKey) (ξ : Fin N) :
    ∀ ℓ ∈ signScope X u, Function.update Z t ξ ℓ = Function.update Z' t ξ ℓ := by
  classical
  intro ℓ hℓ
  by_cases heq : ℓ = t
  · simp [heq]
  · simp [Function.update_of_ne heq, hZ ℓ hℓ]

theorem pr_expect_indicator {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A = P.expect (fun ω => if A ω then 1 else 0) := by
  classical
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : A ω <;> simp [h]

theorem presents_indicator_depends (u : CubeVertex n) (H : X.Hist) (P a : X.Loc → Bool)
    (τ : X.hp.Ties) (D : Finset (X.Loc × X.Ty))
    (hD : ∀ e ∈ D, e.2.obs ⊆ signScope X u) (o : X.Data X.Loc) :
    FinProb.DependsOn (fun d : X.Data X.Loc =>
      if X.Presents H (((P, d), a), τ) (X.g.L.stateOf u) D o then (1 : ℝ) else 0)
      (tupleScope X u) := by
  classical
  intro d d' hdd
  have ho : TupleAgree X u (((P, d), a), τ) (((P, d'), a), τ) := by
    intro e he
    exact hdd e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
  have hP := presents_congr_data X u H (((P, d), a), τ) (((P, d'), a), τ)
    rfl rfl rfl ho D hD o
  change (if X.Presents H (((P, d), a), τ) (X.g.L.stateOf u) D o then (1 : ℝ) else 0) =
    (if X.Presents H (((P, d'), a), τ) (X.g.L.stateOf u) D o then 1 else 0)
  rw [propext hP]

theorem presProb_congr_hid (u : CubeVertex n) (b₀ : X.Base) (P : X.Loc → Bool)
    (Z Z' : X.Hid) (hZ : ∀ ℓ ∈ signScope X u, Z ℓ = Z' ℓ)
    (D : Finset (X.Loc × X.Ty)) (hD : ∀ e ∈ D, e.2.obs ⊆ signScope X u)
    (o : X.Data X.Loc) (ξ : Fin N) :
    X.presProb (b₀, Z) P (X.g.L.stateOf u) D o ξ =
      X.presProb (b₀, Z') P (X.g.L.stateOf u) D o ξ := by
  classical
  let Zξ : X.Hid := Function.update Z (X.tgt (X.g.L.stateOf u)) ξ
  let Zξ' : X.Hid := Function.update Z' (X.tgt (X.g.L.stateOf u)) ξ
  have hξ : ∀ ℓ ∈ signScope X u, Zξ ℓ = Zξ' ℓ :=
    update_scope_agree X u Z Z' hZ _ ξ
  have hInd (ω : (X.Data X.Loc × (X.Loc → Bool)) × X.hp.Ties) :
      X.Presents (b₀, Zξ) (X.assemble P ω) (X.g.L.stateOf u) D o ↔
      X.Presents (b₀, Zξ') (X.assemble P ω) (X.g.L.stateOf u) D o :=
    presents_congr_hid X u b₀ (X.assemble P ω) Zξ Zξ' hξ D o
  unfold Ctx6.presProb
  rw [pr_expect_indicator, pr_expect_indicator]
  change (X.proxyLaw (b₀, Zξ)).expect (fun ω =>
      if X.Presents (b₀, Zξ) (X.assemble P ω) (X.g.L.stateOf u) D o then 1 else 0) =
    (X.proxyLaw (b₀, Zξ')).expect (fun ω =>
      if X.Presents (b₀, Zξ') (X.assemble P ω) (X.g.L.stateOf u) D o then 1 else 0)
  simp_rw [hInd]
  unfold Ctx6.proxyLaw
  simp only [_root_.Lane_q_s06_loads.finProb_prod_expect]
  apply _root_.Lane_q_s06_loads.dataLaw_expect_congr_hid X b₀ Zξ Zξ' (tupleScope X u)
  · intro d d' hdd
    have hP (a : X.Loc → Bool) (τ : X.hp.Ties) :
        (if X.Presents (b₀, Zξ') (((P, d), a), τ) (X.g.L.stateOf u) D o then (1 : ℝ) else 0) =
        (if X.Presents (b₀, Zξ') (((P, d'), a), τ) (X.g.L.stateOf u) D o then 1 else 0) :=
      presents_indicator_depends X u (b₀, Zξ') P a τ D hD o d d' hdd
    apply congrArg (fun f : (X.Loc → Bool) → ℝ => X.hp.actLaw.expect f)
    funext a
    apply congrArg (fun f : X.hp.Ties → ℝ => X.hp.tieLaw.expect f)
    funext τ
    exact hP a τ
  · intro e he ℓ hℓ
    exact hξ ℓ ((Finset.mem_filter.mp he).2 hℓ)

theorem s3Post_congr_hid (b₀ : X.Base) (Z Z' : X.Hid) (b : X.State)
    (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc)
    (ho : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) :
    X.s3Post (b₀, Z) b D o = X.s3Post (b₀, Z') b D o := by
  unfold Ctx6.s3Post
  congr 1
  funext ξ
  exact _root_.Lane_q_s06_loads.s3Weight_congr_hid X b₀ Z Z' b D o none ξ ho

theorem lowRow_congr_hid (u : CubeVertex n) (b₀ : X.Base) (P : X.Loc → Bool)
    (Z Z' : X.Hid) (hZ : ∀ ℓ ∈ signScope X u, Z ℓ = Z' ℓ)
    (D : Finset (X.Loc × X.Ty)) (hD : ∀ e ∈ D, e.2.obs ⊆ signScope X u)
    (o : X.Data X.Loc) :
    X.lowRow (b₀, Z) P (X.g.L.stateOf u) D o =
      X.lowRow (b₀, Z') P (X.g.L.stateOf u) D o := by
  have ho : ∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ := fun ℓ hℓ => hZ ℓ (locHid_scope X u D hD hℓ)
  have hF (ξ : Fin N) : X.lowF (b₀, Z) (X.g.L.stateOf u) D o ξ =
      X.lowF (b₀, Z') (X.g.L.stateOf u) D o ξ := by
    unfold Ctx6.lowF
    rw [propext (_root_.Lane_q_s06_loads.lowGate_congr_hid X b₀ Z Z'
      (X.g.L.stateOf u) D ξ ho)]
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    exact _root_.Lane_q_s06_loads.lowLik_congr_hid X b₀ Z Z' (X.g.L.stateOf u) ξ e.2 (o e)
      (fun ℓ hℓ => hZ ℓ (hD e he hℓ))
  have hQ : X.lowQ (b₀, Z) (X.g.L.stateOf u) D o =
      X.lowQ (b₀, Z') (X.g.L.stateOf u) D o := by
    unfold Ctx6.lowQ
    apply Finset.prod_congr rfl
    intro e he
    rw [_root_.Lane_q_s06_loads.lowRef_congr_hid X b₀ Z Z' (X.g.L.stateOf u) e.2
      (fun ℓ hℓ => hZ ℓ (hD e he hℓ))]
  have hpres (ξ : Fin N) := presProb_congr_hid X u b₀ P Z Z' hZ D hD o ξ
  have hW (ξ : Fin N) : X.adjWeight (b₀, Z) P (X.g.L.stateOf u) D o ξ =
      X.adjWeight (b₀, Z') P (X.g.L.stateOf u) D o ξ := by
    unfold Ctx6.adjWeight Ctx6.table
    rw [hF ξ, hQ, hpres ξ]
  unfold Ctx6.lowRow
  simp_rw [hF, hW]
  rw [s3Post_congr_hid X b₀ Z Z' (X.g.L.stateOf u) D o ho,
    show X.adjWeight (b₀, Z) P (X.g.L.stateOf u) D o =
      X.adjWeight (b₀, Z') P (X.g.L.stateOf u) D o from funext hW]

theorem proxyRow_hid_local (b₀ : X.Base) (C : X.Centre) (u : CubeVertex n) (y : Fin N)
    (Z Z' : X.Hid) (hZ : ∀ ℓ ∈ signScope X u, Z ℓ = Z' ℓ) :
    X.proxyRow (b₀, Z) C u y = X.proxyRow (b₀, Z') C u y := by
  have hc := short_choices_congr_hid X u b₀ C Z Z' hZ
  have hd := actDesc_congr_choices X (b₀, Z) (b₀, Z') C C (X.g.L.stateOf u) X.Rshort hc
  have hv := oddValid_congr_hid X u b₀ C Z Z' hZ
  have hD : ∀ e ∈ X.actDesc (b₀, Z) C X.Rshort (X.g.L.stateOf u), e.2.obs ⊆ signScope X u :=
    fun e he => actDesc_obs_scope X u (b₀, Z) C X.Rshort he
  unfold Ctx6.proxyRow Ctx6.oddRowAt
  rw [propext hv, ← hd]
  split
  · cases hm : X.stMode (X.g.L.stateOf u) with
    | low => rw [lowRow_congr_hid X u b₀ (X.pos C) Z Z' hZ _ hD (X.tup C)]
    | high =>
      rw [s3Post_congr_hid X b₀ Z Z' (X.g.L.stateOf u) _ (X.tup C)
        (fun ℓ hℓ => hZ ℓ (locHid_scope X u _ hD hℓ))]
  · rfl

end

end HypercubeRamsey.S06.Lane_sol_s06_hjoint
