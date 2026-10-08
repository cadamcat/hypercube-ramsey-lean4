import HypercubeRamsey.S06.OddLoads_opus_hjoint_sol_s06_hjoint

namespace HypercubeRamsey.S06.Lane_sol_s06_hjoint

open OAI.HypercubeRamsey Classical
open scoped BigOperators

noncomputable section

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
  {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

def signScope (u : CubeVertex n) : Finset X.HKey :=
  Finset.univ.filter fun ℓ => _root_.hammingDist ℓ.2 (X.g.L.sign u) ≤ X.Rshort + 6

def TupleAgree (u : CubeVertex n) (C C' : X.Centre) : Prop :=
  ∀ e : X.Loc × X.Ty, e.2.obs ⊆ signScope X u → X.tup C e = X.tup C' e

theorem reach_congr_bad (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool)
    (elig elig' : p.EligMap) (q : CubeVertex p.d) (R : ℕ)
    (hb : ∀ v ∈ Sites, _root_.hammingDist v q ≤ R → ∀ j,
      p.Bad P A elig v j ↔ p.Bad P A elig' v j) (v : CubeVertex p.d) (j : ℕ) :
    p.Reach Sites P A elig q R v j ↔ p.Reach Sites P A elig' q R v j := by
  have forward (elig elig' : p.EligMap)
      (hb : ∀ v ∈ Sites, _root_.hammingDist v q ≤ R → ∀ j,
        p.Bad P A elig v j ↔ p.Bad P A elig' v j)
      {v j} (h : p.Reach Sites P A elig q R v j) :
      p.Reach Sites P A elig' q R v j := by
    induction h with
    | start v hv hd => exact .start v hv hd
    | up v j hj h hbad ih =>
      obtain ⟨hv, hd⟩ := reach_domain p Sites P A elig q R h
      obtain ⟨hj', hbad⟩ := hbad
      exact .up v j hj ih ⟨hj', (hb v hv hd ⟨j, hj'⟩).mp hbad⟩
    | down v v' j h hv hd hdist ih => exact .down v v' j ih hv hd hdist
  exact ⟨forward elig elig' hb,
    forward elig' elig (fun v hv hd j => (hb v hv hd j).symm)⟩

theorem selection_congr_elig (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool)
    (elig elig' : p.EligMap) (τ : p.Ties) (q : CubeVertex p.d) (R : ℕ)
    (he : ∀ v ∈ Sites, _root_.hammingDist v q ≤ R → ∀ j, elig v j = elig' v j)
    (heq : ∀ j, elig q j = elig' q j) :
    p.selectionAt Sites P A elig τ R q = p.selectionAt Sites P A elig' τ R q := by
  have hb (v) (hv : v ∈ Sites) (hd : _root_.hammingDist v q ≤ R) (j) :
      p.Bad P A elig v j ↔ p.Bad P A elig' v j := by
    unfold HDParams.Bad
    rw [he v hv hd j]
  have hheight : p.height Sites P A elig R q = p.height Sites P A elig' R q := by
    unfold HDParams.height
    congr 1
    ext j
    simp only [Finset.mem_filter]
    rw [reach_congr_bad p Sites P A elig elig' q R hb]
  have hbq (j) : p.Bad P A elig q j ↔ p.Bad P A elig' q j := by
    unfold HDParams.Bad
    rw [heq j]
  have hactive (j) : (elig q j).filter (fun ℓ => A ℓ = true) =
      (elig' q j).filter (fun ℓ => A ℓ = true) := by rw [heq j]
  unfold HDParams.selectionAt
  simp only [hheight]
  split
  · simp only [show p.Bad P A elig q ⟨p.height Sites P A elig' R q, by omega⟩ =
      p.Bad P A elig' q ⟨p.height Sites P A elig' R q, by omega⟩ from propext (hbq _)]
    split
    · rfl
    · simp only [hactive]
  · rfl

theorem failedSets_congr_tests (H H' : X.Hist) (C C' : X.Centre) (b : X.State)
    (hp : X.pos C = X.pos C') (j : Fin X.hp.H)
    (hf : ∀ D ∈ X.descsIn b (X.permAt (X.pos C) b j),
      X.S3Fail H b D (X.tup C) ↔ X.S3Fail H' b D (X.tup C')) :
    X.failedSets H C b j = X.failedSets H' C' b j := by
  unfold Ctx6.failedSets
  rw [← hp]
  congr 1
  apply Finset.filter_congr
  exact hf

theorem marked_congr_tests (u : CubeVertex n) (H H' : X.Hist) (C C' : X.Centre)
    (a : X.State) (ha : a ∈ X.g.L.stNbr (X.g.L.stateOf u))
    (v : CubeVertex X.code.d) (hd : _root_.hammingDist v (X.site a) ≤ X.Rshort)
    (hp : X.pos C = X.pos C')
    (hf : ∀ b, _root_.hammingDist (X.g.L.stSign b) (X.g.L.sign u) ≤ X.Rshort + 2 →
      ∀ j D, D ∈ X.descsIn b (X.permAt (X.pos C) b j) →
        (X.S3Fail H b D (X.tup C) ↔ X.S3Fail H' b D (X.tup C')))
    (l : Fin (X.hp.H + 1)) : X.marked H C v l = X.marked H' C' v l := by
  unfold Ctx6.marked
  apply Finset.biUnion_congr rfl
  intro b hb
  split_ifs with hinc
  · apply Finset.biUnion_congr rfl
    intro j hj
    have hnear := consulted_incident_star_sign X u a ha v hd b hinc
    rw [failedSets_congr_tests X H H' C C' b hp j (hf b hnear j)]
  · rfl

theorem short_choices_congr_tests (u : CubeVertex n) (H H' : X.Hist) (C C' : X.Centre)
    (hp : X.pos C = X.pos C') (ha : X.act C = X.act C') (ht : X.ties C = X.ties C')
    (hf : ∀ b, _root_.hammingDist (X.g.L.stSign b) (X.g.L.sign u) ≤ X.Rshort + 2 →
      ∀ j D, D ∈ X.descsIn b (X.permAt (X.pos C) b j) →
        (X.S3Fail H b D (X.tup C) ↔ X.S3Fail H' b D (X.tup C'))) :
    ∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u),
      X.choice H C X.Rshort a = X.choice H' C' X.Rshort a := by
  intro a hab
  have he (v : CubeVertex X.code.d) (hd : _root_.hammingDist v (X.site a) ≤ X.Rshort) (j) :
      X.elig H C v j = X.elig H' C' v j := by
    unfold Ctx6.elig
    rw [hp, marked_congr_tests X u H H' C C' a hab v hd hp hf j]
  unfold Ctx6.choice
  rw [← hp, ← ha, ← ht]
  apply selection_congr_elig
  · intro v hv hd j
    exact he v hd j
  · intro j
    exact he (X.site a) (by simp only [_root_.hammingDist_self]; exact Nat.zero_le _) j

theorem actDesc_congr_choices (H H' : X.Hist) (C C' : X.Centre) (b : X.State) (R : ℕ)
    (hc : ∀ a ∈ X.g.L.stNbr b, X.choice H C R a = X.choice H' C' R a) :
    X.actDesc H C R b = X.actDesc H' C' R b := by
  unfold Ctx6.actDesc
  congr 1
  funext a
  rw [hc a.1 a.2]

theorem short_choices_congr_data (u : CubeVertex n) (H : X.Hist) (C C' : X.Centre)
    (hp : X.pos C = X.pos C') (ha : X.act C = X.act C') (ht : X.ties C = X.ties C')
    (ho : TupleAgree X u C C') :
    ∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u),
      X.choice H C X.Rshort a = X.choice H C' X.Rshort a := by
  apply short_choices_congr_tests X u H H C C' hp ha ht
  intro b hb j D hD
  apply _root_.Lane_q_s06_loads.S3Fail_congr_data X H b D (X.tup C) (X.tup C')
  intro e he
  exact ho e (descsIn_obs_scope X u b hb _ hD he)

theorem oddValid_congr_data (u : CubeVertex n) (H : X.Hist) (C C' : X.Centre)
    (hp : X.pos C = X.pos C') (ha : X.act C = X.act C') (ht : X.ties C = X.ties C')
    (ho : TupleAgree X u C C') :
    X.OddValid H C X.Rshort (X.g.L.stateOf u) ↔
      X.OddValid H C' X.Rshort (X.g.L.stateOf u) := by
  have hc := short_choices_congr_data X u H C C' hp ha ht ho
  have hd := actDesc_congr_choices X H H C C' (X.g.L.stateOf u) X.Rshort hc
  have htests := _root_.Lane_q_s06_loads.S3Tests_congr_data X H (X.g.L.stateOf u)
    (X.actDesc H C X.Rshort (X.g.L.stateOf u)) (X.tup C) (X.tup C')
    (fun e he => ho e (actDesc_obs_scope X u H C X.Rshort he))
  have hs : (∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u), (X.choice H C X.Rshort a).isSome) ↔
      (∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u), (X.choice H C' X.Rshort a).isSome) := by
    apply forall₂_congr
    intro a hab
    rw [hc a hab]
  have hl : (∃ j : Fin X.hp.H, ∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u), ∀ ℓ,
      X.choice H C X.Rshort a = some ℓ → ℓ.2 ∈ X.levelPair j) ↔
      (∃ j : Fin X.hp.H, ∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u), ∀ ℓ,
      X.choice H C' X.Rshort a = some ℓ → ℓ.2 ∈ X.levelPair j) := by
    apply exists_congr
    intro j
    apply forall₂_congr
    intro a hab
    rw [hc a hab]
  unfold Ctx6.OddValid
  rw [← hd, htests, hs, hl, hp]

theorem s3Post_congr_data (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty))
    (o o' : X.Data X.Loc) (ho : ∀ e ∈ D, o e = o' e) :
    X.s3Post H b D o = X.s3Post H b D o' := by
  unfold Ctx6.s3Post
  congr 1
  funext ξ
  exact _root_.Lane_q_s06_loads.s3Weight_congr_data X H b D o o' none ξ ho

theorem lowRow_congr_data (H : X.Hist) (P : X.Loc → Bool) (b : X.State)
    (D : Finset (X.Loc × X.Ty)) (o o' : X.Data X.Loc) (ho : ∀ e ∈ D, o e = o' e) :
    X.lowRow H P b D o = X.lowRow H P b D o' := by
  have hpres (ξ : Fin N) : X.presProb H P b D o ξ = X.presProb H P b D o' ξ := by
    unfold Ctx6.presProb
    congr 1
    funext ω
    apply propext
    unfold Ctx6.Presents
    apply and_congr Iff.rfl
    apply and_congr Iff.rfl
    apply forall₂_congr
    intro e he
    rw [ho e he]
  have hF (ξ : Fin N) : X.lowF H b D o ξ = X.lowF H b D o' ξ := by
    unfold Ctx6.lowF
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    rw [ho e he]
  have hQ : X.lowQ H b D o = X.lowQ H b D o' := by
    unfold Ctx6.lowQ
    apply Finset.prod_congr rfl
    intro e he
    rw [ho e he]
  have hW (ξ : Fin N) : X.adjWeight H P b D o ξ = X.adjWeight H P b D o' ξ := by
    unfold Ctx6.adjWeight Ctx6.table
    rw [hF ξ, hQ, hpres ξ]
  unfold Ctx6.lowRow
  simp_rw [hF, hW]
  rw [s3Post_congr_data X H b D o o' ho,
    show X.adjWeight H P b D o = X.adjWeight H P b D o' from funext hW]

theorem proxyRow_congr_data (H : X.Hist) (C C' : X.Centre) (u : CubeVertex n)
    (hp : X.pos C = X.pos C') (ha : X.act C = X.act C') (ht : X.ties C = X.ties C')
    (ho : TupleAgree X u C C') (y : Fin N) :
    X.proxyRow H C u y = X.proxyRow H C' u y := by
  have hc := short_choices_congr_data X u H C C' hp ha ht ho
  have hd := actDesc_congr_choices X H H C C' (X.g.L.stateOf u) X.Rshort hc
  have hv := oddValid_congr_data X u H C C' hp ha ht ho
  have hD : ∀ e ∈ X.actDesc H C X.Rshort (X.g.L.stateOf u), X.tup C e = X.tup C' e :=
    fun e he => ho e (actDesc_obs_scope X u H C X.Rshort he)
  unfold Ctx6.proxyRow Ctx6.oddRowAt
  rw [propext hv, ← hd]
  split
  · cases hm : X.stMode (X.g.L.stateOf u) with
    | low =>
      rw [hp, lowRow_congr_data X H (X.pos C') (X.g.L.stateOf u) _ _ _ hD]
    | high =>
      rw [s3Post_congr_data X H (X.g.L.stateOf u) _ _ _ hD]
  · rfl

end

end HypercubeRamsey.S06.Lane_sol_s06_hjoint
