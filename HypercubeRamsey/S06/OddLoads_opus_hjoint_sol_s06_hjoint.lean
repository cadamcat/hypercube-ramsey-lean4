import HypercubeRamsey.S06.OddLoads_sol_s06_loadB

namespace HypercubeRamsey.S06.Lane_sol_s06_hjoint

open OAI.HypercubeRamsey Classical
open scoped BigOperators

noncomputable section

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
  {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

theorem reach_domain (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool)
    (elig : p.EligMap) (q : CubeVertex p.d) (R : ℕ) {v : CubeVertex p.d} {j : ℕ}
    (h : p.Reach Sites P A elig q R v j) :
    v ∈ Sites ∧ _root_.hammingDist v q ≤ R := by
  induction h with
  | start v hv hd => exact ⟨hv, hd⟩
  | up v j hj h hb ih => exact ih
  | down v v' j h hv hd hdist ih => exact ⟨hv, hd⟩

theorem nbr_represented (b a : X.State) (ha : a ∈ X.g.L.stNbr b) :
    ∃ x : CubeVertex n, X.g.L.stateOf x = a := by
  simp only [ChunkLayout6.stNbr, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨u, v, _, _, _, hv, _⟩ := ha
  exact ⟨v, hv⟩

theorem even_represented (a : X.State) (ha : a ∈ X.g.L.evenStates) :
    ∃ x : CubeVertex n, X.g.L.stateOf x = a := by
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp ha
  exact ⟨x, hx⟩

theorem consulted_site_sign (u : CubeVertex n) (a : X.State)
    (ha : a ∈ X.g.L.stNbr (X.g.L.stateOf u))
    (v : CubeVertex X.code.d) (hv : v ∈ X.sites)
    (hd : _root_.hammingDist v (X.site a) ≤ X.Rshort) :
    ∃ a₂ ∈ X.g.L.evenStates, v = X.site a₂ ∧
      _root_.hammingDist (X.g.L.stSign a₂) (X.g.L.sign u) ≤ X.Rshort + 1 := by
  obtain ⟨a₂, ha₂, hv⟩ := Finset.mem_image.mp hv
  obtain ⟨x, hx⟩ := even_represented X a₂ ha₂
  obtain ⟨y, hy⟩ := nbr_represented X (X.g.L.stateOf u) a ha
  have hcode : _root_.hammingDist (X.g.L.stSign a₂) (X.g.L.stSign a) ≤
      _root_.hammingDist (X.site a₂) (X.site a) := by
    convert X.code.sign_dist x y using 1 <;>
      simp only [hx, hy, Ctx6.site, HypercubeRamsey.hammingDist,
        _root_.hammingDist]
    congr 1
  have hn := _root_.HypercubeRamsey.Lane_q_s06_loads.ctx6_stNbr_sign_dist_le_one
    X (X.g.L.stateOf u) a ha
  rw [X.facts.sign_eq u, _root_.hammingDist_comm] at hn
  refine ⟨a₂, ha₂, hv.symm, ?_⟩
  have ht := _root_.hammingDist_triangle (X.g.L.stSign a₂)
    (X.g.L.stSign a) (X.g.L.sign u)
  rw [← hv] at hd
  omega

theorem short_reach_sign (u : CubeVertex n) (H : X.Hist) (C : X.Centre)
    (a : X.State) (ha : a ∈ X.g.L.stNbr (X.g.L.stateOf u))
    {v : CubeVertex X.code.d} {j : ℕ}
    (h : X.hp.Reach X.sites (X.pos C) (X.act C) (X.elig H C)
      (X.site a) X.Rshort v j) :
    ∃ a₂ ∈ X.g.L.evenStates, v = X.site a₂ ∧
      _root_.hammingDist (X.g.L.stSign a₂) (X.g.L.sign u) ≤ X.Rshort + 1 := by
  obtain ⟨hv, hd⟩ := reach_domain X.hp X.sites (X.pos C) (X.act C) (X.elig H C)
    (X.site a) X.Rshort h
  exact consulted_site_sign X u a ha v hv hd

theorem incident_star_sign (u : CubeVertex n) (a₂ b₂ : X.State)
    (hnear : _root_.hammingDist (X.g.L.stSign a₂) (X.g.L.sign u) ≤ X.Rshort + 1)
    (ha₂ : a₂ ∈ X.g.L.stNbr b₂) :
    _root_.hammingDist (X.g.L.stSign b₂) (X.g.L.sign u) ≤ X.Rshort + 2 := by
  have hn := _root_.HypercubeRamsey.Lane_q_s06_loads.ctx6_stNbr_sign_dist_le_one
    X b₂ a₂ ha₂
  have ht := _root_.hammingDist_triangle (X.g.L.stSign b₂)
    (X.g.L.stSign a₂) (X.g.L.sign u)
  omega

theorem stType_obs_dist (a : X.State) (ℓ : X.HKey) (hℓ : ℓ ∈ (X.stType a).obs) :
    _root_.hammingDist (X.g.L.stSign a) ℓ.2 ≤ 1 := by
  exact (_root_.Lane_q_s06_loads.makeType6_obs_scope binAdjacent6
    (X.g.L.stKey a) (X.g.L.stSign a) (X.g.L.stFlippable a)
    (X.g.L.stSeverity a) X.J ℓ (by
      simpa [Ctx6.stType, ChunkLayout6.stType] using hℓ)).2

theorem nbr_type_obs_dist (b a : X.State) (ha : a ∈ X.g.L.stNbr b)
    (ℓ : X.HKey) (hℓ : ℓ ∈ (X.stType a).obs) :
    _root_.hammingDist (X.g.L.stSign b) ℓ.2 ≤ 2 := by
  have hn := _root_.HypercubeRamsey.Lane_q_s06_loads.ctx6_stNbr_sign_dist_le_one
    X b a ha
  have ho := stType_obs_dist X a ℓ hℓ
  have ht := _root_.hammingDist_triangle (X.g.L.stSign b) (X.g.L.stSign a) ℓ.2
  omega

theorem descsIn_type {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (perm : X.g.L.stNbr b → Finset Id)
    {D : Finset (Id × X.Ty)} (hD : D ∈ X.descsIn b perm)
    {e : Id × X.Ty} (he : e ∈ D) :
    ∃ a ∈ X.g.L.stNbr b, e.2 = X.stType a := by
  obtain ⟨φ, _, rfl⟩ := Finset.mem_image.mp hD
  obtain ⟨a, _, hea⟩ := Finset.mem_image.mp he
  exact ⟨a.1, a.2, congrArg Prod.snd hea.symm⟩

theorem actDesc_type (H : X.Hist) (C : X.Centre) (R : ℕ) (b : X.State)
    {e : X.Loc × X.Ty} (he : e ∈ X.actDesc H C R b) :
    ∃ a ∈ X.g.L.stNbr b, e.2 = X.stType a := by
  obtain ⟨a, _, hea⟩ := Finset.mem_image.mp he
  exact ⟨a.1, a.2, congrArg Prod.snd hea.symm⟩

theorem star_obs_bound (u : CubeVertex n) (b : X.State) (r : ℕ)
    (hb : _root_.hammingDist (X.g.L.stSign b) (X.g.L.sign u) ≤ r)
    {β : X.Ty} (hβ : ∃ a ∈ X.g.L.stNbr b, β = X.stType a)
    {ℓ : X.HKey} (hℓ : ℓ ∈ β.obs) :
    _root_.hammingDist ℓ.2 (X.g.L.sign u) ≤ r + 2 := by
  obtain ⟨a, ha, rfl⟩ := hβ
  have ho := nbr_type_obs_dist X b a ha ℓ hℓ
  rw [_root_.hammingDist_comm] at ho
  have ht := _root_.hammingDist_triangle ℓ.2 (X.g.L.stSign b) (X.g.L.sign u)
  omega

theorem consulted_star_obs (u : CubeVertex n) (a a₂ b₂ : X.State)
    (ha : a ∈ X.g.L.stNbr (X.g.L.stateOf u))
    (ha₂ : a₂ ∈ X.g.L.evenStates)
    (hd : _root_.hammingDist (X.site a₂) (X.site a) ≤ X.Rshort)
    (hab : a₂ ∈ X.g.L.stNbr b₂)
    {β : X.Ty} (hβ : ∃ a₃ ∈ X.g.L.stNbr b₂, β = X.stType a₃)
    {ℓ : X.HKey} (hℓ : ℓ ∈ β.obs) :
    _root_.hammingDist ℓ.2 (X.g.L.sign u) ≤ X.Rshort + 4 := by
  have hsite : X.site a₂ ∈ X.sites := Finset.mem_image.mpr ⟨a₂, ha₂, rfl⟩
  obtain ⟨a', ha', heq, hnear⟩ := consulted_site_sign X u a ha (X.site a₂) hsite hd
  obtain ⟨x, hx⟩ := even_represented X a₂ ha₂
  obtain ⟨y, hy⟩ := even_represented X a' ha'
  have haa : a₂ = a' := by
    have hxy := X.code.enc_injective x y (by
      simpa only [hx, hy, Ctx6.site] using heq)
    simpa only [hx, hy] using hxy
  rw [← haa] at hnear
  exact star_obs_bound X u b₂ (X.Rshort + 2)
    (incident_star_sign X u a₂ b₂ hnear hab) hβ hℓ

theorem consulted_incident_star_sign (u : CubeVertex n) (a : X.State)
    (ha : a ∈ X.g.L.stNbr (X.g.L.stateOf u))
    (v : CubeVertex X.code.d)
    (hd : _root_.hammingDist v (X.site a) ≤ X.Rshort)
    (b : X.State) (hv : v ∈ (X.g.L.stNbr b).image X.site) :
    _root_.hammingDist (X.g.L.stSign b) (X.g.L.sign u) ≤ X.Rshort + 2 := by
  obtain ⟨a₂, ha₂, heq⟩ := Finset.mem_image.mp hv
  obtain ⟨x, hx⟩ := nbr_represented X b a₂ ha₂
  obtain ⟨y, hy⟩ := nbr_represented X (X.g.L.stateOf u) a ha
  have hcode : _root_.hammingDist (X.g.L.stSign a₂) (X.g.L.stSign a) ≤
      _root_.hammingDist v (X.site a) := by
    simpa only [hx, hy, ← heq, Ctx6.site, HypercubeRamsey.hammingDist,
      _root_.hammingDist] using X.code.sign_dist x y
  have hn := _root_.HypercubeRamsey.Lane_q_s06_loads.ctx6_stNbr_sign_dist_le_one
    X (X.g.L.stateOf u) a ha
  rw [X.facts.sign_eq u, _root_.hammingDist_comm] at hn
  have ht := _root_.hammingDist_triangle (X.g.L.stSign a₂)
    (X.g.L.stSign a) (X.g.L.sign u)
  apply incident_star_sign X u a₂ b (by omega) ha₂

theorem star_obs_scope (u : CubeVertex n) (b : X.State)
    (hb : _root_.hammingDist (X.g.L.stSign b) (X.g.L.sign u) ≤ X.Rshort + 2)
    {β : X.Ty} (hβ : ∃ a ∈ X.g.L.stNbr b, β = X.stType a) :
    β.obs ⊆ Finset.univ.filter
      (fun ℓ : X.HKey => _root_.hammingDist ℓ.2 (X.g.L.sign u) ≤ X.Rshort + 6) := by
  intro ℓ hℓ
  have hd := star_obs_bound X u b (X.Rshort + 2) hb hβ hℓ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩

theorem descsIn_obs_scope {Id : Type} [Fintype Id] [DecidableEq Id]
    (u : CubeVertex n) (b : X.State)
    (hb : _root_.hammingDist (X.g.L.stSign b) (X.g.L.sign u) ≤ X.Rshort + 2)
    (perm : X.g.L.stNbr b → Finset Id)
    {D : Finset (Id × X.Ty)} (hD : D ∈ X.descsIn b perm)
    {e : Id × X.Ty} (he : e ∈ D) :
    e.2.obs ⊆ Finset.univ.filter
      (fun ℓ : X.HKey => _root_.hammingDist ℓ.2 (X.g.L.sign u) ≤ X.Rshort + 6) :=
  star_obs_scope X u b hb (descsIn_type X b perm hD he)

theorem actDesc_obs_scope (u : CubeVertex n) (H : X.Hist) (C : X.Centre) (R : ℕ)
    {e : X.Loc × X.Ty} (he : e ∈ X.actDesc H C R (X.g.L.stateOf u)) :
    e.2.obs ⊆ Finset.univ.filter
      (fun ℓ : X.HKey => _root_.hammingDist ℓ.2 (X.g.L.sign u) ≤ X.Rshort + 6) := by
  apply star_obs_scope X u (X.g.L.stateOf u) ?_
    (actDesc_type X H C R (X.g.L.stateOf u) he)
  rw [X.facts.sign_eq u, _root_.hammingDist_self]
  exact Nat.zero_le _

theorem target_scope (u : CubeVertex n) (b : X.State)
    (hb : _root_.hammingDist (X.g.L.stSign b) (X.g.L.sign u) ≤ X.Rshort + 2) :
    X.tgt b ∈ Finset.univ.filter
      (fun ℓ : X.HKey => _root_.hammingDist ℓ.2 (X.g.L.sign u) ≤ X.Rshort + 6) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change _root_.hammingDist (X.g.L.stSign b) (X.g.L.sign u) ≤ X.Rshort + 6
  omega

end

end HypercubeRamsey.S06.Lane_sol_s06_hjoint
