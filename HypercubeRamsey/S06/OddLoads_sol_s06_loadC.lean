import HypercubeRamsey.S06.OddRows
import HypercubeRamsey.S06.OddLoads_sol_s06_loadA

namespace HypercubeRamsey.Lane_sol_s06_loadC

open OAI.HypercubeRamsey Classical
open HypercubeRamsey.S06
open scoped BigOperators
noncomputable section

/-- A reachable site stays in the consultation domain. -/
theorem reach_dom (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool)
    (E : p.EligMap) (q : CubeVertex p.d) (R : ℕ) {v : CubeVertex p.d} {j : ℕ}
    (h : p.Reach Sites P A E q R v j) : v ∈ Sites ∧ _root_.hammingDist (ι := Fin p.d) v q ≤ R := by
  induction h with
  | start v hv hd => exact ⟨hv, hd⟩
  | up v j hj h hb ih => exact ih
  | down v v' j h hv hd hdist ih => exact ⟨hv, hd⟩

/-- Height paths read only badness inside the declared consultation domain. -/
theorem reach_congr (p : HDParams) (Sites : p.Sites) (P A P' A' : p.Loc → Bool)
    (E E' : p.EligMap) (q : CubeVertex p.d) (R : ℕ)
    (hb : ∀ v ∈ Sites, _root_.hammingDist (ι := Fin p.d) v q ≤ R → ∀ j,
      p.Bad P A E v j ↔ p.Bad P' A' E' v j) (v : CubeVertex p.d) (j : ℕ) :
    p.Reach Sites P A E q R v j ↔ p.Reach Sites P' A' E' q R v j := by
  have forward (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
      (hb : ∀ v ∈ Sites, _root_.hammingDist (ι := Fin p.d) v q ≤ R → ∀ j,
        p.Bad P A E v j ↔ p.Bad P' A' E' v j)
      {v j} (h : p.Reach Sites P A E q R v j) :
      p.Reach Sites P' A' E' q R v j := by
    induction h with
    | start v hv hd => exact .start v hv hd
    | up v j hj h hbad ih =>
      obtain ⟨hv, hd⟩ := reach_dom p Sites P A E q R h
      obtain ⟨hj', hbad⟩ := hbad
      exact .up v j hj ih ⟨hj', (hb v hv hd ⟨j, hj'⟩).mp hbad⟩
    | down v v' j h hv hd hdist ih => exact .down v v' j ih hv hd hdist
  exact ⟨forward P A P' A' E E' hb,
    forward P' A' P A E' E (fun v hv hd j => (hb v hv hd j).symm)⟩

theorem height_congr (p : HDParams) (Sites : p.Sites) (P A P' A' : p.Loc → Bool)
    (E E' : p.EligMap) (q : CubeVertex p.d) (R : ℕ)
    (hb : ∀ v ∈ Sites, _root_.hammingDist (ι := Fin p.d) v q ≤ R → ∀ j,
      p.Bad P A E v j ↔ p.Bad P' A' E' v j) :
    p.height Sites P A E R q = p.height Sites P' A' E' R q := by
  unfold HDParams.height
  congr 1
  ext j
  simp only [Finset.mem_filter]
  rw [reach_congr p Sites P A P' A' E E' q R hb]

/-- Selection reads local badness, the queried eligible set, and one tie permutation. -/
theorem selection_congr (p : HDParams) (Sites : p.Sites) (P A P' A' : p.Loc → Bool)
    (E E' : p.EligMap) (τ τ' : p.Ties) (q : CubeVertex p.d) (R : ℕ)
    (hb : ∀ v ∈ Sites, _root_.hammingDist (ι := Fin p.d) v q ≤ R → ∀ j,
      p.Bad P A E v j ↔ p.Bad P' A' E' v j)
    (hbq : ∀ j, p.Bad P A E q j ↔ p.Bad P' A' E' q j)
    (he : ∀ j, E q j = E' q j)
    (ha : ∀ j ℓ, ℓ ∈ E q j → A ℓ = A' ℓ)
    (ht : ∀ j, τ (q, j) = τ' (q, j)) :
    p.selectionAt Sites P A E τ R q = p.selectionAt Sites P' A' E' τ' R q := by
  have hheight := height_congr p Sites P A P' A' E E' q R hb
  have hactive (j) : (E q j).filter (fun ℓ => A ℓ = true) =
      (E' q j).filter (fun ℓ => A' ℓ = true) := by
    rw [← he j]
    apply Finset.filter_congr
    intro ℓ hℓ
    rw [ha j ℓ hℓ]
  have hpriority (j) : (fun ℓ => p.priority τ (q, j) ℓ) =
      (fun ℓ => p.priority τ' (q, j) ℓ) := by
    funext ℓ
    unfold HDParams.priority
    rw [ht j]
  unfold HDParams.selectionAt
  simp only [hheight]
  split
  · rename_i hj
    simp only [show p.Bad P A E q ⟨p.height Sites P' A' E' R q, by omega⟩ =
      p.Bad P' A' E' q ⟨p.height Sites P' A' E' R q, by omega⟩ from propext (hbq _)]
    split
    · rfl
    · simp only [hactive, hpriority]
  · rfl

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-- Agreement on the four primitive arrays within a spatial ball. -/
def Agree (C C' : X.Centre) (q : CubeVertex X.hp.d) (R : ℕ) : Prop :=
  ∀ c : X.Loc, _root_.hammingDist (ι := Fin X.hp.d) c.1 q ≤ R →
    X.pos C c = X.pos C' c ∧ (∀ β, X.tup C (c, β) = X.tup C' (c, β)) ∧
      X.act C c = X.act C' c ∧ X.ties C c = X.ties C' c

/-- Shrink and recenter an agreement ball. -/
theorem Agree.recenter {C C' : X.Centre} {q q' : CubeVertex X.hp.d} {R R' : ℕ}
    (h : Agree X C C' q R) (hd : R' + _root_.hammingDist (ι := Fin X.hp.d) q' q ≤ R) :
    Agree X C C' q' R' := by
  intro c hc
  apply h c
  have ht := _root_.hammingDist_triangle (ι := Fin X.hp.d) c.1 q' q
  omega

theorem s3Weight_congr {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o o' : X.Data Id)
    (h : ∀ e ∈ D, o e = o' e) (drop : Option (Id × X.Ty)) (ξ : Fin N) :
    X.s3Weight H b D o drop ξ = X.s3Weight H b D o' drop ξ := by
  unfold Ctx6.s3Weight
  cases X.stMode b <;> dsimp only [Ctx6.lowWeight, Ctx6.highWeight]
  all_goals
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    rw [h e he]

theorem s3Mass_congr {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o o' : X.Data Id)
    (h : ∀ e ∈ D, o e = o' e) (drop : Option (Id × X.Ty)) :
    X.s3Mass H b D o drop = X.s3Mass H b D o' drop := by
  unfold Ctx6.s3Mass
  apply Finset.sum_congr rfl
  intro ξ hξ
  exact s3Weight_congr X H b D o o' h drop ξ

theorem s3Tests_congr {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o o' : X.Data Id)
    (h : ∀ e ∈ D, o e = o' e) : X.S3Tests H b D o ↔ X.S3Tests H b D o' := by
  unfold Ctx6.S3Tests
  simp_rw [s3Mass_congr X H b D o o' h]

theorem prosp_congr (P P' : X.Loc → Bool) (q : CubeVertex X.hp.d)
    (h : ∀ c, _root_.hammingDist (ι := Fin X.hp.d) c.1 q ≤ X.hp.r → P c = P' c) (l) :
    X.prosp P q l = X.prosp P' q l := by
  ext c
  simp only [Ctx6.prosp, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hd : _root_.hammingDist (ι := Fin X.hp.d) c.1 q ≤ X.hp.r
  · rw [h c hd]
  · simp [hd]

/-- A descriptor uses only the IDs permitted at its neighbouring sites. -/
theorem descsIn_mem (b : X.State) (perm : X.g.L.stNbr b → Finset X.Loc)
    {D : Finset (X.Loc × X.Ty)} (hD : D ∈ X.descsIn b perm)
    {e : X.Loc × X.Ty} (he : e ∈ D) :
    ∃ a : X.g.L.stNbr b, e.1 ∈ perm a := by
  obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hD
  have hperm := (Finset.mem_filter.mp hφ).2.1
  obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp he
  exact ⟨a, by simpa [← hae] using hperm a⟩

/-- All failure tests at an odd state read its neighbours' prospective balls. -/
theorem failedSets_congr (H : X.Hist) (C C' : X.Centre) (b : X.State)
    (q : CubeVertex X.hp.d) (d : ℕ)
    (hn : ∀ a ∈ X.g.L.stNbr b, _root_.hammingDist (ι := Fin X.hp.d) (X.site a) q ≤ d)
    (h : Agree X C C' q (X.hp.r + d)) (j) :
    X.failedSets H C b j = X.failedSets H C' b j := by
  have hp (a : X.g.L.stNbr b) (l) :
      X.prosp (X.pos C) (X.site a.1) l = X.prosp (X.pos C') (X.site a.1) l := by
    apply prosp_congr X
    intro c hc
    apply (h c ?_).1
    have ht := _root_.hammingDist_triangle (ι := Fin X.hp.d) c.1 (X.site a.1) q
    have hn := hn a.1 a.2
    omega
  have hperm : X.permAt (X.pos C) b j = X.permAt (X.pos C') b j := by
    funext a
    dsimp only [Ctx6.permAt]
    apply Finset.biUnion_congr rfl
    intro l hl
    exact hp a l
  have hdata {D : Finset (X.Loc × X.Ty)} (hD : D ∈ X.descsIn b (X.permAt (X.pos C) b j)) :
      ∀ e ∈ D, X.tup C e = X.tup C' e := by
    intro e he
    obtain ⟨a, hea⟩ := descsIn_mem X b _ hD he
    obtain ⟨l, hl, heball⟩ := Finset.mem_biUnion.mp hea
    have hc := (Finset.mem_filter.mp heball).2.2.2
    apply (h e.1 ?_).2.1 e.2
    have ht := _root_.hammingDist_triangle (ι := Fin X.hp.d) e.1.1 (X.site a.1) q
    have hn := hn a.1 a.2
    omega
  unfold Ctx6.failedSets
  congr 1
  rw [← hperm]
  apply Finset.filter_congr
  intro D hD
  unfold Ctx6.S3Fail
  rw [s3Tests_congr X H b D (X.tup C) (X.tup C') (hdata hD)]

/-- Marking at a site reads only a radius r+D ball around that site. -/
theorem marked_congr (H : X.Hist) (C C' : X.Centre) (q : CubeVertex X.hp.d)
    (h : Agree X C C' q (X.hp.r + D₀₆)) (l) :
    X.marked H C q l = X.marked H C' q l := by
  unfold Ctx6.marked
  apply Finset.biUnion_congr rfl
  intro b hb
  split_ifs with hq
  ·
    apply Finset.biUnion_congr rfl
    intro j hj
    have hn : ∀ a ∈ X.g.L.stNbr b, _root_.hammingDist (ι := Fin X.hp.d) (X.site a) q ≤ D₀₆ := by
      obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp hq
      intro a ha
      exact X.code.nbr_dist b a ha a₀ ha₀
    rw [failedSets_congr X H C C' b q D₀₆ hn h j]
  · rfl

/-- Eligibility always lies in the prospective radius-r ball. -/
theorem elig_mem (H : X.Hist) (C : X.Centre) (q : CubeVertex X.hp.d) (j)
    {c : X.Loc} (h : c ∈ X.elig H C q j) : _root_.hammingDist (ι := Fin X.hp.d) c.1 q ≤ X.hp.r :=
  (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2.2.2

theorem elig_congr (H : X.Hist) (C C' : X.Centre) (q : CubeVertex X.hp.d)
    (h : Agree X C C' q (X.hp.r + D₀₆)) (l) :
    X.elig H C q l = X.elig H C' q l := by
  unfold Ctx6.elig
  rw [marked_congr X H C C' q h l]
  rw [prosp_congr X (X.pos C) (X.pos C') q (fun c hc => (h c (by omega)).1) l]

/-- Badness reads local eligibility, positions and activations. -/
theorem bad_congr (H : X.Hist) (C C' : X.Centre) (q : CubeVertex X.hp.d)
    (h : Agree X C C' q (X.hp.r + D₀₆)) (j) :
    X.hp.Bad (X.pos C) (X.act C) (X.elig H C) q j ↔
      X.hp.Bad (X.pos C') (X.act C') (X.elig H C') q j := by
  have he := elig_congr X H C C' q h j
  unfold HDParams.Bad
  have hact : (∀ c ∈ X.elig H C q j, X.act C c = false) ↔
      (∀ c ∈ X.elig H C' q j, X.act C' c = false) := by
    rw [← he]
    apply forall₂_congr
    intro c hc
    rw [(h c (by have := elig_mem X H C q j hc; omega)).2.2.1]
  have hfilter : (Finset.univ.filter fun u : CubeVertex X.hp.d =>
      X.pos C (u, j) = true ∧ X.act C (u, j) = true ∧ _root_.hammingDist (ι := Fin X.hp.d) u q ≤ X.hp.r + X.hp.D) =
      (Finset.univ.filter fun u : CubeVertex X.hp.d =>
      X.pos C' (u, j) = true ∧ X.act C' (u, j) = true ∧ _root_.hammingDist (ι := Fin X.hp.d) u q ≤ X.hp.r + X.hp.D) := by
    ext u
    have hD : X.hp.D = D₀₆ := rfl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hD]
    by_cases hd : _root_.hammingDist (ι := Fin X.hp.d) u q ≤ X.hp.r + D₀₆
    · have hc := h (u, j) hd
      rw [hc.1, hc.2.2.1]
    · simp [hd]
  rw [hact, hfilter]

theorem self_dist (q : CubeVertex X.hp.d) :
    _root_.hammingDist (ι := Fin X.hp.d) q q = 0 :=
  _root_.hammingDist_self q

/-- Long or short selection at a site reads a radius R+r+D ball. -/
theorem choice_congr (H : X.Hist) (C C' : X.Centre) (a : X.State) (R : ℕ)
    (h : Agree X C C' (X.site a) (R + X.hp.r + D₀₆)) :
    X.choice H C R a = X.choice H C' R a := by
  have hself := self_dist X (X.site a)
  unfold Ctx6.choice
  apply selection_congr
  · intro v hv hd j
    apply bad_congr X H C C' v
    apply h.recenter X
    omega
  · intro j
    apply bad_congr X H C C' (X.site a)
    apply h.recenter X
    omega
  · intro j
    apply elig_congr X H C C' (X.site a)
    apply h.recenter X
    omega
  · intro j c hc
    apply (h c ?_).2.2.1
    have := elig_mem X H C (X.site a) j hc
    omega
  · intro j
    exact (h (X.site a, j) (by exact hself.le.trans (Nat.zero_le _))).2.2.2

theorem choice_mem (H : X.Hist) (C : X.Centre) (a : X.State) (R : ℕ) (c : X.Loc)
    (hs : X.choice H C R a = some c) : _root_.hammingDist (ι := Fin X.hp.d) c.1 (X.site a) ≤ X.hp.r := by
  unfold Ctx6.choice at hs
  dsimp only [HDParams.selectionAt] at hs
  split_ifs at hs with hj hbad hne
  all_goals try cases hs
  let j : Fin (X.hp.H + 1) := ⟨X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) R (X.site a), by omega⟩
  let active := (X.elig H C (X.site a) j).filter fun i => X.act C i = true
  let priorities := active.image fun i => X.hp.priority (X.ties C) (X.site a, j) i
  have hmem := Finset.mem_image.mp (Finset.min'_mem priorities hne)
  exact elig_mem X H C (X.site a) j (Finset.mem_filter.mp (Classical.choose_spec hmem).1).1

theorem actDesc_congr (H : X.Hist) (C C' : X.Centre) (b : X.State) (R d : ℕ)
    (q : CubeVertex X.hp.d)
    (hn : ∀ a ∈ X.g.L.stNbr b, _root_.hammingDist (ι := Fin X.hp.d) (X.site a) q ≤ d)
    (h : Agree X C C' q (R + X.hp.r + D₀₆ + d)) :
    X.actDesc H C R b = X.actDesc H C' R b := by
  unfold Ctx6.actDesc
  congr 1
  funext a
  rw [choice_congr X H C C' a.1 R (h.recenter X (by have := hn a.1 a.2; omega))]

theorem actDesc_mem_dist (H : X.Hist) (C : X.Centre) (b : X.State) (R d : ℕ)
    (q : CubeVertex X.hp.d)
    (hn : ∀ a ∈ X.g.L.stNbr b, _root_.hammingDist (ι := Fin X.hp.d) (X.site a) q ≤ d)
    (hs : ∀ a ∈ X.g.L.stNbr b, (X.choice H C R a).isSome)
    {e : X.Loc × X.Ty} (he : e ∈ X.actDesc H C R b) :
    _root_.hammingDist (ι := Fin X.hp.d) e.1.1 q ≤ X.hp.r + d := by
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp he
  cases hc : X.choice H C R a.1 with
  | none => have := hs a.1 a.2; simp [hc] at this
  | some c =>
    have hd := choice_mem X H C a.1 R c hc
    have ha := hn a.1 a.2
    have ht := _root_.hammingDist_triangle (ι := Fin X.hp.d) c.1 (X.site a.1) q
    have heq' : c = e.1 := by simpa [hc] using congrArg Prod.fst heq
    rw [← heq']
    omega

/-- Odd validity reads local choices, position counts, and the descriptor tuples. -/
theorem oddValid_congr (H : X.Hist) (C C' : X.Centre) (b : X.State) (R d : ℕ)
    (q : CubeVertex X.hp.d)
    (hn : ∀ a ∈ X.g.L.stNbr b, _root_.hammingDist (ι := Fin X.hp.d) (X.site a) q ≤ d)
    (h : Agree X C C' q (R + X.hp.r + D₀₆ + d)) :
    X.OddValid H C R b ↔ X.OddValid H C' R b := by
  have hchoice (a : X.State) (ha : a ∈ X.g.L.stNbr b) :
      X.choice H C R a = X.choice H C' R a :=
    choice_congr X H C C' a R (h.recenter X (by have := hn a ha; omega))
  have hsome : (∀ a ∈ X.g.L.stNbr b, (X.choice H C R a).isSome) ↔
      (∀ a ∈ X.g.L.stNbr b, (X.choice H C' R a).isSome) := by
    apply forall₂_congr
    intro a ha
    rw [hchoice a ha]
  by_cases hs : ∀ a ∈ X.g.L.stNbr b, (X.choice H C R a).isSome
  · have hs' := hsome.mp hs
    have hdesc := actDesc_congr X H C C' b R d q hn h
    have htests : X.S3Tests H b (X.actDesc H C R b) (X.tup C) ↔
        X.S3Tests H b (X.actDesc H C R b) (X.tup C') := by
      apply s3Tests_congr X
      intro e he
      exact (h e.1 (by have := actDesc_mem_dist X H C b R d q hn hs he; omega)).2.1 e.2
    have hcounts : (∀ a ∈ X.g.L.stNbr b, ∀ l,
        ((X.prosp (X.pos C) (X.site a) l).card : ℝ) ≤ 2 * X.hp.lam) ↔
        (∀ a ∈ X.g.L.stNbr b, ∀ l,
        ((X.prosp (X.pos C') (X.site a) l).card : ℝ) ≤ 2 * X.hp.lam) := by
      apply forall₂_congr
      intro a ha
      apply forall_congr'
      intro l
      rw [prosp_congr X (X.pos C) (X.pos C') (X.site a) (fun c hc =>
        (h.recenter X (show X.hp.r + _root_.hammingDist (ι := Fin X.hp.d) (X.site a) q ≤ R + X.hp.r + D₀₆ + d by
          have := hn a ha; omega) c hc).1) l]
    have hlevels : (∃ j : Fin X.hp.H, ∀ a ∈ X.g.L.stNbr b, ∀ c,
        X.choice H C R a = some c → c.2 ∈ X.levelPair j) ↔
        (∃ j : Fin X.hp.H, ∀ a ∈ X.g.L.stNbr b, ∀ c,
        X.choice H C' R a = some c → c.2 ∈ X.levelPair j) := by
      apply exists_congr
      intro j
      apply forall₂_congr
      intro a ha
      rw [hchoice a ha]
    unfold Ctx6.OddValid
    rw [← hdesc, ← htests, ← hcounts, ← hlevels]
    exact and_congr hsome Iff.rfl
  · have hs' : ¬ ∀ a ∈ X.g.L.stNbr b, (X.choice H C' R a).isSome := fun h' => hs (hsome.mpr h')
    exact ⟨fun hv => False.elim (hs hv.1), fun hv => False.elim (hs' hv.1)⟩

/-- Low-row tables see only local positions and the recorded descriptor entries. -/
theorem lowRow_congr (H : X.Hist) (P P' : X.Loc → Bool) (b : X.State)
    (D : Finset (X.Loc × X.Ty)) (o o' : X.Data X.Loc) (q : CubeVertex X.hp.d) (d : ℕ)
    (hn : ∀ a ∈ X.g.L.stNbr b, _root_.hammingDist (ι := Fin X.hp.d) (X.site a) q ≤ d)
    (hp : ∀ c, _root_.hammingDist (ι := Fin X.hp.d) c.1 q ≤ X.Rshort + X.hp.r + D₀₆ + d → P c = P' c)
    (ho : ∀ e ∈ D, o e = o' e) : X.lowRow H P b D o = X.lowRow H P' b D o' := by
  have hpres (ξ : Fin N) : X.presProb H P b D o ξ = X.presProb H P' b D o' ξ := by
    unfold Ctx6.presProb
    congr 1
    funext ω
    apply propext
    have ha : Agree X (X.assemble P ω) (X.assemble P' ω) q (X.Rshort + X.hp.r + D₀₆ + d) := by
      intro c hc
      exact ⟨hp c hc, fun β => rfl, rfl, rfl⟩
    have hv := oddValid_congr X (X.withHid H (X.tgt b) ξ) _ _ b X.Rshort d q hn ha
    have hd := actDesc_congr X (X.withHid H (X.tgt b) ξ) _ _ b X.Rshort d q hn ha
    have htuple : (∀ e ∈ D, X.tup (X.assemble P ω) e = o e) ↔
        (∀ e ∈ D, X.tup (X.assemble P' ω) e = o' e) := by
      apply forall₂_congr
      intro e he
      rw [ho e he]
      rfl
    unfold Ctx6.Presents
    rw [hv, hd, htuple]
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
  have hW (ξ : Fin N) : X.adjWeight H P b D o ξ = X.adjWeight H P' b D o' ξ := by
    unfold Ctx6.adjWeight Ctx6.table
    rw [hF ξ, hQ, hpres ξ]
  have hPost : X.s3Post H b D o = X.s3Post H b D o' := by
    unfold Ctx6.s3Post
    congr 1
    funext ξ
    exact s3Weight_congr X H b D o o' ho none ξ
  unfold Ctx6.lowRow
  simp_rw [hF, hW]
  rw [hPost, show X.adjWeight H P b D o = X.adjWeight H P' b D o' from funext hW]

theorem oddRowAt_congr (H : X.Hist) (C C' : X.Centre) (b : X.State) (R d : ℕ)
    (q : CubeVertex X.hp.d)
    (hn : ∀ a ∈ X.g.L.stNbr b, _root_.hammingDist (ι := Fin X.hp.d) (X.site a) q ≤ d)
    (hshort : X.Rshort ≤ R)
    (h : Agree X C C' q (R + X.hp.r + D₀₆ + d)) :
    X.oddRowAt H C R b = X.oddRowAt H C' R b := by
  have hv := oddValid_congr X H C C' b R d q hn h
  by_cases hvalid : X.OddValid H C R b
  · have hvalid' := hv.mp hvalid
    have hd := actDesc_congr X H C C' b R d q hn h
    have ho : ∀ e ∈ X.actDesc H C R b, X.tup C e = X.tup C' e := by
      intro e he
      exact (h e.1 (by have := actDesc_mem_dist X H C b R d q hn hvalid.1 he; omega)).2.1 e.2
    unfold Ctx6.oddRowAt
    rw [if_pos hvalid, if_pos hvalid', ← hd]
    cases hm : X.stMode b
    · change (X.lowRow H (X.pos C) b (X.actDesc H C R b) (X.tup C)).w =
        (X.lowRow H (X.pos C') b (X.actDesc H C R b) (X.tup C')).w
      rw [lowRow_congr X H (X.pos C) (X.pos C') b _ _ _ q d hn
        (fun c hc => (h c (by omega)).1) ho]
    · change (X.s3Post H b (X.actDesc H C R b) (X.tup C)).w =
        (X.s3Post H b (X.actDesc H C R b) (X.tup C')).w
      have hp : X.s3Post H b (X.actDesc H C R b) (X.tup C) =
          X.s3Post H b (X.actDesc H C R b) (X.tup C') := by
        unfold Ctx6.s3Post
        congr 1
        funext ξ
        exact s3Weight_congr X H b _ _ _ ho none ξ
      rw [hp]
  · have hvalid' : ¬ X.OddValid H C' R b := fun h' => hvalid (hv.mpr h')
    simp [Ctx6.oddRowAt, hvalid, hvalid']

/-- In a Section 6 context the short radius is below the long radius. -/
theorem short_le_long : X.Rshort ≤ X.Rlong := by
  obtain ⟨i, hi⟩ := X.g.L.residual_nonempty
  have hn : 1 ≤ n := by have := i.isLt; omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hα : α₆ p₀ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hm : X.m ≤ n := by
    change X.g.L.m ≤ n
    rw [X.g.m_eq]
    apply Nat.ceil_le.mpr
    simpa using Real.rpow_le_rpow_of_exponent_le hnR hα
  have hζ : ζ₆ (α₆ p₀) ≤ 1 / 2 := by
    have ha : α₆ p₀ ≤ 1 / 10 ^ 12 := min_le_left _ _
    unfold ζ₆
    linarith
  have htop : ⌈(n : ℝ) ^ (1 - ζ₆ (α₆ p₀))⌉₊ ≤ X.hp.H := by
    change ⌈(n : ℝ) ^ (1 - ζ₆ (α₆ p₀))⌉₊ ≤ topScale n (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀))
    unfold topScale
    exact Nat.find_spec (p := fun j : ℕ =>
      ⌈(n : ℝ) ^ (1 - ζ₆ (α₆ p₀))⌉₊ ≤
        (max 2 ⌈(n : ℝ) ^ σ₆ (α₆ p₀)⌉₊) ^ j * max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊) _
  have hroot : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (X.hp.H : ℝ) := by
    calc
      (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 - ζ₆ (α₆ p₀)) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
      _ ≤ (⌈(n : ℝ) ^ (1 - ζ₆ (α₆ p₀))⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ X.hp.H := by exact_mod_cast htop
  have hsquare : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = n := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    norm_num
  have hnH : n ≤ X.hp.H ^ 2 := by
    have hnonneg : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have : (n : ℝ) ≤ (X.hp.H : ℝ) ^ 2 := by nlinarith
    exact_mod_cast this
  have hs : Nat.sqrt X.m ≤ X.hp.H :=
    (Nat.sqrt_le_sqrt (hm.trans hnH)).trans (by rw [Nat.sqrt_eq'])
  change X.hp.D * Nat.sqrt X.m ≤ 2 * X.hp.D * X.hp.H
  nlinarith [Nat.mul_le_mul_left X.hp.D hs]


/-- A fixed coordinate supplies an adjacent even role for every odd role. -/
def pivot : Fin n := X.g.L.residual_nonempty.choose

def anchor (u : CubeVertex n) : CubeVertex n := cubeFlip u (pivot X)

def query (u : CubeVertex n) : CubeVertex X.hp.d := X.site (X.g.L.stateOf (anchor X u))

/-- The selection ball enlarged by the prospective radius and the neighbour diameter. -/
def rowRadius : ℕ := X.Rlong + X.hp.r + 2 * D₀₆

/-- Position, activation and tie coordinates in the row's spatial scope, at every level. -/
def rowLocScope (u : CubeVertex n) : Finset X.Loc :=
  Finset.univ.filter fun c => _root_.hammingDist c.1 (query X u) ≤ rowRadius X

/-- The tuple coordinates retain their types as separate product coordinates. -/
def rowTupleScope (u : CubeVertex n) : Finset (X.Loc × X.Ty) :=
  rowLocScope X u ×ˢ Finset.univ

/-- A radius shared with the eventual residual-neighbour counting estimate. -/
def separationRadius : ℕ := 2 * X.hp.r + 8 * X.hp.Rlong + 100

/-- The same coordinate flip on both roles preserves residual Hamming distance. -/
theorem anchor_residualDist (u v : CubeVertex n) :
    X.g.L.residualDist (anchor X u) (anchor X v) = X.g.L.residualDist u v := by
  unfold ChunkLayout6.residualDist
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro a _
  by_cases ha : a = pivot X
  · subst a
    simp [anchor, cubeFlip]
  · simp [anchor, cubeFlip, ha]

set_option maxHeartbeats 400000 in
/-- Every neighbouring even state lies within the code diameter of the anchor. -/
theorem neighbours_near_query (u : CubeVertex n) (hu : ¬ IsEvenRole u) :
    ∀ a ∈ X.g.L.stNbr (X.g.L.stateOf u),
      _root_.hammingDist (X.site a) (query X u) ≤ D₀₆ := by
  have ha : X.g.L.stateOf (anchor X u) ∈ X.g.L.stNbr (X.g.L.stateOf u) := by
    simp only [ChunkLayout6.stNbr, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, anchor X u, hu, (cubeFlip_parity u (pivot X)).mpr hu,
      rfl, rfl, cubeFlip_adj u (pivot X)⟩
  intro a ha'
  exact X.code.nbr_dist _ a ha' _ ha

/-- The long odd row reads only the four arrays in the declared spatial ball. -/
theorem oddRow_congr (H : X.Hist) (C C' : X.Centre) (u : CubeVertex n)
    (hu : ¬ IsEvenRole u) (h : Agree X C C' (query X u) (rowRadius X)) :
    X.oddRow H C u = X.oddRow H C' u := by
  apply oddRowAt_congr X H C C' (X.g.L.stateOf u) X.Rlong D₀₆ (query X u)
    (neighbours_near_query X u hu) (short_le_long X)
  simpa [rowRadius, two_mul, Nat.add_assoc] using h

/-- Zero on even roles, so moments can be taken over the full cube. -/
def rowTerm (H : X.Hist) (u : CubeVertex n) (y : Fin N) (C : X.Centre) : ℝ :=
  if IsEvenRole u then 0 else (N : ℝ) * X.oddRow H C u y

theorem rowTerm_congr (H : X.Hist) (u : CubeVertex n) (y : Fin N) (C C' : X.Centre)
    (h : Agree X C C' (query X u) (rowRadius X)) :
    rowTerm X H u y C = rowTerm X H u y C' := by
  by_cases hu : IsEvenRole u
  · simp [rowTerm, hu]
  · simp only [rowTerm, hu, ite_false]
    rw [oddRow_congr X H C C' u hu h]

theorem rowTerm_depends_position (H : X.Hist) (u : CubeVertex n) (y : Fin N)
    (O : X.Data X.Loc) (A : X.Loc → Bool) (τ : X.hp.Ties) :
    FinProb.DependsOn (fun P => rowTerm X H u y (((P, O), A), τ)) (rowLocScope X u) := by
  intro P P' hP
  apply rowTerm_congr X H u y
  intro c hc
  exact ⟨hP c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩), fun _ => rfl, rfl, rfl⟩

theorem rowTerm_depends_tuple (H : X.Hist) (u : CubeVertex n) (y : Fin N)
    (P : X.Loc → Bool) (A : X.Loc → Bool) (τ : X.hp.Ties) :
    FinProb.DependsOn (fun O => rowTerm X H u y (((P, O), A), τ)) (rowTupleScope X u) := by
  intro O O' hO
  apply rowTerm_congr X H u y
  intro c hc
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro β
  exact hO (c, β) (Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, Finset.mem_univ _⟩)

theorem rowTerm_depends_activation (H : X.Hist) (u : CubeVertex n) (y : Fin N)
    (P : X.Loc → Bool) (O : X.Data X.Loc) (τ : X.hp.Ties) :
    FinProb.DependsOn (fun A => rowTerm X H u y (((P, O), A), τ)) (rowLocScope X u) := by
  intro A A' hA
  apply rowTerm_congr X H u y
  intro c hc
  exact ⟨rfl, fun _ => rfl, hA c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩), rfl⟩

theorem rowTerm_depends_tie (H : X.Hist) (u : CubeVertex n) (y : Fin N)
    (P : X.Loc → Bool) (O : X.Data X.Loc) (A : X.Loc → Bool) :
    FinProb.DependsOn (fun τ => rowTerm X H u y (((P, O), A), τ)) (rowLocScope X u) := by
  intro τ τ' hτ
  apply rowTerm_congr X H u y
  intro c hc
  exact ⟨rfl, fun _ => rfl, rfl, hτ c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)⟩

/-- Residually separated roles have disjoint position, activation and tie scopes. -/
theorem rowLocScope_disjoint (u v : CubeVertex n)
    (hsep : separationRadius X < X.g.L.residualDist u v) :
    Disjoint (rowLocScope X u) (rowLocScope X v) := by
  apply Finset.disjoint_left.mpr
  intro c hc hc'
  have hc := (Finset.mem_filter.mp hc).2
  have hc' := (Finset.mem_filter.mp hc').2
  have ht := _root_.hammingDist_triangle (query X u) c.1 (query X v)
  rw [_root_.hammingDist_comm (query X u) c.1] at ht
  have hr : 2 * rowRadius X ≤ separationRadius X := by
    dsimp [rowRadius, separationRadius, Ctx6.Rlong]
    norm_num [D₀₆]
    omega
  have hres := X.code.residual_dist (anchor X u) (anchor X v)
  rw [anchor_residualDist X u v] at hres
  change X.g.L.residualDist u v ≤ _root_.hammingDist (query X u) (query X v) at hres
  omega

/-- The associated tuple scopes are disjoint, including their type coordinates. -/
theorem rowTupleScope_disjoint (u v : CubeVertex n)
    (hsep : separationRadius X < X.g.L.residualDist u v) :
    Disjoint (rowTupleScope X u) (rowTupleScope X v) := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  exact Finset.disjoint_left.mp (rowLocScope_disjoint X u v hsep)
    (Finset.mem_product.mp he).1 (Finset.mem_product.mp he').1

/-- The raw moment at separated roles is the product of their raw long means. -/
theorem rowTerm_expect_prod (H : X.Hist) (U : Finset (CubeVertex n)) (y : Fin N)
    (hsep : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → separationRadius X < X.g.L.residualDist u v) :
    (X.centreLaw H).expect (fun C => ∏ u ∈ U, rowTerm X H u y C) =
      ∏ u ∈ U, (X.centreLaw H).expect (rowTerm X H u y) := by
  apply Lane_sol_s06_loadA.centreLaw_expect_prod_of_scopes X H U
    (rowLocScope X) (rowTupleScope X) (rowLocScope X) (rowLocScope X)
    (fun u C => rowTerm X H u y C)
    (fun u O A τ => rowTerm_depends_position X H u y O A τ)
    (fun u P A τ => rowTerm_depends_tuple X H u y P A τ)
    (fun u P O τ => rowTerm_depends_activation X H u y P O τ)
    (fun u P O A => rowTerm_depends_tie X H u y P O A)
  · intro u hu v hv hne
    exact rowLocScope_disjoint X u v (hsep u hu v hv hne)
  · intro u hu v hv hne
    exact rowTupleScope_disjoint X u v (hsep u hu v hv hne)
  · intro u hu v hv hne
    exact rowLocScope_disjoint X u v (hsep u hu v hv hne)
  · intro u hu v hv hne
    exact rowLocScope_disjoint X u v (hsep u hu v hv hne)

end
end HypercubeRamsey.Lane_sol_s06_loadC
