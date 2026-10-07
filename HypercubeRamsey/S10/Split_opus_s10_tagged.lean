import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k
import HypercubeRamsey.S10.Split_opus_s10_tagged_q_s10_d4

/-!
# Section 10: the global experiment and the split of the construction (TeX 10:23–262)

`Lane_opus_s10_row.tagged_of_menu` asks for a `TaggedSystem` from the patch menu
and the initial discrepancy. This file

* **d1** defines the global experiment completely (P10.1b, 10:43–54, 10:101–117,
  10:128–153, 10:188–250): parameters, slices and projected sites (reusing the
  p-s10-1k geometry), per-slice height devices, IDs, tuple arrays, masks,
  hypothetical lists and the fixed-list test, the greedy maximal disjoint family
  of failed lists, eligibility, height selection, realized lists, group validity,
  restricted squared-tilt cluster laws, label laws, odd rows, the even
  sublikelihood, the deletion reference, the predictive test and the normalized
  light-part even rows, comparison means, near relations and caps;
* states **d2–d10** as sub-lemmas about these objects;
* is imported by `Split_opus_s10_row.lean`, whose `tagged_of_menu` is assembled
  from them.

The mask strategy is a parameter of the experiment (`MaskStrategy`); d4 proves
that a good one exists (10:153).
-/

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1000000

namespace HypercubeRamsey.Lane_opus_s10_tagged

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-! ## Menu data -/

/-- The finite patch menu (same fields as `Lane_opus_s10_row.PatchMenu`). -/
structure MenuData (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (G : Colour) (ζ δ κ : ℝ) where
  I : Type
  [fI : Fintype I]
  [dI : DecidableEq I]
  [neI : Nonempty I]
  μ : I → Law N
  K : I → ℕ
  lam : (i : I) → Fin (K i) → ℝ
  D : (i : I) → Fin (K i) → Law N
  μ_support : ∀ i, (μ i).SupportedIn X
  D_support : ∀ i j, (D i j).SupportedIn Y
  lam_nonneg : ∀ i j, 0 ≤ lam i j
  lam_sum : ∀ i, ∑ j, lam i j = 1
  μ_width : ∀ i, (μ i).WidthLE ((n : ℝ) ^ δ)
  ν_width : ∀ i y, ∑ j, lam i j * (D i j).w y ≤ Real.exp ((n : ℝ) ^ δ) / N
  D_atom : ∀ i j y, (D i j).w y ≤ Real.exp (-(n : ℝ) ^ ζ)
  codegree : ∀ i j, 0 < lam i j → ∀ y y', 0 < (D i j).w y → 0 < (D i j).w y' →
    1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G (μ i) y y'
  avoid : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
    ∃ i, (∀ x ∈ RX, (μ i).w x = 0) ∧ ∀ y ∈ RY, ∑ j, lam i j * (D i j).w y = 0

attribute [instance] MenuData.fI MenuData.dI MenuData.neI

/-! ## Parameters (10:26, 10:43–48, 10:124) -/

section Params

variable (n : ℕ) (δ : ℝ)

/-- Number of special bits `m = ⌊n^{200δ}⌋`, capped by `n` so that the slice
split is always defined. -/
noncomputable def mS : ℕ := min (p10_1kSpecialCount n δ) n

theorem mS_le : mS n δ ≤ n := min_le_right _ _

/-- Tuple length `k = ⌈n^{300δ}⌉`. -/
noncomputable abbrev kT : ℕ := p10_1kTupleListLength n δ

/-- Own-fan bound `T = ⌈n^{141δ}⌉`. -/
noncomputable abbrev TT : ℕ := p10_1kHeightCount n δ

/-- The per-slice height device (`r = ⌊n^{1-10δ}⌋`, `λ = n^{10}`, step bound 6). -/
noncomputable abbrev hp : HDParams := p10_1kHeightParams n (mS n δ) δ

/-- The codegree gain `a = n^{-δ}`. -/
noncomputable def aG : ℝ := (n : ℝ) ^ (-δ)

/-- Slices: words on the special coordinates. -/
abbrev Slice := Fin (mS n δ) → Bool

/-- Projected sites: a slice and a residual word. -/
abbrev Site := P10_1kProjectedSite n (mS n δ)

/-- Center IDs: a slice, a residual location and a level. -/
abbrev ID := P10_1kProspectiveId n (mS n δ) δ

/-- The local radius `R_loc = 4r + 40H + 40⌈log₂ n⌉` (10:124). -/
noncomputable def Rloc : ℕ := 4 * (hp n δ).r + 40 * (hp n δ).H + 40 * (Nat.log 2 n + 1)

end Params

/-- Odd and even roles. -/
abbrev OddRole (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}
abbrev EvenRole (n : ℕ) := {v : CubeVertex n // IsEvenRole v}

/-- Odd neighbours of an even role. -/
noncomputable def starOf {n : ℕ} (a : EvenRole n) : Finset (OddRole n) :=
  Finset.univ.filter fun b => (cube n).Adj a.1 b.1

/-- The projected group of an odd role. -/
noncomputable def groupOf {n : ℕ} (δ : ℝ) (b : OddRole n) : Site n δ :=
  p10_1kProjectedVertex (mS_le n δ) b.1

/-- The projected site of an even role. -/
noncomputable def evenSite {n : ℕ} (δ : ℝ) (a : EvenRole n) : Site n δ :=
  p10_1kProjectedVertex (mS_le n δ) a.1

/-- A projected site is an odd group when some odd role projects to it. -/
def IsGroup {n : ℕ} (δ : ℝ) (q : Site n δ) : Prop :=
  (p10_1kOddGroupRoles (mS_le n δ) q).Nonempty

/-- Even projected sites of a slice (the height device's site set). -/
noncomputable def sliceSites {n : ℕ} (δ : ℝ) (z : Slice n δ) : (hp n δ).Sites :=
  p10_1kProjectedEvenSites (mS_le n δ) z

/-- Incident even sites of a group: even projected sites in its envelope
(one special flip, or residual distance at most 3). -/
noncomputable def incidentSites {n : ℕ} (δ : ℝ) (q : Site n δ) : Finset (Site n δ) :=
  (p10_1kProjectedNeighborEnvelope q).filter fun s => s.2 ∈ sliceSites δ s.1

/-! ## Finite-law utilities -/

/-- Normalize a nonnegative weight with positive total. -/
noncomputable def normalizeLaw {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hpos : 0 < ∑ a, w a) : FinProb α where
  w a := w a / ∑ b, w b
  nonneg a := div_nonneg (hw a) hpos.le
  sum_eq_one := by rw [← Finset.sum_div]; exact div_self hpos.ne'

/-- Restriction of a law to a set of positive mass, and the law itself otherwise. -/
noncomputable def restrictOrSelf {N : ℕ} (D : Law N) (F : Finset (Fin N)) : Law N :=
  if h : 0 < lawMassOn D F then Law.restrict D F h else D

/-- Greedy maximal pairwise disjoint subfamily (as the union of its members),
scanning a fixed list (10:102). -/
def greedyUnion {α : Type*} [DecidableEq α] : List (Finset α) → Finset α → Finset α
  | [], used => used
  | L :: rest, used => if Disjoint L used then greedyUnion rest (used ∪ L) else greedyUnion rest used

/-! ## d1: the experiment (P10.1b) -/

section Experiment

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour}
  {ζ δ κ : ℝ} (M : MenuData n N E X Y G ζ δ κ)

/-- The cluster prior of tag `i`. -/
noncomputable def prior (i : M.I) : FinProb (Fin (M.K i)) :=
  ⟨M.lam i, M.lam_nonneg i, M.lam_sum i⟩

/-- Clusters giving mask `S` mass at least `1/2` (10:50). -/
noncomputable def keptClusters (i : M.I) (S : Finset (Fin N)) : Finset (Fin (M.K i)) :=
  Finset.univ.filter fun j => (1 / 2 : ℝ) ≤ lawMassOn (M.D i j) S

/-- A permitted (non-trivial) mask: its kept clusters carry prior mass at least `1/2`. -/
def Permitted (i : M.I) (S : Finset (Fin N)) : Prop :=
  (1 / 2 : ℝ) ≤ (prior M i).pr (fun j => j ∈ keptClusters M i S)

/-- The masked cluster prior: conditioned on the kept clusters for a permitted
mask, the original prior otherwise (the trivial mask). -/
noncomputable def maskedPrior (i : M.I) (S : Finset (Fin N)) : FinProb (Fin (M.K i)) :=
  if h : Permitted M i S then
    (prior M i).cond (fun j => j ∈ keptClusters M i S)
      (lt_of_lt_of_le (by norm_num) h)
  else prior M i

/-- The masked cluster: a kept cluster of a permitted mask is conditioned on `S`. -/
noncomputable def maskedCluster (i : M.I) (S : Finset (Fin N)) (j : Fin (M.K i)) : Law N :=
  if Permitted M i S ∧ j ∈ keptClusters M i S then restrictOrSelf (M.D i j) S else M.D i j

/-- A mask strategy: for each tag assignment, a mask law at every projected site
(10:50, 10:153). -/
abbrev MaskStrategy := (Slice n δ → M.I) → Site n δ → FinProb (Finset (Fin N))

/-- A pre-cluster history: positions, tuple arrays, masks, activations, ties
(10:52). -/
abbrev History (n N : ℕ) (δ : ℝ) :=
  ((((ID n δ → Bool) × (ID n δ → Fin (kT n δ) → Fin N)) × (Site n δ → Finset (Fin N))) ×
    (ID n δ → Bool)) × (ID n δ → (hp n δ).TiePerm)

/-- The history type is finite (named so that importers need not re-synthesize it). -/
noncomputable instance historyFintype (n N : ℕ) (δ : ℝ) : Fintype (History n N δ) := by
  unfold History; infer_instance

/-- Cluster configurations over all sites form a finite type. -/
noncomputable instance clusterConfigFintype {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {G : Colour} {ζ δ κ : ℝ} (M : MenuData n N E X Y G ζ δ κ) :
    Fintype (Site n δ → (Σ i : M.I, Fin (M.K i))) := by
  infer_instance

namespace History
variable {n N : ℕ} {δ : ℝ} (h : History n N δ)
def pos : ID n δ → Bool := h.1.1.1.1
def tup : ID n δ → Fin (kT n δ) → Fin N := h.1.1.1.2
def mask : Site n δ → Finset (Fin N) := h.1.1.2
def act : ID n δ → Bool := h.1.2
def tie : ID n δ → (hp n δ).TiePerm := h.2
/-- Replace the tuple at one ID (10:191). -/
noncomputable def setTuple (c : ID n δ) (w : Fin (kT n δ) → Fin N) : History n N δ :=
  ((((h.pos, Function.update h.tup c w), h.mask), h.act), h.tie)
end History

/-- The history law at tags `t` (10:48–52): independent positions, tuple arrays
`W_c ∼ μ_{t z}^{⊗k}`, masks from the strategy, activations and ties. -/
noncomputable def historyLaw (σ : MaskStrategy M) (t : Slice n δ → M.I) :
    FinProb (History n N δ) :=
  ((((p10_1kGlobalPositionLaw n (mS n δ) δ).prod
      (p10_1kGlobalTupleArrayLaw (k := kT n δ) n (mS n δ) δ (fun z => M.μ (t z)))).prod
    (FinProb.pi (fun q => σ t q))).prod
    (p10_1kGlobalActivationLaw n (mS n δ) δ)).prod (p10_1kGlobalTieLaw n (mS n δ) δ)

variable (t : Slice n δ → M.I)

/-- Present IDs in the incident site balls of a group, at all levels (10:102). -/
noncomputable def candidates (h : History n N δ) (q : Site n δ) : Finset (ID n δ) :=
  p10_1kGroupPositionCandidates δ q h.pos

/-- Hypothetical lists of the prescribed form: at most `T` own-slice IDs and
exactly one ID from each adjacent slice (10:57). -/
noncomputable def lists (h : History n N δ) (q : Site n δ) : Finset (Finset (ID n δ)) :=
  (candidates h q).powerset.filter fun L =>
    (L.filter fun c => c.1 = q.1).card ≤ TT n δ ∧
    (∀ c ∈ L, c.1 = q.1 ∨ hammingDist c.1 q.1 = 1) ∧
    ∀ z' : Slice n δ, hammingDist z' q.1 = 1 → (L.filter fun c => c.1 = z').card = 1

/-- The fixed-list test (10.1) for list `L` at group `q`, under the masked
cluster mixture of `q`'s tag and mask (10:56–68). -/
def listFails (h : History n N δ) (q : Site n δ) (L : Finset (ID n δ)) : Prop :=
  fixedListFailure E G (maskedPrior M (t q.1) (h.mask q)) (maskedCluster M (t q.1) (h.mask q))
    (fun b => M.μ (t (L.equivFin.symm b).1.1)) (aG n δ)
    (fun b => h.tup (L.equivFin.symm b).1)

/-- IDs of a greedy maximal disjoint family of failed lists at a group (10:102). -/
noncomputable def forbidden (h : History n N δ) (q : Site n δ) : Finset (ID n δ) :=
  if IsGroup δ q then
    greedyUnion ((lists h q).filter (listFails M t h q)).toList ∅
  else ∅

/-- Eligibility in slice `z`: present IDs in the radius-`r` ball at the level,
minus IDs forbidden by a group whose envelope contains the site (10:102). -/
noncomputable def elig (h : History n N δ) (z : Slice n δ) : (hp n δ).EligMap :=
  fun v j => (p10_1kHeightEligibleIds (hp n δ) (fun loc => h.pos (z, loc)) v j).filter
    fun loc => ∀ q : Site n δ, (z, v) ∈ p10_1kProjectedNeighborEnvelope q →
      (z, loc) ∉ forbidden M t h q

/-- The height rule in each slice (10:115, Lemma 3.8): the selected center at a
projected site. -/
noncomputable def selected (h : History n N δ) (s : Site n δ) : Option (hp n δ).Loc :=
  (hp n δ).selection (sliceSites δ s.1) (fun loc => h.pos (s.1, loc))
    (fun loc => h.act (s.1, loc)) (elig M t h s.1) (fun loc => h.tie (s.1, loc)) s.2

/-- The realized list of a group: the IDs selected at its incident sites (10:54). -/
noncomputable def realizedList (h : History n N δ) (q : Site n δ) : Finset (ID n δ) :=
  (incidentSites δ q).biUnion fun s => (selected M t h s).elim ∅ (fun loc => {(s.1, loc)})

/-- Common hits of the realized list, and with one ID deleted. -/
noncomputable def hitSet (h : History n N δ) (q : Site n δ) : Finset (Fin N) :=
  Finset.univ.filter fun y => ∀ c ∈ realizedList M t h q, ∀ i, Hits E G (h.tup c i) y

noncomputable def hitSetWithout (h : History n N δ) (q : Site n δ) (c' : ID n δ) :
    Finset (Fin N) :=
  Finset.univ.filter fun y => ∀ c ∈ realizedList M t h q, c ≠ c' → ∀ i, Hits E G (h.tup c i) y

/-- Clusters passing the absolute-mass and deletion-ratio restrictions of the
squared tilt (10:131–136). -/
noncomputable def tiltKept (h : History n N δ) (q : Site n δ) : Finset (Fin (M.K (t q.1))) :=
  Finset.univ.filter fun j =>
    Real.exp (-(3 / 2 : ℝ) * kT n δ * (realizedList M t h q).card) ≤
        lawMassOn (maskedCluster M (t q.1) (h.mask q) j) (hitSet M t h q) ∧
    ∀ c ∈ realizedList M t h q,
      (if c.1 = q.1 then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) * kT n δ)
        else Real.exp (-(6 / 5 : ℝ) * kT n δ)) *
          lawMassOn (maskedCluster M (t q.1) (h.mask q) j) (hitSetWithout M t h q c) ≤
        lawMassOn (maskedCluster M (t q.1) (h.mask q) j) (hitSet M t h q)

/-- Restricted squared-tilt weight of a cluster (10:131). -/
noncomputable def tiltWeight (h : History n N δ) (q : Site n δ) (j : Fin (M.K (t q.1))) : ℝ :=
  if j ∈ tiltKept M t h q then
    (maskedPrior M (t q.1) (h.mask q)).w j *
      (lawMassOn (maskedCluster M (t q.1) (h.mask q) j) (hitSet M t h q)) ^ 2
  else 0

theorem tiltWeight_nonneg (h : History n N δ) (q : Site n δ) (j : Fin (M.K (t q.1))) :
    0 ≤ tiltWeight M t h q j := by
  unfold tiltWeight
  split_ifs
  · exact mul_nonneg ((maskedPrior M _ _).nonneg j) (sq_nonneg _)
  · exact le_rfl

/-- The local validity event `𝒱_g` (10:117): position counts within relative
error `.002`, eligibility sizes at least `.99λ`, selections at all incident sites,
a passing realized list of the prescribed form (own fan at most `T`), and positive
retained squared-tilt mass (`h_F > 0`, 10:142). -/
def groupValid (h : History n N δ) (q : Site n δ) : Prop :=
  (∀ s ∈ incidentSites δ q, ∀ j,
    (998 / 1000 : ℝ) * (hp n δ).lam ≤
        (p10_1kHeightPositionCount (hp n δ) (fun loc => h.pos (s.1, loc)) s.2 j : ℝ) ∧
      (p10_1kHeightPositionCount (hp n δ) (fun loc => h.pos (s.1, loc)) s.2 j : ℝ) ≤
        (1002 / 1000 : ℝ) * (hp n δ).lam) ∧
  (∀ s ∈ incidentSites δ q, ∀ j, (99 / 100 : ℝ) * (hp n δ).lam ≤ ((elig M t h s.1 s.2 j).card : ℝ)) ∧
  (∀ s ∈ incidentSites δ q, (selected M t h s).isSome) ∧
  realizedList M t h q ∈ lists h q ∧
  ¬ listFails M t h q (realizedList M t h q) ∧
  0 < ∑ j, tiltWeight M t h q j

/-- Global validity: all groups valid. -/
def valid (h : History n N δ) : Prop := ∀ q, IsGroup δ q → groupValid M t h q

/-- Cluster index: a tag and one of its clusters. -/
abbrev ClIdx := Σ i : M.I, Fin (M.K i)

/-- The cluster law of a group (10:131): the restricted squared tilt on a valid
group with positive retained weight; the masked prior otherwise (local default). -/
noncomputable def clusterLaw (h : History n N δ) (q : Site n δ) : FinProb (ClIdx M) :=
  if hpos : groupValid M t h q ∧ 0 < ∑ j, tiltWeight M t h q j then
    FinProb.map (normalizeLaw (tiltWeight M t h q) (tiltWeight_nonneg M t h q) hpos.2)
      (fun j => (⟨t q.1, j⟩ : ClIdx M))
  else FinProb.map (maskedPrior M (t q.1) (h.mask q)) (fun j => (⟨t q.1, j⟩ : ClIdx M))

/-- The reference label law of an odd role given its group's cluster
(10:144): the cluster restricted to the hit set when the group is valid and the
cluster passes the absolute-mass gate, the masked cluster otherwise. -/
noncomputable def labLaw (h : History n N δ) (b : OddRole n) (c : ClIdx M) : Law N :=
  if groupValid M t h (groupOf δ b) ∧
      Real.exp (-(3 / 2 : ℝ) * kT n δ * (realizedList M t h (groupOf δ b)).card) ≤
        lawMassOn (maskedCluster M c.1 (h.mask (groupOf δ b)) c.2) (hitSet M t h (groupOf δ b))
  then restrictOrSelf (maskedCluster M c.1 (h.mask (groupOf δ b)) c.2) (hitSet M t h (groupOf δ b))
  else maskedCluster M c.1 (h.mask (groupOf δ b)) c.2

/-- The cluster-averaged odd row `p_b^W` times `1_{𝒱_g}` (10:149). -/
noncomputable def oddRow (h : History n N δ) (b : OddRole n) (y : Fin N) : ℝ :=
  if groupValid M t h (groupOf δ b) then
    (clusterLaw M t h (groupOf δ b)).expect (fun c => (labLaw M t h b c).w y)
  else 0

/-! ### Even side (10:191–250) -/

/-- The center selected at an even role's site, as a global ID. -/
noncomputable def centerOf (h : History n N δ) (a : EvenRole n) : Option (ID n δ) :=
  (selected M t h (evenSite δ a)).map fun loc => ((evenSite δ a).1, loc)

/-- Incident groups of an even role. -/
noncomputable def incGroups (a : EvenRole n) : Finset (Site n δ) :=
  p10_1kIncidentOddGroups (mS_le n δ) a

/-- The true local gate at `a` for center `c` (10:193): `c` selected at `a`, the
position counts at `a`'s site, and validity of every incident group. -/
def gate (h : History n N δ) (a : EvenRole n) (c : ID n δ) : Prop :=
  centerOf M t h a = some c ∧
  (∀ j, (998 / 1000 : ℝ) * (hp n δ).lam ≤
      (p10_1kHeightPositionCount (hp n δ) (fun loc => h.pos ((evenSite δ a).1, loc))
        (evenSite δ a).2 j : ℝ) ∧
    (p10_1kHeightPositionCount (hp n δ) (fun loc => h.pos ((evenSite δ a).1, loc))
        (evenSite δ a).2 j : ℝ) ≤ (1002 / 1000 : ℝ) * (hp n δ).lam) ∧
  ∀ q ∈ incGroups a, groupValid M t h q

/-- Reference likelihood of the star labels: one cluster per incident group,
then independent labels (10:193). -/
noncomputable def starLik (h : History n N δ) (a : EvenRole n) (ω : OddRole n → Fin N) : ℝ :=
  ∏ q ∈ incGroups a, (clusterLaw M t h q).expect fun c =>
    ∏ b ∈ (starOf a).filter (fun b => groupOf δ b = q), (labLaw M t h b c).w (ω b)

/-- The sublikelihood `L_w` with candidate tuple `w` at center `c`, all rules
recomputed (10:193). -/
noncomputable def subLik (h : History n N δ) (a : EvenRole n) (c : ID n δ)
    (w : Fin (kT n δ) → Fin N) (ω : OddRole n → Fin N) : ℝ :=
  if gate M t (h.setTuple c w) a c then starLik M t (h.setTuple c w) a ω else 0

/-- The candidate-tuple prior `μ_{t z}^{⊗k}`. -/
noncomputable def tuplePrior (c : ID n δ) : FinProb (Fin (kT n δ) → Fin N) :=
  p10_1kBlockTupleArrayLaw (M.μ (t c.1))

/-- The data marginal `Z` (10:226). -/
noncomputable def predMass (h : History n N δ) (a : EvenRole n) (c : ID n δ)
    (ω : OddRole n → Fin N) : ℝ :=
  (tuplePrior M t c).expect fun w => subLik M t h a c w ω

/-- Deletion reference of one group (10:200): the masked prior tilted by
`D(F_{-c})²`, then independent labels from `D|_{F_{-c}}`, for list `L`. -/
noncomputable def deletionRef (h : History n N δ) (a : EvenRole n) (q : Site n δ)
    (L : Finset (ID n δ)) (c : ID n δ) (ω : OddRole n → Fin N) : ℝ :=
  let Fm : Finset (Fin N) :=
    Finset.univ.filter fun y => ∀ c' ∈ L, c' ≠ c → ∀ i, Hits E G (h.tup c' i) y
  let ρ := maskedPrior M (t q.1) (h.mask q)
  let D := maskedCluster M (t q.1) (h.mask q)
  let A := ∑ j, ρ.w j * (lawMassOn (D j) Fm) ^ 2
  ∑ j, (ρ.w j * (lawMassOn (D j) Fm) ^ 2 / A) *
    ∏ b ∈ (starOf a).filter (fun b => groupOf δ b = q), (restrictOrSelf (D j) Fm).w (ω b)

/-- Uniform average of the deletion references over the lists containing `c`
(10:216). -/
noncomputable def groupRef (h : History n N δ) (a : EvenRole n) (q : Site n δ) (c : ID n δ)
    (ω : OddRole n → Fin N) : ℝ :=
  (((lists h q).filter fun L => c ∈ L).card : ℝ)⁻¹ *
    ∑ L ∈ (lists h q).filter (fun L => c ∈ L), deletionRef M t h a q L c ω

/-- The reference `Q` of (10.2), independent of the candidate tuple. -/
noncomputable def refQ (h : History n N δ) (a : EvenRole n) (c : ID n δ)
    (ω : OddRole n → Fin N) : ℝ :=
  ∏ q ∈ incGroups a, groupRef M t h a q c ω

/-- Posterior weight of a candidate tuple (10:228). -/
noncomputable def posterior (h : History n N δ) (a : EvenRole n) (c : ID n δ)
    (ω : OddRole n → Fin N) (w : Fin (kT n δ) → Fin N) : ℝ :=
  (tuplePrior M t c).w w * subLik M t h a c w ω / predMass M t h a c ω

/-- Average coordinate marginal `p̄` of the posterior (10:232). -/
noncomputable def avgMarginal (h : History n N δ) (a : EvenRole n) (c : ID n δ)
    (ω : OddRole n → Fin N) (x : Fin N) : ℝ :=
  ∑ w, posterior M t h a c ω w *
    (((Finset.univ.filter fun i => w i = x).card : ℝ) / kT n δ)

/-- Heavy labels `B` (10:234). -/
noncomputable def heavy (h : History n N δ) (a : EvenRole n) (c : ID n δ)
    (ω : OddRole n → Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun x =>
    Real.exp ((Real.log 2 - (2 / 100 : ℝ) * aG n δ) * n) < N * avgMarginal M t h a c ω x

/-- Mass of the light part. -/
noncomputable def lightMass (h : History n N δ) (a : EvenRole n) (c : ID n δ)
    (ω : OddRole n → Fin N) : ℝ :=
  ∑ x ∈ Finset.univ \ heavy M t h a c ω, avgMarginal M t h a c ω x

/-- Passing the predictive test at the true gates (10:226), with a light part. -/
def predOK (h : History n N δ) (a : EvenRole n) (c : ID n δ) (ω : OddRole n → Fin N) : Prop :=
  gate M t h a c ∧ 0 < predMass M t h a c ω ∧
    Real.exp (-(1 / 100 : ℝ) * aG n δ * kT n δ * n) * refQ M t h a c ω ≤
      predMass M t h a c ω ∧
    0 < lightMass M t h a c ω

/-- The predictive event of an even role. -/
def predictive (a : EvenRole n) (h : History n N δ) (ω : OddRole n → Fin N) : Prop :=
  ∃ c, centerOf M t h a = some c ∧ predOK M t h a c ω

/-- The even row `p_v^X`: the normalized light part on predictive success, zero
otherwise (10:246). -/
noncomputable def evenRow (h : History n N δ) (ω : OddRole n → Fin N) (a : EvenRole n)
    (x : Fin N) : ℝ :=
  match centerOf M t h a with
  | none => 0
  | some c =>
    if predOK M t h a c ω ∧ x ∉ heavy M t h a c ω then
      avgMarginal M t h a c ω x / lightMass M t h a c ω
    else 0

/-! ### Comparison means, near relations, caps -/

variable (σ : MaskStrategy M)

/-- Normalized odd comparison mean `N p̂_b(y)` at tags `t` (10:156). -/
noncomputable def oddMean (y : Fin N) (b : OddRole n) : ℝ :=
  (N : ℝ) * (historyLaw M σ t).expect fun h => oddRow M t h b y

/-- Normalized even comparison mean `N p̂_v^X(x)` at tags `t` (10:253, 10:292):
prehistory, independent group clusters, reference labels. -/
noncomputable def evenMean (x : Fin N) (a : EvenRole n) : ℝ :=
  (N : ℝ) * (historyLaw M σ t).expect fun h =>
    ∑ c : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w c *
      (FinProb.pi (fun b => labLaw M t h b (c (groupOf δ b)))).expect
        (fun ω => evenRow M t h ω a x)

end Experiment

/-- Residual-near odd roles: special distance at most 8 and projected residual
distance at most `2 R_loc + 16` (10:271). -/
noncomputable def oddNear {n : ℕ} (δ : ℝ) (b : OddRole n) : Finset (OddRole n) :=
  Finset.univ.filter fun b' =>
    hammingDist (groupOf δ b).1 (groupOf δ b').1 ≤ 8 ∧
      hammingDist (groupOf δ b).2 (groupOf δ b').2 ≤ 2 * Rloc n δ + 16

/-- Residual-near even roles (10:288). -/
noncomputable def evenNear {n : ℕ} (δ : ℝ) (a : EvenRole n) : Finset (EvenRole n) :=
  Finset.univ.filter fun a' =>
    hammingDist (evenSite δ a).1 (evenSite δ a').1 ≤ 8 ∧
      hammingDist (evenSite δ a).2 (evenSite δ a').2 ≤ 2 * Rloc n δ + 16

/-- Tag-dependence neighbourhood of a slice: special distance at most 4
(10:119–121, 10:263). -/
noncomputable def tagNbhd {n : ℕ} (δ : ℝ) (z : Slice n δ) : Finset (Slice n δ) :=
  Finset.univ.filter fun z' => hammingDist z z' ≤ 4


/-! ## Caps, fractions and failure levels as finite suprema

The budget fields of `TypicalCore`/`TaggedSystem` are filled with the actual
finite suprema below; d3, d5, d7 and d8d bound them. -/

section Caps

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour}
  {ζ δ κ : ℝ} (M : MenuData n N E X Y G ζ δ κ) (t : Slice n δ → M.I) (σ : MaskStrategy M)

/-- Odd row cap `sup N p_b^W(y)`. -/
noncomputable def oddCapOf : ℝ :=
  ⨆ p : History n N δ × OddRole n × Fin N, (N : ℝ) * oddRow M t p.1 p.2.1 p.2.2

/-- Even row cap `sup N p_v^X(x)`. -/
noncomputable def rowCapOf : ℝ :=
  ⨆ p : History n N δ × (OddRole n → Fin N) × EvenRole n × Fin N,
    (N : ℝ) * evenRow M t p.1 p.2.1 p.2.2.1 p.2.2.2

/-- Group column contribution cap, floored at `e^{-n^ζ}` (10:279). -/
noncomputable def groupCapOf : ℝ :=
  max (⨆ p : History n N δ × Site n δ × ClIdx M × Fin N,
      ∑ b ∈ Finset.univ.filter (fun b => groupOf δ b = p.2.1), (labLaw M t p.1 b p.2.2.1).w p.2.2.2)
    (Real.exp (-(n : ℝ) ^ ζ))

/-- Reference-law predictive failure at an even role, with the validity gate (10:286). -/
noncomputable def refFail (a : EvenRole n) : ℝ :=
  ∑ h, (historyLaw M σ t).w h * (if valid M t h then ∑ c : Site n δ → ClIdx M,
      (FinProb.pi (clusterLaw M t h)).w c *
        (FinProb.pi (fun b => labLaw M t h b (c (groupOf δ b)))).pr
          (fun ω => ¬ predictive M t a h ω)
      else 0)

/-- Worst predictive failure level. -/
noncomputable def εRefOf : ℝ := ⨆ a : EvenRole n, refFail M t σ a

end Caps

/-- Near fractions of the odd and even residual-near relations (10:271). -/
noncomputable def oddFracOf (n : ℕ) (δ : ℝ) : ℝ :=
  ⨆ b : OddRole n, ((oddNear δ b).card : ℝ) / Fintype.card (OddRole n)

noncomputable def evenFracOf (n : ℕ) (δ : ℝ) : ℝ :=
  ⨆ a : EvenRole n, ((evenNear δ a).card : ℝ) / Fintype.card (EvenRole n)

/-- Tag-near sets: roles whose tag neighbourhoods meet (10:267). -/
noncomputable def oddTagNear {n : ℕ} (δ : ℝ) (b : OddRole n) : Finset (OddRole n) :=
  Finset.univ.filter fun b' =>
    ¬ Disjoint (tagNbhd δ (groupOf δ b).1) (tagNbhd δ (groupOf δ b').1)

noncomputable def evenTagNear {n : ℕ} (δ : ℝ) (a : EvenRole n) : Finset (EvenRole n) :=
  Finset.univ.filter fun a' =>
    ¬ Disjoint (tagNbhd δ (evenSite δ a).1) (tagNbhd δ (evenSite δ a').1)

/-- The tag near fraction. -/
noncomputable def tagFracOf (n : ℕ) (δ : ℝ) : ℝ :=
  max (⨆ b : OddRole n, ((oddTagNear δ b).card : ℝ) / Fintype.card (OddRole n))
    (⨆ a : EvenRole n, ((evenTagNear δ a).card : ℝ) / Fintype.card (EvenRole n))

/-- The comparison-mean cap over all tag assignments. -/
noncomputable def meanCapOf {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {G : Colour} {ζ δ κ : ℝ} (M : MenuData n N E X Y G ζ δ κ) (σ : MaskStrategy M) : ℝ :=
  max 0 (max (⨆ p : (Slice n δ → M.I) × Fin N × OddRole n, oddMean M p.1 σ p.2.1 p.2.2)
    (⨆ p : (Slice n δ → M.I) × Fin N × EvenRole n, evenMean M p.1 σ p.2.1 p.2.2))

/-! ## Mask strategies (P10.1f, 10:150–153) -/

section Strategy

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour}
  {ζ δ κ : ℝ} (M : MenuData n N E X Y G ζ δ κ)

/-- The list row `p_𝒟` of a hypothetical list of `r` blocks with tuples `W`
(10:144): the restricted squared tilt of the masked mixture, then `D|_F`; zero when
(10.1) fails or nothing is retained. `own b` marks own-slice blocks. -/
noncomputable def hypListRow (i : M.I) (S : Finset (Fin N)) {r k : ℕ} (μs : Fin r → Law N)
    (own : Fin r → Prop) (W : Fin r → Fin k → Fin N) (y : Fin N) : ℝ :=
  let ρ := maskedPrior M i S
  let D := maskedCluster M i S
  let F := fixedListHitSet E G W
  let kept : Fin (M.K i) → Prop := fun j =>
    Real.exp (-(3 / 2 : ℝ) * k * r) ≤ lawMassOn (D j) F ∧
    ∀ b, (if own b then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) * k)
        else Real.exp (-(6 / 5 : ℝ) * k)) * lawMassOn (D j) (fixedListHitSetWithout E G W b) ≤
      lawMassOn (D j) F
  let wt : Fin (M.K i) → ℝ := fun j => if kept j then ρ.w j * (lawMassOn (D j) F) ^ 2 else 0
  if fixedListFailure E G ρ D μs (aG n δ) W ∨ ∑ j, wt j = 0 then 0
  else ∑ j, wt j / (∑ j', wt j') * (restrictOrSelf (D j) F).w y

/-- The slice adjacent to `z` across special coordinate `e`. -/
noncomputable def flipSlice {n : ℕ} {δ : ℝ} (z : Slice n δ) (e : Fin (mS n δ)) : Slice n δ :=
  Function.update z e (!z e)

/-- Hypothetical mean of `p_𝒟` at group `q` with mask `S` and `s` own IDs
(10:153): `s` own blocks with law `μ_{t z}` and one external block per adjacent
slice with that slice's law, all with independent tuples. -/
noncomputable def hypMean (t : Slice n δ → M.I) (q : Site n δ) (S : Finset (Fin N)) (s : ℕ)
    (y : Fin N) : ℝ :=
  let μs : Fin (s + mS n δ) → Law N := fun b =>
    Fin.addCases (fun _ => M.μ (t q.1)) (fun e => M.μ (t (flipSlice q.1 e))) b
  let own : Fin (s + mS n δ) → Prop := fun b => (b : ℕ) < s
  (p10_1kTupleArrayLaw (k := kT n δ) μs).expect fun W => hypListRow M (t q.1) S μs own W y

/-- A good mask strategy (10:50, 10:153): local in the tags of the group's
slice and its adjacent slices, supported on permitted or trivial masks, with
every hypothetical mean at most `e^{m/100} ν` pointwise (the paper gives
`O(T+1) ν`, which is smaller for large `n`; d5 needs only this). -/
structure GoodStrategy (σ : MaskStrategy M) : Prop where
  local_tags : ∀ q : Site n δ, FinProb.DependsOn (fun t : Slice n δ → M.I => σ t q)
    (Finset.univ.filter fun z => hammingDist z q.1 ≤ 1)
  permitted : ∀ t q S, (σ t q).w S ≠ 0 → Permitted M (t q.1) S ∨ S = Finset.univ
  balanced : ∀ t q (s : ℕ), s ≤ TT n δ → ∀ y,
    ∑ S, (σ t q).w S * hypMean M t q S s y ≤
      Real.exp ((mS n δ : ℝ) / 100) * ∑ j, M.lam (t q.1) j * (M.D (t q.1) j).w y

end Strategy

/-! ## Bookkeeping lemmas for the assembly -/

theorem le_iSup_fin {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) : f i ≤ ⨆ j, f j :=
  le_ciSup (Set.finite_range f).bddAbove i

theorem card_le_ratio_mul {β : Type*} [Fintype β] (F : ℝ) (k : ℕ) (hβ : 0 < Fintype.card β)
    (hk : (k : ℝ) / Fintype.card β ≤ F) : (k : ℝ) ≤ F * Fintype.card β := by
  have hpos : (0 : ℝ) < Fintype.card β := by exact_mod_cast hβ
  rwa [div_le_iff₀ hpos] at hk

theorem pr_nonneg' {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) : 0 ≤ P.pr A := by
  unfold FinProb.pr
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [P.nonneg ω]

theorem refFail_nonneg {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {G : Colour} {ζ δ κ : ℝ} (M : MenuData n N E X Y G ζ δ κ) (t : Slice n δ → M.I)
    (σ : MaskStrategy M) (a : EvenRole n) : 0 ≤ refFail M t σ a := by
  unfold refFail
  apply Finset.sum_nonneg; intro h _
  apply mul_nonneg ((historyLaw M σ t).nonneg h)
  split_ifs
  · exact Finset.sum_nonneg fun c _ => mul_nonneg ((FinProb.pi _).nonneg c) (pr_nonneg' _ _)
  · exact le_rfl

/-! ## Sub-lemmas d1f–d10 -/

section SubLemmas

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour}
  {ζ δ κ : ℝ}

/-- **d1f** (deterministic consequences of the definitions; lemma-level, ~300
lines). Nonnegativity, the cluster average of the labels on validity, the even row
normalization and common-neighbour support on predictive success (the posterior is
supported on tuples hitting every star label, 10:228), and the star locality of the
predictive event and row. Inputs: d1 definitions,
`p10_1k_evenSite_mem_oddGroupEnvelope_of_adjacent`. -/
theorem d1f_facts (M : MenuData n N E X Y G ζ δ κ) (σ : MaskStrategy M)
    (t : Slice n δ → M.I) :
    (∀ h b y, 0 ≤ oddRow M t h b y) ∧
    (∀ h, valid M t h → ∀ b y,
      (clusterLaw M t h (groupOf δ b)).expect (fun c => (labLaw M t h b c).w y) ≤
        oddRow M t h b y) ∧
    (∀ h ω a x, 0 ≤ evenRow M t h ω a x) ∧
    (∀ h ω a, valid M t h → predictive M t a h ω → ∑ x, evenRow M t h ω a x = 1) ∧
    (∀ h ω a, valid M t h → predictive M t a h ω → ∀ x, evenRow M t h ω a x ≠ 0 →
      ∀ b : OddRole n, (cube n).Adj a.1 b.1 → Hits E G x (ω b)) ∧
    (∀ a h, FinProb.DependsOn (fun ω => predictive M t a h ω) (starOf a)) ∧
    (∀ a h x, FinProb.DependsOn (fun ω => evenRow M t h ω a x) (starOf a)) ∧
    (∀ y b, 0 ≤ oddMean M t σ y b) ∧
    (∀ x a, 0 ≤ evenMean M t σ x a) := by
  sorry

/-- **d2** = P10.1d (10:101–117; ~500 lines; new probabilistic argument over
the global experiment). All groups are valid with probability at least `0.99`:
position counts (Chernoff, 10:104), at most `L_n` lists and fewer than `n`
disjoint failures per group (`S10.p10_1c_fixed_list_squared_mass_test`,
`S10.p10_1d_disjoint_failure_union_bound`, independence of disjoint tuple
entries), eligibility at least `.99λ`, height success
(`height_selection_global`), own fan at most `T`
(`p10_1kOddGroupOwnTupleIds_card_le_heightCount`). -/
theorem d2_valid_whp (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ) (σ : MaskStrategy M),
      2 ^ n ≤ N → N ≤ n * 2 ^ n →
      DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
      GoodStrategy M σ → ∀ t : Slice n δ → M.I,
      (historyLaw M σ t).pr (fun h => ¬ valid M t h) ≤ 1 / 100 := by
  sorry

/-- **d3** = P10.1e (10:128–149; ~300 lines; lemma-level from the helper's
squared-tilt kernels). Pointwise caps: `N p_b^W ≤ 8 e^{2k(T+m)+n^δ}`, every label
law has atoms at most `e^{-n^ζ/2}`, and so has each group column contribution
(group size `n^{O(log n)}`, `p10_1k_oddGroup_card_le`). -/
theorem d3_tilt_caps (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ) (t : Slice n δ → M.I),
      2 ^ n ≤ N →
      (∀ h b y, (N : ℝ) * oddRow M t h b y ≤
        8 * Real.exp (2 * kT n δ * (TT n δ + mS n δ) + (n : ℝ) ^ δ)) ∧
      (∀ h b c y, (labLaw M t h b c).w y ≤ Real.exp (-(n : ℝ) ^ ζ / 2)) ∧
      (∀ h q c y, ∑ b ∈ Finset.univ.filter (fun b => groupOf δ b = q),
        (labLaw M t h b c).w y ≤ Real.exp (-(n : ℝ) ^ ζ / 2)) := by
  sorry

/-- **d4** = P10.1f (10:150–153; ~300 lines; lemma-level). A good mask strategy
exists: cheap-label masks from the prices `c_s(y)` (`p10_1f_mask_price_separation`,
`p10_1k_mask_price_response`), chosen per group from the tags at its slice and the
adjacent slices. -/
theorem d4_mask_strategy (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ),
      2 ^ n ≤ N → ∃ σ : MaskStrategy M, GoodStrategy M σ := by
  classical
  have hscaleEvent : ∀ᶠ n : ℕ in atTop,
      10 * ((TT n δ + 1 : ℕ) : ℝ) ≤ Real.exp ((mS n δ : ℝ) / 100) := by
    let x : ℕ → ℝ := fun n => (n : ℝ) ^ (200 * δ)
    have hxTend : Tendsto x atTop atTop := by
      dsimp [x]
      exact (_root_.tendsto_rpow_atTop (by positivity : (0 : ℝ) < 200 * δ)).comp
        tendsto_natCast_atTop_atTop
    have hlarge := hxTend.eventually_gt_atTop (2000000 : ℝ)
    have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
      Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
    filter_upwards [hlarge, hnlarge] with n hlarge hn
    have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by omega)
    have hδsmall' : δ < (1 : ℝ) / 2000 :=
      lt_of_lt_of_le hδsmall
        (div_le_div_of_nonneg_right (min_le_right (min η₀ ζ) 1) (by norm_num))
    have h200 : 200 * δ < 1 := by nlinarith [hδsmall']
    have hxle : x n ≤ (n : ℝ) := by
      calc
        x n = (n : ℝ) ^ (200 * δ) := rfl
        _ ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
        _ = (n : ℝ) := by rw [Real.rpow_one]
    have hsple : p10_1kSpecialCount n δ ≤ n := by
      have hcast : (p10_1kSpecialCount n δ : ℝ) ≤ x n := by
        dsimp [p10_1kSpecialCount, x]
        exact Nat.floor_le (by positivity)
      exact_mod_cast le_trans hcast hxle
    have hmEq : mS n δ = p10_1kSpecialCount n δ := by
      simp [mS, hsple]
    have hfloor : x n < (p10_1kSpecialCount n δ : ℝ) + 1 := by
      dsimp [p10_1kSpecialCount, x]
      exact Nat.lt_floor_add_one _
    have hmLower : x n / 2 ≤ (mS n δ : ℝ) := by
      rw [hmEq]
      nlinarith [hlarge, hfloor]
    have hTnat : p10_1kHeightCount n δ ≤
        ⌊(n : ℝ) ^ (141 * δ)⌋₊ + 1 := Nat.ceil_le_floor_add_one _
    have hTcast : (TT n δ : ℝ) ≤ (n : ℝ) ^ (141 * δ) + 1 := by
      have hcast : (p10_1kHeightCount n δ : ℝ) ≤
          ((⌊(n : ℝ) ^ (141 * δ)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hTnat
      dsimp [TT, p10_1kHeightCount] at hcast ⊢
      rw [Nat.cast_add, Nat.cast_one] at hcast
      have hfloor' := Nat.floor_le (by positivity : 0 ≤ (n : ℝ) ^ (141 * δ))
      have hfloorAdd :
          (⌊(n : ℝ) ^ (141 * δ)⌋₊ : ℝ) + 1 ≤
            (n : ℝ) ^ (141 * δ) + 1 := by linarith
      exact hcast.trans hfloorAdd
    have h141 : (n : ℝ) ^ (141 * δ) ≤ x n := by
      dsimp [x]
      exact Real.rpow_le_rpow_of_exponent_le hnreal (by nlinarith [hδ])
    have hTplus : ((TT n δ + 1 : ℕ) : ℝ) ≤ x n + 2 := by
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    have hxnonneg : 0 ≤ x n := le_of_lt (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) _)
    have hprod : 0 ≤ x n * (x n - 2000000) :=
      mul_nonneg hxnonneg (sub_nonneg.mpr hlarge.le)
    have hpoly : 10 * (x n + 2) ≤ (1 + x n / 400) ^ 2 := by
      nlinarith [hlarge, hprod]
    have hlin : 1 + x n / 400 ≤ Real.exp (x n / 400) := by
      simpa [add_comm] using Real.add_one_le_exp (x n / 400)
    have hsquare : (1 + x n / 400) ^ 2 ≤ Real.exp (x n / 200) := by
      have ha : 0 ≤ 1 + x n / 400 := by positivity
      have he : 0 ≤ Real.exp (x n / 400) := (Real.exp_pos _).le
      calc
        (1 + x n / 400) ^ 2 = (1 + x n / 400) * (1 + x n / 400) := by ring
        _ ≤ Real.exp (x n / 400) * (1 + x n / 400) :=
          mul_le_mul_of_nonneg_right hlin ha
        _ ≤ Real.exp (x n / 400) * Real.exp (x n / 400) :=
          mul_le_mul_of_nonneg_left hlin he
        _ = Real.exp (x n / 200) := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hExp : 10 * (x n + 2) ≤ Real.exp ((mS n δ : ℝ) / 100) := by
      calc
        10 * (x n + 2) ≤ (1 + x n / 400) ^ 2 := hpoly
        _ ≤ Real.exp (x n / 200) := hsquare
        _ ≤ Real.exp ((mS n δ : ℝ) / 100) :=
          Real.exp_le_exp.mpr (by nlinarith [hmLower])
    exact (mul_le_mul_of_nonneg_left hTplus (by norm_num)).trans hExp

  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hscaleEvent
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y G M hN
  have hypList_nonneg {r k : ℕ} (i : M.I) (S : Finset (Fin N))
      (μs : Fin r → Law N) (own : Fin r → Prop) (W : Fin r → Fin k → Fin N)
      (y : Fin N) : 0 ≤ hypListRow M i S μs own W y := by
    let ρ := maskedPrior M i S
    let D := maskedCluster M i S
    let F := fixedListHitSet E G W
    let kept : Fin (M.K i) → Prop := fun j =>
      Real.exp (-(3 / 2 : ℝ) * k * r) ≤ lawMassOn (D j) F ∧
        ∀ b, (if own b then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) * k)
            else Real.exp (-(6 / 5 : ℝ) * k)) *
          lawMassOn (D j) (fixedListHitSetWithout E G W b) ≤ lawMassOn (D j) F
    let wt : Fin (M.K i) → ℝ := fun j =>
      if kept j then ρ.w j * (lawMassOn (D j) F) ^ 2 else 0
    have hwt : ∀ j, 0 ≤ wt j := by
      intro j
      dsimp [wt]
      split_ifs
      · exact mul_nonneg (ρ.nonneg j) (sq_nonneg _)
      · exact le_rfl
    have hden : 0 ≤ ∑ j, wt j := Finset.sum_nonneg fun j _ => hwt j
    change 0 ≤ (if fixedListFailure E G ρ D μs (aG n δ) W ∨
      ∑ j, wt j = 0 then 0 else
        ∑ j, wt j / (∑ j', wt j') * (restrictOrSelf (D j) F).w y)
    by_cases hbad : fixedListFailure E G ρ D μs (aG n δ) W ∨ ∑ j, wt j = 0
    · simp [hbad]
    · have hdenpos : 0 < ∑ j, wt j :=
        lt_of_le_of_ne hden (Ne.symm (fun heq => hbad (Or.inr heq)))
      simp only [if_neg hbad]
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (div_nonneg (hwt j) hdenpos.le) ((restrictOrSelf (D j) F).nonneg y)

  have hypList_sum_le_one {r k : ℕ} (i : M.I) (S : Finset (Fin N))
      (μs : Fin r → Law N) (own : Fin r → Prop) (W : Fin r → Fin k → Fin N) :
      ∑ y, hypListRow M i S μs own W y ≤ 1 := by
    classical
    let ρ := maskedPrior M i S
    let D := maskedCluster M i S
    let F := fixedListHitSet E G W
    let kept : Fin (M.K i) → Prop := fun j =>
      Real.exp (-(3 / 2 : ℝ) * k * r) ≤ lawMassOn (D j) F ∧
        ∀ b, (if own b then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) * k)
            else Real.exp (-(6 / 5 : ℝ) * k)) *
          lawMassOn (D j) (fixedListHitSetWithout E G W b) ≤ lawMassOn (D j) F
    let wt : Fin (M.K i) → ℝ := fun j =>
      if kept j then ρ.w j * (lawMassOn (D j) F) ^ 2 else 0
    have hwt : ∀ j, 0 ≤ wt j := by
      intro j
      dsimp [wt]
      split_ifs
      · exact mul_nonneg (ρ.nonneg j) (sq_nonneg _)
      · exact le_rfl
    have hden : 0 ≤ ∑ j, wt j := Finset.sum_nonneg fun j _ => hwt j
    change ∑ y, (if fixedListFailure E G ρ D μs (aG n δ) W ∨
      ∑ j, wt j = 0 then 0 else
        ∑ j, wt j / (∑ j', wt j') * (restrictOrSelf (D j) F).w y) ≤ 1
    by_cases hbad : fixedListFailure E G ρ D μs (aG n δ) W ∨ ∑ j, wt j = 0
    · simp [hbad]
    · have hdenne : (∑ j, wt j) ≠ 0 := by
        intro heq
        exact hbad (Or.inr heq)
      have hdenpos : 0 < ∑ j, wt j := lt_of_le_of_ne hden (Ne.symm hdenne)
      simp only [if_neg hbad]
      calc
        (∑ y, ∑ j, wt j / (∑ j', wt j') * (restrictOrSelf (D j) F).w y) =
            ∑ j, wt j / (∑ j', wt j') * ∑ y, (restrictOrSelf (D j) F).w y := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.mul_sum]
        _ = ∑ j, wt j / (∑ j', wt j') := by
          apply Finset.sum_congr rfl
          intro j hj
          have hlaw : ∑ y, (restrictOrSelf (D j) F).w y = 1 :=
            (restrictOrSelf (D j) F).sum_eq_one
          rw [hlaw]
          ring
        _ = 1 := by
          rw [← Finset.sum_div]
          exact div_self hdenne
        _ ≤ 1 := le_rfl

  have hypList_supported {r k : ℕ} (i : M.I) (S : Finset (Fin N))
      (μs : Fin r → Law N) (own : Fin r → Prop) (W : Fin r → Fin k → Fin N)
      (hPerm : Permitted M i S) {y : Fin N} (hy : y ∉ S) :
      hypListRow M i S μs own W y = 0 := by
    classical
    let ρ := maskedPrior M i S
    let D := maskedCluster M i S
    let F := fixedListHitSet E G W
    let kept : Fin (M.K i) → Prop := fun j =>
      Real.exp (-(3 / 2 : ℝ) * k * r) ≤ lawMassOn (D j) F ∧
        ∀ b, (if own b then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) * k)
            else Real.exp (-(6 / 5 : ℝ) * k)) *
          lawMassOn (D j) (fixedListHitSetWithout E G W b) ≤ lawMassOn (D j) F
    let wt : Fin (M.K i) → ℝ := fun j =>
      if kept j then ρ.w j * (lawMassOn (D j) F) ^ 2 else 0
    have hρzero (j : Fin (M.K i)) (hj : j ∉ keptClusters M i S) : ρ.w j = 0 := by
      dsimp [ρ, maskedPrior]
      rw [dif_pos hPerm]
      simp [FinProb.cond, hj]
    have hDsupport (j : Fin (M.K i)) (hj : j ∈ keptClusters M i S) :
        ∀ y, y ∉ S → (D j).w y = 0 := by
      intro y hy
      have hmass : 0 < lawMassOn (M.D i j) S :=
        lt_of_lt_of_le (by norm_num) (Finset.mem_filter.mp hj).2
      simp [D, maskedCluster, hPerm, hj, restrictOrSelf, hmass, Law.restrict, hy]
    change (if fixedListFailure E G ρ D μs (aG n δ) W ∨
      ∑ j, wt j = 0 then 0 else
        ∑ j, wt j / (∑ j', wt j') * (restrictOrSelf (D j) F).w y) = 0
    by_cases hbad : fixedListFailure E G ρ D μs (aG n δ) W ∨ ∑ j, wt j = 0
    · simp [hbad]
    · simp only [if_neg hbad]
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hjK : j ∈ keptClusters M i S
      · have hrow : (restrictOrSelf (D j) F).w y = 0 := by
          unfold restrictOrSelf
          split_ifs with hmass
          · simp [Law.restrict, hDsupport j hjK y hy]
          · exact hDsupport j hjK y hy
        simp [hrow]
      · have hwtzero : wt j = 0 := by
          dsimp [wt]
          split_ifs
          · simp [hρzero j hjK]
          · rfl
        simp [hwtzero]

  have hypMean_nonneg (p : Slice n δ → M.I) (q : Site n δ)
      (S : Finset (Fin N)) (s : ℕ) (y : Fin N) :
      0 ≤ hypMean M p q S s y := by
    let μs : Fin (s + mS n δ) → Law N := fun b =>
      Fin.addCases (fun _ => M.μ (p q.1)) (fun e => M.μ (p (flipSlice q.1 e))) b
    let own : Fin (s + mS n δ) → Prop := fun b => (b : ℕ) < s
    let P := p10_1kTupleArrayLaw (k := kT n δ) μs
    have hrow (W : Fin (s + mS n δ) → Fin (kT n δ) → Fin N) :
        0 ≤ hypListRow M (p q.1) S μs own W y := by
      exact hypList_nonneg (r := s + mS n δ) (k := kT n δ)
        (p q.1) S μs own W y
    change 0 ≤ ∑ W, P.w W * hypListRow M (p q.1) S μs own W y
    apply Finset.sum_nonneg
    intro W hW
    exact mul_nonneg (P.nonneg W) (hrow W)

  have hypMean_sum_le_one (p : Slice n δ → M.I) (q : Site n δ)
      (S : Finset (Fin N)) (s : ℕ) :
      ∑ y, hypMean M p q S s y ≤ 1 := by
    let μs : Fin (s + mS n δ) → Law N := fun b =>
      Fin.addCases (fun _ => M.μ (p q.1)) (fun e => M.μ (p (flipSlice q.1 e))) b
    let own : Fin (s + mS n δ) → Prop := fun b => (b : ℕ) < s
    let P := p10_1kTupleArrayLaw (k := kT n δ) μs
    have heq : ∑ y, hypMean M p q S s y =
        ∑ W, P.w W * ∑ y, hypListRow M (p q.1) S μs own W y := by
      unfold hypMean FinProb.expect
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro W hW
      rw [← Finset.mul_sum]
    calc
      ∑ y, hypMean M p q S s y =
          ∑ W, P.w W * ∑ y, hypListRow M (p q.1) S μs own W y := heq
      _ ≤ ∑ W, P.w W * 1 := by
        apply Finset.sum_le_sum
        intro W hW
        exact mul_le_mul_of_nonneg_left
          (hypList_sum_le_one (p q.1) S μs own W) (P.nonneg W)
      _ = 1 := by simp [P.sum_eq_one]

  have hypMean_supported (p : Slice n δ → M.I) (q : Site n δ)
      (S : Finset (Fin N)) (hPerm : Permitted M (p q.1) S) (s : ℕ)
      {y : Fin N} (hy : y ∉ S) : hypMean M p q S s y = 0 := by
    let μs : Fin (s + mS n δ) → Law N := fun b =>
      Fin.addCases (fun _ => M.μ (p q.1)) (fun e => M.μ (p (flipSlice q.1 e))) b
    let own : Fin (s + mS n δ) → Prop := fun b => (b : ℕ) < s
    unfold hypMean FinProb.expect
    apply Finset.sum_eq_zero
    intro W hW
    change (p10_1kTupleArrayLaw (k := kT n δ) μs).w W *
      hypListRow M (p q.1) S μs own W y = 0
    rw [hypList_supported (p q.1) S μs own W hPerm hy]
    simp

  let Action := fun (p : Slice n δ → M.I) (q : Site n δ) =>
    {S : Finset (Fin N) // Permitted M (p q.1) S ∨ S = Finset.univ}
  have maskResponseExists (p : Slice n δ → M.I) (q : Site n δ) :
      ∃ P : FinProb (Action p q),
        ∀ s : Fin (TT n δ + 1), ∀ y,
          P.expect (fun a => hypMean M p q a.1 s y) ≤
            10 * ((TT n δ + 1 : ℕ) : ℝ) *
              (Law.mix (prior M (p q.1)) (M.D (p q.1))).w y := by
    classical
    let i := p q.1
    let data : P10_1kClusterData (n := n) (N := N) E G ζ δ X Y := {
      μ := M.μ i
      K := M.K i
      lam := M.lam i
      D := M.D i
      μ_supported := M.μ_support i
      D_supported := M.D_support i
      lam_nonneg := M.lam_nonneg i
      lam_sum := M.lam_sum i
      μ_width := M.μ_width i
      aggregate_width := M.ν_width i
      D_atom := M.D_atom i
      codegree := M.codegree i
    }
    let ν : Law N := Law.mix (prior M i) (M.D i)
    let Coord := Fin (TT n δ + 1) × Fin N
    let v : Action p q → Coord → ℝ := fun S c =>
      hypMean M p q S.1 c.1 c.2
    let bound : Coord → ℝ := fun c =>
      10 * ((TT n δ + 1 : ℕ) : ℝ) * ν.w c.2
    have hprice : ∀ c : Coord → ℝ, (∀ z, 0 ≤ c z) →
        ∃ S : Action p q, ∑ z, c z * v S z ≤ ∑ z, c z * bound z := by
      intro c hc
      let price : Fin (TT n δ + 1) → Fin N → ℝ := fun s y => c (s, y)
      have hpriceNonneg : ∀ s y, 0 ≤ price s y := by
        intro s y
        exact hc (s, y)
      let F := cheapMaskLabels ν price
      have hsep := p10_1f_mask_price_separation ν price hpriceNonneg
      have hmass : 9 / 10 ≤
          lawMassOn (Law.mix (p10_1kClusterPrior data) data.D) F := by
        simpa [F, ν, i, data, prior, p10_1kClusterPrior, Law.mix] using hsep.1
      have hret := p10_1k_retainedClusterSet_mass
        (p10_1kClusterPrior data) data.D F hmass
      have hPerm : Permitted M i F := by
        change (1 / 2 : ℝ) ≤
          (prior M i).pr (fun j => j ∈ keptClusters M i F)
        simpa [prior, keptClusters, p10_1kClusterPrior,
          p10_1kRetainedClusterSet, data] using hret
      let S : Action p q := ⟨F, Or.inl hPerm⟩
      have hcheap (y : Fin N) (hy : y ∈ F) :
          ∑ s : Fin (TT n δ + 1), price s y ≤ 10 * totalMaskPrice ν price := by
        simpa [F, cheapMaskLabels] using (Finset.mem_filter.mp hy).2
      have hpriceBound (s : Fin (TT n δ + 1)) (y : Fin N) (hy : y ∈ F) :
          price s y ≤ 10 * totalMaskPrice ν price := by
        calc
          price s y ≤ ∑ s' : Fin (TT n δ + 1), price s' y :=
            Finset.single_le_sum (fun s' hs' => hpriceNonneg s' y)
              (Finset.mem_univ s)
          _ ≤ 10 * totalMaskPrice ν price := hcheap y hy
      have hSnonneg : 0 ≤ totalMaskPrice ν price := by
        unfold totalMaskPrice
        apply Finset.sum_nonneg
        intro s hs
        apply Finset.sum_nonneg
        intro y hy
        exact mul_nonneg (ν.nonneg y) (hpriceNonneg s y)
      have hrowCost (s : Fin (TT n δ + 1)) :
          ∑ y, price s y * hypMean M p q F s y ≤
            10 * totalMaskPrice ν price := by
        calc
          ∑ y, price s y * hypMean M p q F s y ≤
              ∑ y, (10 * totalMaskPrice ν price) * hypMean M p q F s y := by
            apply Finset.sum_le_sum
            intro y hy
            by_cases hyF : y ∈ F
            · exact mul_le_mul_of_nonneg_right (hpriceBound s y hyF)
                (hypMean_nonneg p q F s y)
            · rw [hypMean_supported p q F hPerm s hyF]
              simp
          _ = (10 * totalMaskPrice ν price) *
                ∑ y, hypMean M p q F s y := by rw [← Finset.mul_sum]
          _ ≤ (10 * totalMaskPrice ν price) * 1 :=
            mul_le_mul_of_nonneg_left (hypMean_sum_le_one p q F s)
              (mul_nonneg (by norm_num) hSnonneg)
          _ = 10 * totalMaskPrice ν price := by ring
      have htarget :
          ∑ s : Fin (TT n δ + 1), ∑ y : Fin N,
              price s y * (10 * ((TT n δ + 1 : ℕ) : ℝ) * ν.w y) =
            (10 * ((TT n δ + 1 : ℕ) : ℝ)) * totalMaskPrice ν price := by
        unfold totalMaskPrice
        calc
          _ = ∑ s : Fin (TT n δ + 1),
                (10 * ((TT n δ + 1 : ℕ) : ℝ)) *
                  ∑ y : Fin N, ν.w y * price s y := by
            apply Finset.sum_congr rfl
            intro s hs
            calc
              ∑ y : Fin N, price s y *
                  (10 * ((TT n δ + 1 : ℕ) : ℝ) * ν.w y) =
                  ∑ y : Fin N,
                    (10 * ((TT n δ + 1 : ℕ) : ℝ)) * (ν.w y * price s y) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
              _ = (10 * ((TT n δ + 1 : ℕ) : ℝ)) *
                    ∑ y : Fin N, ν.w y * price s y := by
                rw [← Finset.mul_sum]
          _ = (10 * ((TT n δ + 1 : ℕ) : ℝ)) *
                ∑ s : Fin (TT n δ + 1), ∑ y : Fin N, ν.w y * price s y := by
            rw [← Finset.mul_sum]
          _ = (10 * ((TT n δ + 1 : ℕ) : ℝ)) * totalMaskPrice ν price := rfl
      have hcost :
          ∑ s : Fin (TT n δ + 1), ∑ y : Fin N,
              price s y * hypMean M p q F s y ≤
            ∑ s : Fin (TT n δ + 1), ∑ y : Fin N,
              price s y * (10 * ((TT n δ + 1 : ℕ) : ℝ) * ν.w y) := by
        calc
          ∑ s : Fin (TT n δ + 1), ∑ y : Fin N,
              price s y * hypMean M p q F s y ≤
              ∑ s : Fin (TT n δ + 1), 10 * totalMaskPrice ν price :=
            Finset.sum_le_sum fun s hs => hrowCost s
          _ = (10 * ((TT n δ + 1 : ℕ) : ℝ)) * totalMaskPrice ν price := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
          _ = ∑ s : Fin (TT n δ + 1), ∑ y : Fin N,
              price s y * (10 * ((TT n δ + 1 : ℕ) : ℝ) * ν.w y) := htarget.symm
      refine ⟨S, ?_⟩
      simpa [v, bound, Coord, price, S, F, Fintype.sum_prod_type] using hcost
    obtain ⟨w, hw0, hw1, hbound⟩ :=
      HypercubeRamsey.Lane_q_s10_d4.finite_mixture_le_of_price_bound v bound hprice
    let P : FinProb (Action p q) := ⟨w, hw0, hw1⟩
    refine ⟨P, ?_⟩
    intro s y
    simpa [P, v, bound, FinProb.expect] using hbound (s, y)

  let near := fun q : Site n δ =>
    Finset.univ.filter fun z : Slice n δ => hammingDist z q.1 ≤ 1
  have hflipDist (z : Slice n δ) (e : Fin (mS n δ)) :
      hammingDist z (flipSlice z e) ≤ 1 := by
    classical
    have hsub :
        (Finset.univ.filter fun i : Fin (mS n δ) => z i ≠ flipSlice z e i) ⊆ {e} := by
      intro i hi
      by_contra hnot
      have hne : i ≠ e := by
        intro hie
        apply hnot
        simp [hie]
      have heq : flipSlice z e i = z i := by
        simp [flipSlice, Function.update_of_ne hne]
      exact (Finset.mem_filter.mp hi).2 heq.symm
    change (Finset.univ.filter fun i : Fin (mS n δ) => z i ≠ flipSlice z e i).card ≤ 1
    calc
      _ ≤ ({e} : Finset (Fin (mS n δ))).card := Finset.card_le_card hsub
      _ = 1 := by simp
  let defaultTag : M.I := Classical.choice M.neI
  let localize := fun (p : Slice n δ → M.I) (q : Site n δ) =>
    fun z : Slice n δ => if z ∈ near q then p z else defaultTag
  have hqNear (q : Site n δ) : q.1 ∈ near q := by
    simp [near]
  have hflipNear (q : Site n δ) (e : Fin (mS n δ)) :
      flipSlice q.1 e ∈ near q := by
    simp [near, hammingDist_comm, hflipDist]
  have hmeanLocalized (p : Slice n δ → M.I) (q : Site n δ)
      (S : Finset (Fin N)) (s : ℕ) (y : Fin N) :
      hypMean M (localize p q) q S s y = hypMean M p q S s y := by
    have hself : localize p q q.1 = p q.1 := by
      simp [localize, hqNear]
    have hflip : ∀ e, localize p q (flipSlice q.1 e) = p (flipSlice q.1 e) := by
      intro e
      simp [localize, hflipNear]
    have hfirst :
        (fun _ : Fin s => M.μ (localize p q q.1)) =
          (fun _ : Fin s => M.μ (p q.1)) := by
      funext b
      rw [hself]
    have hsecond :
        (fun e : Fin (mS n δ) => M.μ (localize p q (flipSlice q.1 e))) =
          (fun e : Fin (mS n δ) => M.μ (p (flipSlice q.1 e))) := by
      funext e
      rw [hflip e]
    have hμs' :
        @Fin.addCases s (mS n δ) (fun _ : Fin (s + mS n δ) => Law N)
          (fun _ : Fin s => M.μ (localize p q q.1))
          (fun e : Fin (mS n δ) => M.μ (localize p q (flipSlice q.1 e))) =
        @Fin.addCases s (mS n δ) (fun _ : Fin (s + mS n δ) => Law N)
          (fun _ : Fin s => M.μ (p q.1))
          (fun e : Fin (mS n δ) => M.μ (p (flipSlice q.1 e))) := by
      rw [hfirst, hsecond]
    simp only [hypMean]
    rw [hμs', hself]

  let chooseLaw := fun (p : Slice n δ → M.I) (q : Site n δ) =>
    Classical.choose (maskResponseExists p q)
  let σ : MaskStrategy M := fun t q =>
    FinProb.map (chooseLaw (localize t q) q) Subtype.val

  refine ⟨σ, ?_, ?_, ?_⟩
  · intro q
    unfold FinProb.DependsOn
    intro t t' hagree
    have hlocal : localize t q = localize t' q := by
      funext z
      simp only [localize]
      by_cases hz : z ∈ near q
      · simp [hz, hagree z hz]
      · simp [hz]
    change FinProb.map (chooseLaw (localize t q) q) Subtype.val =
      FinProb.map (chooseLaw (localize t' q) q) Subtype.val
    rw [hlocal]
  · intro t q S hweight
    let p := localize t q
    by_contra hnot
    have hnotLocal : ¬(Permitted M (p q.1) S ∨ S = Finset.univ) := by
      intro hP
      apply hnot
      simpa [p, localize, hqNear] using hP
    have hterm : ∀ a : Action p q,
        (if a.1 = S then (chooseLaw p q).w a else 0) = 0 := by
      intro a
      by_cases heq : a.1 = S
      · have hprop : Permitted M (p q.1) S ∨ S = Finset.univ := by
          simpa [Action, heq] using a.2
        exact False.elim (hnotLocal hprop)
      · simp [heq]
    have hzero : ∑ a : Action p q,
        (if a.1 = S then (chooseLaw p q).w a else 0) = 0 :=
      Finset.sum_eq_zero fun a ha => hterm a
    have hweight' : (FinProb.map (chooseLaw p q) Subtype.val).w S ≠ 0 := by
      simpa [σ, chooseLaw, p] using hweight
    change (∑ a : Action p q,
      if a.1 = S then (chooseLaw p q).w a else 0) ≠ 0 at hweight'
    exact hweight' hzero
  · intro t q s hs y
    let p := localize t q
    let P := chooseLaw p q
    have hP := Classical.choose_spec (maskResponseExists p q)
    have hsame (S : Finset (Fin N)) :
        hypMean M p q S s y = hypMean M t q S s y := by
      exact hmeanLocalized t q S s y
    have heq : P.expect (fun a : Action p q => hypMean M p q a.1 s y) =
        P.expect (fun a : Action p q => hypMean M t q a.1 s y) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro a ha
      change P.w a * hypMean M p q a.1 s y =
        P.w a * hypMean M t q a.1 s y
      rw [hsame a.1]
    have hnu : (Law.mix (prior M (p q.1)) (M.D (p q.1))).w y =
        ∑ j, M.lam (p q.1) j * (M.D (p q.1) j).w y := by
      simp [prior, Law.mix]
    let sFin : Fin (TT n δ + 1) := ⟨s, by omega⟩
    have hPbound : P.expect (fun a : Action p q => hypMean M p q a.1 s y) ≤
        10 * ((TT n δ + 1 : ℕ) : ℝ) *
          (Law.mix (prior M (p q.1)) (M.D (p q.1))).w y := by
      simpa [P, chooseLaw, sFin] using hP sFin y
    have hself : p q.1 = t q.1 := by
      simp [p, localize, hqNear]
    have hrows :
        (∑ j, M.lam (p q.1) j * (M.D (p q.1) j).w y) =
          ∑ j, M.lam (t q.1) j * (M.D (t q.1) j).w y := by
      exact congrArg (fun i : M.I =>
        ∑ j : Fin (M.K i), M.lam i j * (M.D i j).w y) hself
    calc
      ∑ S : Finset (Fin N), (σ t q).w S * hypMean M t q S s y =
          (FinProb.map P Subtype.val).expect (fun S => hypMean M t q S s y) := rfl
      _ = P.expect (fun a : Action p q => hypMean M t q a.1 s y) :=
        FinProb.map_expect P Subtype.val _
      _ = P.expect (fun a : Action p q => hypMean M p q a.1 s y) := heq.symm
      _ ≤ 10 * ((TT n δ + 1 : ℕ) : ℝ) *
          (Law.mix (prior M (p q.1)) (M.D (p q.1))).w y := hPbound
      _ ≤ Real.exp ((mS n δ : ℝ) / 100) *
          ∑ j, M.lam (p q.1) j * (M.D (p q.1) j).w y := by
        have hsc := mul_le_mul_of_nonneg_right (hn₀ n hn)
          ((Law.mix (prior M (p q.1)) (M.D (p q.1))).nonneg y)
        simpa [hnu] using hsc
      _ = Real.exp ((mS n δ : ℝ) / 100) *
          ∑ j, M.lam (t q.1) j * (M.D (t q.1) j).w y := by rw [hrows]

/-- **d5** = P10.1g (10:155–186; ~500 lines; new argument: the position-only
enumeration of own lists, the eligibility-free selection bounds `w_{ℓ,c}` from
Lemma 3.8, independence across slices given positions). The odd comparison means
satisfy `N p̂_b ≤ e^{.1m}`. -/
theorem d5_odd_mean_cap (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ) (σ : MaskStrategy M),
      2 ^ n ≤ N → GoodStrategy M σ → ∀ (t : Slice n δ → M.I) y b,
      oddMean M t σ y b ≤ Real.exp ((mS n δ : ℝ) / 10) := by
  sorry

/-- **d6** = P10.1h, the comparison (10.2) (10:191–222; ~500 lines; new
argument per group: ratio `2 A(F_{-c})/A(F) (D(F)/D(F_{-c}))^{2-j}`, singleton groups,
uniform averaging over lists containing `c`; product by
`p10_1h_product_likelihood_comparison`). -/
theorem d6_likelihood_comparison (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ) (t : Slice n δ → M.I),
      2 ^ n ≤ N → ∀ h a c w ω,
      subLik M t h a c w ω ≤
        Real.exp ((Real.log 2 - (6 / 100 : ℝ) * aG n δ) * kT n δ * n) * refQ M t h a c ω := by
  sorry

/-- **d7a** = P10.1i(i) with 10:286 (~300 lines; lemma-level from d6 and
`p10_1i_predictive_test`). Reference-law predictive failure at one even role,
summed over its polynomially many candidates, including the light-part bound
(the posterior cap `e^{(log 2-.04a)kn}` and the heavy-set union, 10:228–244). -/
theorem d7a_predictive_failure (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ) (σ : MaskStrategy M),
      2 ^ n ≤ N → N ≤ n * 2 ^ n → ∀ (t : Slice n δ → M.I) a,
      refFail M t σ a ≤ Real.exp (-(1 / 200 : ℝ) * aG n δ * kT n δ * n) := by
  sorry

/-- **d7b** = P10.1i(iii) (10:246–250; ~150 lines; lemma-level): the even row
cap `N p_v^X ≤ e^{(log 2 - .01a)n}` (light part and its mass `c₆a`). -/
theorem d7b_even_row_cap (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ) (t : Slice n δ → M.I),
      2 ^ n ≤ N → ∀ h ω a x,
      (N : ℝ) * evenRow M t h ω a x ≤ Real.exp ((Real.log 2 - (1 / 100 : ℝ) * aG n δ) * n) := by
  sorry

/-- **d7c** = P10.1i(iv) (10:252–261; ~400 lines; new argument: the integration
identity of `p10_1i_predictive_test` turns the posterior back into the tuple prior,
then the gate probability and polynomially many candidates). Even comparison means
satisfy `N p̂_v^X ≤ e^{.1m}`. -/
theorem d7c_even_mean_cap (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ) (σ : MaskStrategy M),
      2 ^ n ≤ N → GoodStrategy M σ → ∀ (t : Slice n δ → M.I) x a,
      evenMean M t σ x a ≤ Real.exp ((mS n δ : ℝ) / 10) := by
  sorry

/-- **d8a** (10:119–126, 10:271–275; ~500 lines; new formal argument: the input
domain of a group calculation, the product structure of `historyLaw`, and
factorization over disjoint domains). At separated odd roles the gated product of
normalized rows has expectation at most the product of comparison means. -/
theorem d8a_odd_separated (M : MenuData n N E X Y G ζ δ κ) (σ : MaskStrategy M)
    (hσ : GoodStrategy M σ) (t : Slice n δ → M.I) :
    ∀ y (m : ℕ), m ≤ n → ∀ s : Fin m → OddRole n,
      (∀ i j : Fin m, j < i → s i ∉ oddNear δ (s j)) →
        ∑ h, (historyLaw M σ t).w h *
            (if valid M t h then ∏ i, (N : ℝ) * oddRow M t h (s i) y else 0) ≤
          ∏ i, oddMean M t σ y (s i) := by
  sorry

/-- **d8b** (10:288–292; ~500 lines; new formal argument, shares the domain
bookkeeping of d8a): at separated even roles, integrating prehistory, group
clusters and reference labels factorizes into the even comparison means. -/
theorem d8b_even_separated (M : MenuData n N E X Y G ζ δ κ) (σ : MaskStrategy M)
    (hσ : GoodStrategy M σ) (t : Slice n δ → M.I) :
    ∀ x (m : ℕ), m ≤ n → ∀ s : Fin m → EvenRole n,
      (∀ i j : Fin m, j < i → s i ∉ evenNear δ (s j)) →
        ∑ h, (historyLaw M σ t).w h * (if valid M t h then ∑ c : Site n δ → ClIdx M,
            (FinProb.pi (clusterLaw M t h)).w c *
              (FinProb.pi (fun b => labLaw M t h b (c (groupOf δ b)))).expect
                (fun ω => ∏ i, (N : ℝ) * evenRow M t h ω (s i) x) else 0) ≤
          1 ^ m * ∏ i, evenMean M t σ x (s i) := by
  sorry

/-- **d8c** (10:119–121, 10:263; ~300 lines; new formal argument, the tag part
of the input domain): comparison means read only tags within special distance 4. -/
theorem d8c_tag_locality (M : MenuData n N E X Y G ζ δ κ) (σ : MaskStrategy M)
    (hσ : GoodStrategy M σ) :
    (∀ y b, FinProb.DependsOn (fun t : Slice n δ → M.I => oddMean M t σ y b)
      (tagNbhd δ (groupOf δ b).1)) ∧
    (∀ x a, FinProb.DependsOn (fun t : Slice n δ → M.I => evenMean M t σ x a)
      (tagNbhd δ (evenSite δ a).1)) := by
  sorry

/-- **d8d** (10:39, 10:267, 10:271; ~300 lines; lemma-level counting): the near
fractions. Residual: special ball of radius 8 times a residual ball of radius
`2R_loc + 16` times projection fibres, at most `e^{n^{1-2δ}} 2^{-n}`; tags: at most
`(m+1)^9 2^{-m}`. -/
theorem d8d_near_fractions (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 2000) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      oddFracOf n δ ≤ Real.exp ((n : ℝ) ^ (1 - 2 * δ)) / 2 ^ n ∧
      evenFracOf n δ ≤ Real.exp ((n : ℝ) ^ (1 - 2 * δ)) / 2 ^ n ∧
      tagFracOf n δ ≤ ((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ) := by
  sorry

/-- **d9** (10:265; ~300 lines; lemma-level: `balanced_mixture`-type separation on
the expected slice terms, which are sub-probability vectors supported on the tag's
own patch). The one-slice balanced response with constant `4/κ`. -/
theorem d9_balanced_response (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ) (σ : MaskStrategy M),
      2 ^ n ≤ N → GoodStrategy M σ →
      ∀ j (q : Slice n δ → M.I → ℝ), (∀ i a, 0 ≤ q i a) → (∀ i, ∑ a, q i a = 1) →
        ∃ qj : M.I → ℝ, (∀ a, 0 ≤ qj a) ∧ ∑ a, qj a = 1 ∧
          (∀ y, ∑ τ : Slice n δ → M.I, (∏ i, Function.update q j qj i (τ i)) *
              ((Fintype.card (Slice n δ) : ℝ) / Fintype.card (OddRole n) *
                ∑ b ∈ Finset.univ.filter (fun b => (groupOf δ b).1 = j), oddMean M τ σ y b)
            ≤ 4 / κ) ∧
          (∀ x, ∑ τ : Slice n δ → M.I, (∏ i, Function.update q j qj i (τ i)) *
              ((Fintype.card (Slice n δ) : ℝ) / Fintype.card (EvenRole n) *
                ∑ a ∈ Finset.univ.filter (fun a => (evenSite δ a).1 = j), evenMean M τ σ x a)
            ≤ 4 / κ) := by
  sorry

/-- **d10** (budget arithmetic, 10:13–28, 10:83, 10:109, 10:268–292; ~300 lines;
lemma-level real analysis with `p10_1b_scale_separation`). With `typThr = 8(4/κ+1)`
and `oddThr = 10⁻⁹`, the stated bounds on the failure levels, caps and fractions
give the clock atom condition, the tag budget and the fixed-tag budget. -/
theorem d10_budget (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) (A : ℝ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N, LargeAt n₀ C₀ n N →
      (0 < n ∧ 2 ^ n ≤ N ∧ Real.exp (-(n : ℝ) ^ ζ / 2) ≤ (n : ℝ) ^ (-A)) ∧
      ∀ εv oddCap groupCap εref rowCap oddFrac evenFrac meanCap tagFrac : ℝ,
      0 ≤ εv → εv ≤ 1 / 100 →
      0 ≤ oddCap → oddCap ≤ 8 * Real.exp (2 * kT n δ * (TT n δ + mS n δ) + (n : ℝ) ^ δ) →
      0 < groupCap → groupCap ≤ Real.exp (-(n : ℝ) ^ ζ / 2) →
      0 ≤ εref → εref ≤ Real.exp (-(1 / 200 : ℝ) * aG n δ * kT n δ * n) →
      0 ≤ rowCap → rowCap ≤ Real.exp ((Real.log 2 - (1 / 100 : ℝ) * aG n δ) * n) →
      0 ≤ oddFrac → oddFrac ≤ Real.exp ((n : ℝ) ^ (1 - 2 * δ)) / 2 ^ n →
      0 ≤ evenFrac → evenFrac ≤ Real.exp ((n : ℝ) ^ (1 - 2 * δ)) / 2 ^ n →
      0 ≤ meanCap → meanCap ≤ Real.exp ((mS n δ : ℝ) / 10) →
      0 ≤ tagFrac → tagFrac ≤ ((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ) →
      2 * N * ((4 / κ + n * tagFrac * meanCap) / (8 * (4 / κ + 1))) ^ n < 1 ∧
      εv + N * ((Fintype.card (OddRole n) : ℝ) * (8 * (4 / κ + 1) + n * oddFrac * oddCap) /
            (N * (1 / 10 ^ 9))) ^ n
        + N * Real.exp (((Real.exp 1 - 1) * (1 / 10 ^ 9) - 1e-8) / groupCap)
        + Fintype.card (EvenRole n) * (2 * εref)
        + N * (((Fintype.card (EvenRole n) : ℝ) / N) * (2 * 1) *
            (8 * (4 / κ + 1) + n * evenFrac * rowCap)) ^ n < 1 := by
  sorry

end SubLemmas

end HypercubeRamsey.Lane_opus_s10_tagged
