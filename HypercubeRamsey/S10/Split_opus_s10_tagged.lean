import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k
import HypercubeRamsey.S10.Split_opus_s10_tagged_q_s10_d3

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

/-- Present IDs in the radius-`r` balls of a group's incident even sites, at all
levels (10:102). Only gated sites are read, so on validity the number of
candidates is controlled by the position counts in `groupValid`. -/
noncomputable def candidates (h : History n N δ) (q : Site n δ) : Finset (ID n δ) :=
  (incidentSites δ q).biUnion fun s =>
    (Finset.univ : Finset (Fin ((hp n δ).H + 1))).biUnion fun j =>
      (p10_1kHeightEligibleIds (hp n δ) (fun loc => h.pos (s.1, loc)) s.2 j).image
        (fun loc => (s.1, loc))

/-- Hypothetical lists of the prescribed form: at most `T` own-slice IDs and
exactly one ID from each adjacent slice (10:57). -/
noncomputable def lists (h : History n N δ) (q : Site n δ) : Finset (Finset (ID n δ)) :=
  (candidates h q).powerset.filter fun L =>
    (L.filter fun c => c.1 = q.1).card ≤ TT n δ ∧
    (∀ c ∈ L, c.1 = q.1 ∨ _root_.hammingDist c.1 q.1 = 1) ∧
    ∀ z' : Slice n δ, _root_.hammingDist z' q.1 = 1 → (L.filter fun c => c.1 = z').card = 1

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
error `.002`, eligibility sizes at least `.99λ` at the incident sites and legal
eligibility (`HDParams.Legal`) on every site consulted by their height rules
(`domBall … Rlong`), selections at all incident sites, a passing realized list of
the prescribed form (own fan at most `T`), and positive retained squared-tilt mass
(`h_F > 0`, 10:142). -/
def groupValid (h : History n N δ) (q : Site n δ) : Prop :=
  (∀ s ∈ incidentSites δ q, ∀ j,
    (998 / 1000 : ℝ) * (hp n δ).lam ≤
        (p10_1kHeightPositionCount (hp n δ) (fun loc => h.pos (s.1, loc)) s.2 j : ℝ) ∧
      (p10_1kHeightPositionCount (hp n δ) (fun loc => h.pos (s.1, loc)) s.2 j : ℝ) ≤
        (1002 / 1000 : ℝ) * (hp n δ).lam) ∧
  (∀ s ∈ incidentSites δ q,
    (∀ j, (99 / 100 : ℝ) * (hp n δ).lam ≤ ((elig M t h s.1 s.2 j).card : ℝ)) ∧
    (hp n δ).Legal (fun loc => h.pos (s.1, loc)) (elig M t h s.1)
      ((hp n δ).domBall (sliceSites δ s.1) s.2 (hp n δ).Rlong)) ∧
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
    _root_.hammingDist (groupOf δ b).1 (groupOf δ b').1 ≤ 8 ∧
      _root_.hammingDist (groupOf δ b).2 (groupOf δ b').2 ≤ 2 * Rloc n δ + 16

/-- Residual-near even roles (10:288). -/
noncomputable def evenNear {n : ℕ} (δ : ℝ) (a : EvenRole n) : Finset (EvenRole n) :=
  Finset.univ.filter fun a' =>
    _root_.hammingDist (evenSite δ a).1 (evenSite δ a').1 ≤ 8 ∧
      _root_.hammingDist (evenSite δ a).2 (evenSite δ a').2 ≤ 2 * Rloc n δ + 16

/-- Tag-dependence neighbourhood of a slice: special distance at most 4
(10:119–121, 10:263). -/
noncomputable def tagNbhd {n : ℕ} (δ : ℝ) (z : Slice n δ) : Finset (Slice n δ) :=
  Finset.univ.filter fun z' => _root_.hammingDist z z' ≤ 4


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
    (Finset.univ.filter fun z => _root_.hammingDist z q.1 ≤ 1)
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
  classical
  have expect_nonneg {α : Type} [Fintype α] (P : FinProb α) (f : α → ℝ)
      (hf : ∀ x, 0 ≤ f x) : 0 ≤ P.expect f := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (P.nonneg x) (hf x)
  have starLik_nonneg (h : History n N δ) (a : EvenRole n) (ω : OddRole n → Fin N) :
      0 ≤ starLik M t h a ω := by
    unfold starLik
    apply Finset.prod_nonneg
    intro q hq
    apply expect_nonneg
    intro c
    apply Finset.prod_nonneg
    intro b hb
    exact (labLaw M t h b c).nonneg (ω b)
  have subLik_nonneg (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (w : Fin (kT n δ) → Fin N) (ω : OddRole n → Fin N) :
      0 ≤ subLik M t h a c w ω := by
    unfold subLik
    split_ifs
    · exact starLik_nonneg (History.setTuple h c w) a ω
    · exact le_rfl
  have predMass_nonneg (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (ω : OddRole n → Fin N) : 0 ≤ predMass M t h a c ω := by
    unfold predMass
    apply expect_nonneg
    intro w
    exact subLik_nonneg h a c w ω
  have avgMarginal_nonneg (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (ω : OddRole n → Fin N) (x : Fin N) (hm : 0 < predMass M t h a c ω) :
      0 ≤ avgMarginal M t h a c ω x := by
    unfold avgMarginal
    apply Finset.sum_nonneg
    intro w hw
    apply mul_nonneg
    · unfold posterior
      apply div_nonneg
      · exact mul_nonneg ((tuplePrior M t c).nonneg w)
          (subLik_nonneg h a c w ω)
      · exact hm.le
    · exact div_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg (kT n δ))

  have oddRow_nonneg : ∀ h b y, 0 ≤ oddRow M t h b y := by
    intro h b y
    unfold oddRow
    split_ifs
    · apply expect_nonneg
      intro c
      exact (labLaw M t h b c).nonneg y
    · exact le_rfl

  have groupOf_isGroup (b : OddRole n) : IsGroup δ (groupOf δ b) := by
    change (p10_1kOddGroupRoles (mS_le n δ)
      (p10_1kProjectedVertex (mS_le n δ) b.1)).Nonempty
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

  have hStarLikEq (h : History n N δ) (a : EvenRole n)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      starLik M t h a ω = starLik M t h a ω' := by
    unfold starLik
    apply Finset.prod_congr rfl
    intro q hq
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro c hc
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    exact congrArg (fun y => (labLaw M t h b c).w y)
      (hag b (Finset.mem_filter.mp hb).1)

  have hSubLikEq (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (w : Fin (kT n δ) → Fin N) (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      subLik M t h a c w ω = subLik M t h a c w ω' := by
    unfold subLik
    rw [hStarLikEq (History.setTuple h c w) a ω ω' hag]

  have hDelRefEq (h : History n N δ) (a : EvenRole n) (q : Site n δ)
      (L : Finset (ID n δ)) (c : ID n δ) (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      deletionRef M t h a q L c ω = deletionRef M t h a q L c ω' := by
    unfold deletionRef
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    exact congrArg (fun y => (restrictOrSelf (maskedCluster M (t q.1) (h.mask q) j)
      (Finset.univ.filter fun y => ∀ c' ∈ L, c' ≠ c → ∀ i, Hits E G (h.tup c' i) y)).w y)
      (hag b (Finset.mem_filter.mp hb).1)

  have hGroupRefEq (h : History n N δ) (a : EvenRole n) (q : Site n δ)
      (c : ID n δ) (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      groupRef M t h a q c ω = groupRef M t h a q c ω' := by
    unfold groupRef
    congr 1
    apply Finset.sum_congr rfl
    intro L hL
    exact hDelRefEq h a q L c ω ω' hag

  have hRefQEq (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      refQ M t h a c ω = refQ M t h a c ω' := by
    unfold refQ
    apply Finset.prod_congr rfl
    intro q hq
    exact hGroupRefEq h a q c ω ω' hag

  have hPredMassEq (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      predMass M t h a c ω = predMass M t h a c ω' := by
    unfold predMass FinProb.expect
    apply Finset.sum_congr rfl
    intro w hw
    change (tuplePrior M t c).w w * subLik M t h a c w ω =
      (tuplePrior M t c).w w * subLik M t h a c w ω'
    congr 1
    exact hSubLikEq h a c w ω ω' hag

  have hPosteriorEq (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (ω ω' : OddRole n → Fin N) (w : Fin (kT n δ) → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      posterior M t h a c ω w = posterior M t h a c ω' w := by
    simp [posterior, hSubLikEq h a c w ω ω' hag, hPredMassEq h a c ω ω' hag]

  have hAvgMarginalEq (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (ω ω' : OddRole n → Fin N) (x : Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      avgMarginal M t h a c ω x = avgMarginal M t h a c ω' x := by
    unfold avgMarginal
    apply Finset.sum_congr rfl
    intro w hw
    rw [hPosteriorEq h a c ω ω' w hag]

  have hHeavyEq (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      heavy M t h a c ω = heavy M t h a c ω' := by
    ext x
    simp [heavy, hAvgMarginalEq h a c ω ω' x hag]

  have hLightMassEq (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      lightMass M t h a c ω = lightMass M t h a c ω' := by
    simp [lightMass, hHeavyEq h a c ω ω' hag,
      hAvgMarginalEq h a c ω ω' _ hag]

  have hPredOKEq (h : History n N δ) (a : EvenRole n) (c : ID n δ)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      predOK M t h a c ω ↔ predOK M t h a c ω' := by
    simp [predOK, hPredMassEq h a c ω ω' hag, hRefQEq h a c ω ω' hag,
      hLightMassEq h a c ω ω' hag]

  have hPredictiveEq (a : EvenRole n) (h : History n N δ)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      predictive M t a h ω ↔ predictive M t a h ω' := by
    unfold predictive
    constructor
    · rintro ⟨c, hc, hp⟩
      exact ⟨c, hc, (hPredOKEq h a c ω ω' hag).mp hp⟩
    · rintro ⟨c, hc, hp⟩
      exact ⟨c, hc, (hPredOKEq h a c ω ω' hag).mpr hp⟩

  have hEvenRowEq (h : History n N δ) (a : EvenRole n) (x : Fin N)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b ∈ starOf a, ω b = ω' b) :
      evenRow M t h ω a x = evenRow M t h ω' a x := by
    unfold evenRow
    split <;> simp [hPredOKEq h a _ ω ω' hag,
      hAvgMarginalEq h a _ ω ω' x hag, hHeavyEq h a _ ω ω' hag,
      hLightMassEq h a _ ω ω' hag]

  refine ⟨oddRow_nonneg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hv b y
    have hg : groupValid M t h (groupOf δ b) := hv _ (groupOf_isGroup b)
    simp [oddRow, hg]
  · intro h ω a x
    unfold evenRow
    cases hc : centerOf M t h a with
    | none => exact le_rfl
    | some c =>
      change 0 ≤ if predOK M t h a c ω ∧ x ∉ heavy M t h a c ω then
        avgMarginal M t h a c ω x / lightMass M t h a c ω else 0
      split_ifs with hp
      · exact div_nonneg
          (avgMarginal_nonneg h a c ω x hp.1.2.1)
          (le_of_lt hp.1.2.2.2)
      · exact le_rfl
  · intro h ω a hv hp
    obtain ⟨c, hc, hOK⟩ := hp
    have hlight : 0 < lightMass M t h a c ω := hOK.2.2.2
    have hsum : (∑ x : Fin N, evenRow M t h ω a x) =
        (∑ x ∈ Finset.univ \ heavy M t h a c ω,
          avgMarginal M t h a c ω x) / lightMass M t h a c ω := by
      calc
        (∑ x : Fin N, evenRow M t h ω a x) =
            ∑ x ∈ Finset.univ, if x ∉ heavy M t h a c ω then
              avgMarginal M t h a c ω x / lightMass M t h a c ω else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [evenRow, hc, hOK]
        _ = ∑ x ∈ Finset.univ.filter (fun x => x ∉ heavy M t h a c ω),
              avgMarginal M t h a c ω x / lightMass M t h a c ω := by
          rw [← Finset.sum_filter]
        _ = ∑ x ∈ Finset.univ \ heavy M t h a c ω,
              avgMarginal M t h a c ω x / lightMass M t h a c ω := by
          have hset : Finset.univ.filter (fun x : Fin N => x ∉ heavy M t h a c ω) =
              Finset.univ \ heavy M t h a c ω := by
            ext x
            simp
          rw [hset]
        _ = (∑ x ∈ Finset.univ \ heavy M t h a c ω,
              avgMarginal M t h a c ω x) / lightMass M t h a c ω := by
          rw [← Finset.sum_div]
    rw [hsum]
    unfold lightMass
    exact div_self hlight.ne'
  · intro h ω a hv hpredict x hrowne b hadj
    obtain ⟨c, hc, hOK⟩ := hpredict
    have hxnot : x ∉ heavy M t h a c ω := by
      by_contra hx
      have hz : evenRow M t h ω a x = 0 := by simp [evenRow, hc, hOK, hx]
      exact hrowne hz
    have havgNe : avgMarginal M t h a c ω x ≠ 0 := by
      intro hz
      apply hrowne
      simp [evenRow, hc, hOK, hxnot, hz]
    have havgNN := avgMarginal_nonneg h a c ω x hOK.2.1
    have havgPos : 0 < avgMarginal M t h a c ω x := by
      by_contra hn
      exact havgNe (le_antisymm (le_of_not_gt hn) havgNN)
    have hPosteriorNN (w : Fin (kT n δ) → Fin N) :
        0 ≤ posterior M t h a c ω w := by
      unfold posterior
      apply div_nonneg
      · exact mul_nonneg ((tuplePrior M t c).nonneg w)
          (subLik_nonneg h a c w ω)
      · exact hOK.2.1.le
    have hMarginalTermNN (w : Fin (kT n δ) → Fin N) :
        0 ≤ posterior M t h a c ω w *
          (((Finset.univ.filter fun i => w i = x).card : ℝ) / kT n δ) := by
      apply mul_nonneg (hPosteriorNN w)
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hsumPos : 0 < ∑ w : Fin (kT n δ) → Fin N,
        posterior M t h a c ω w *
          (((Finset.univ.filter fun i => w i = x).card : ℝ) / kT n δ) := by
      simpa [avgMarginal] using havgPos
    obtain ⟨w, hw, htermPos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
        (f := fun w : Fin (kT n δ) → Fin N =>
          posterior M t h a c ω w *
            (((Finset.univ.filter fun i => w i = x).card : ℝ) / kT n δ))
        (by intro w hw; exact hMarginalTermNN w)).mp hsumPos
    have hposteriorPos : 0 < posterior M t h a c ω w := by
      by_contra hn
      have hz : posterior M t h a c ω w = 0 :=
        le_antisymm (le_of_not_gt hn) (hPosteriorNN w)
      rw [hz, zero_mul] at htermPos
      exact (lt_irrefl 0 htermPos)
    have hcountFracPos : 0 <
        (((Finset.univ.filter fun i => w i = x).card : ℝ) / kT n δ) := by
      by_contra hn
      have hz : (((Finset.univ.filter fun i => w i = x).card : ℝ) / kT n δ) = 0 :=
        le_antisymm (le_of_not_gt hn) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      rw [hz, mul_zero] at htermPos
      exact (lt_irrefl 0 htermPos)
    have hcountPos : 0 < ((Finset.univ.filter fun i => w i = x).card : ℝ) := by
      by_contra hn
      have hz : ((Finset.univ.filter fun i => w i = x).card : ℝ) = 0 :=
        le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
      have hzero :
          (((Finset.univ.filter fun i => w i = x).card : ℝ) / kT n δ) = 0 := by
        simp [hz]
      rw [hzero] at hcountFracPos
      exact (lt_irrefl 0 hcountFracPos)
    have hcountNatPos : 0 < (Finset.univ.filter fun i => w i = x).card := by
      exact_mod_cast hcountPos
    obtain ⟨ii, hii⟩ := Finset.card_pos.mp hcountNatPos
    have hwi : w ii = x := (Finset.mem_filter.mp hii).2
    have hpriorSubPos : 0 < (tuplePrior M t c).w w * subLik M t h a c w ω := by
      have hposteriorPos' :
          0 < (tuplePrior M t c).w w * subLik M t h a c w ω / predMass M t h a c ω := by
        simpa [posterior] using hposteriorPos
      exact (div_pos_iff_of_pos_right hOK.2.1).mp hposteriorPos'
    have hsubPos : 0 < subLik M t h a c w ω := by
      by_contra hn
      have hsuble : subLik M t h a c w ω ≤ 0 := le_of_not_gt hn
      have hprodle : (tuplePrior M t c).w w * subLik M t h a c w ω ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ((tuplePrior M t c).nonneg w) hsuble
      exact (not_lt_of_ge hprodle) hpriorSubPos
    let h' : History n N δ := History.setTuple h c w
    have hgate : gate M t h' a c := by
      unfold subLik at hsubPos
      split_ifs at hsubPos with hgate
      · exact hgate
      · norm_num at hsubPos
    have hStarPos : 0 < starLik M t h' a ω := by
      simpa [h', subLik, hgate] using hsubPos
    let q : Site n δ := groupOf δ b
    have hqmem : q ∈ incGroups a := by
      change p10_1kProjectedVertex (mS_le n δ) b.1 ∈
        p10_1kIncidentOddGroups (mS_le n δ) a
      exact (p10_1k_mem_incidentOddGroups (mS_le n δ) a _).mpr
        ⟨b, hadj, rfl⟩
    let labelFactor : Site n δ → ClIdx M → ℝ := fun q' z =>
      ∏ b' ∈ (starOf a).filter (fun b' => groupOf δ b' = q'),
        (labLaw M t h' b' z).w (ω b')
    let Q : FinProb (ClIdx M) := clusterLaw M t h' q
    let groupFactor : Site n δ → ℝ := fun q' =>
      (clusterLaw M t h' q').expect (labelFactor q')
    have hstarprod : 0 < ∏ q' ∈ incGroups a, groupFactor q' := by
      change 0 < ∏ q' ∈ incGroups a,
        (clusterLaw M t h' q').expect (fun z =>
          ∏ b' ∈ (starOf a).filter (fun b' => groupOf δ b' = q'),
            (labLaw M t h' b' z).w (ω b'))
      exact hStarPos
    have hlabelNN (q' : Site n δ) (z : ClIdx M) : 0 ≤ labelFactor q' z := by
      unfold labelFactor
      apply Finset.prod_nonneg
      intro b' hb'
      exact (labLaw M t h' b' z).nonneg (ω b')
    have hfactorNN (q' : Site n δ) : 0 ≤ groupFactor q' := by
      unfold groupFactor
      apply expect_nonneg
      exact hlabelNN q'
    have hqfactorNe : groupFactor q ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp (ne_of_gt hstarprod)) q hqmem
    have hqfactorPos : 0 < groupFactor q :=
      lt_of_le_of_ne (hfactorNN q) (Ne.symm hqfactorNe)
    have hsumFactorPos : 0 < ∑ z : ClIdx M, Q.w z * labelFactor q z := by
      simpa [groupFactor, Q, FinProb.expect] using hqfactorPos
    have hsumFactorTermNN (z : ClIdx M) : 0 ≤ Q.w z * labelFactor q z :=
      mul_nonneg (Q.nonneg z) (hlabelNN q z)
    obtain ⟨z, hz, htermPos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
        (f := fun z : ClIdx M => Q.w z * labelFactor q z)
        (by intro z hz; exact hsumFactorTermNN z)).mp hsumFactorPos
    rcases z with ⟨i, j⟩
    have hQatomPos : 0 < Q.w (⟨i, j⟩ : ClIdx M) := by
      by_contra hn
      have hz0 : Q.w (⟨i, j⟩ : ClIdx M) = 0 :=
        le_antisymm (le_of_not_gt hn) (Q.nonneg _)
      rw [hz0, zero_mul] at htermPos
      exact (lt_irrefl 0 htermPos)
    have hlabelProductPos : 0 < labelFactor q (⟨i, j⟩ : ClIdx M) := by
      by_contra hn
      have hz0 : labelFactor q (⟨i, j⟩ : ClIdx M) = 0 :=
        le_antisymm (le_of_not_gt hn) (hlabelNN q _)
      rw [hz0, mul_zero] at htermPos
      exact (lt_irrefl 0 htermPos)
    have hgroupValid : groupValid M t h' q := hgate.2.2 q hqmem
    have htiltSum : 0 < ∑ j' : Fin (M.K (t q.1)), tiltWeight M t h' q j' := by
      rcases hgroupValid with ⟨_, _, _, _, _, hpos⟩
      exact hpos
    have hbranch : groupValid M t h' q ∧
        0 < ∑ j' : Fin (M.K (t q.1)), tiltWeight M t h' q j' :=
      ⟨hgroupValid, htiltSum⟩
    let norm : FinProb (Fin (M.K (t q.1))) :=
      normalizeLaw (tiltWeight M t h' q) (tiltWeight_nonneg M t h' q) htiltSum
    have hQmapPos : 0 <
        (FinProb.map norm (fun j' => (⟨t q.1, j'⟩ : ClIdx M))).w
          (⟨i, j⟩ : ClIdx M) := by
      simpa [Q, clusterLaw, hbranch, norm] using hQatomPos
    change 0 < ∑ j' : Fin (M.K (t q.1)),
      if (⟨t q.1, j'⟩ : ClIdx M) = (⟨i, j⟩ : ClIdx M) then norm.w j' else 0 at hQmapPos
    obtain ⟨j₀, hj₀, hmapTermPos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
        (f := fun j' : Fin (M.K (t q.1)) =>
          if (⟨t q.1, j'⟩ : ClIdx M) = (⟨i, j⟩ : ClIdx M) then norm.w j' else 0)
        (by intro j' hj'; split_ifs <;> simp [norm.nonneg])).mp hQmapPos
    have hmapEq : (⟨t q.1, j₀⟩ : ClIdx M) = (⟨i, j⟩ : ClIdx M) := by
      by_contra hne
      simp [hne] at hmapTermPos
    have hnormPos : 0 < norm.w j₀ := by simpa [hmapEq] using hmapTermPos
    rcases Sigma.mk.inj_iff.mp hmapEq with ⟨hi, hji⟩
    subst i
    have hjEq : j₀ = j := eq_of_heq hji
    have hnormJPos : 0 < norm.w j := by simpa [hjEq] using hnormPos
    have hweightPos : 0 < tiltWeight M t h' q j := by
      have hdivPos : 0 < tiltWeight M t h' q j /
          (∑ j' : Fin (M.K (t q.1)), tiltWeight M t h' q j') := by
        simpa [norm, normalizeLaw] using hnormJPos
      exact (div_pos_iff_of_pos_right htiltSum).mp hdivPos
    have hkept : j ∈ tiltKept M t h' q := by
      unfold tiltWeight at hweightPos
      split_ifs at hweightPos with hkeep
      · exact hkeep
      · norm_num at hweightPos
    have hmassBound : Real.exp (-(3 / 2 : ℝ) * kT n δ *
        (realizedList M t h' q).card) ≤
        lawMassOn (maskedCluster M (t q.1) (h'.mask q) j)
          (hitSet M t h' q) := by
      have hmem : j ∈ Finset.univ.filter (fun j' =>
          Real.exp (-(3 / 2 : ℝ) * kT n δ * (realizedList M t h' q).card) ≤
            lawMassOn (maskedCluster M (t q.1) (h'.mask q) j') (hitSet M t h' q) ∧
          ∀ c' ∈ realizedList M t h' q,
            (if c'.1 = q.1 then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) *
                kT n δ) else Real.exp (-(6 / 5 : ℝ) * kT n δ)) *
              lawMassOn (maskedCluster M (t q.1) (h'.mask q) j')
                (hitSetWithout M t h' q c') ≤
                lawMassOn (maskedCluster M (t q.1) (h'.mask q) j') (hitSet M t h' q)) := by
        simpa [tiltKept] using hkept
      exact (Finset.mem_filter.mp hmem).2.1
    have hlawCond : groupValid M t h' (groupOf δ b) ∧
        Real.exp (-(3 / 2 : ℝ) * kT n δ *
          (realizedList M t h' (groupOf δ b)).card) ≤
        lawMassOn (maskedCluster M (t (groupOf δ b).1)
          (h'.mask (groupOf δ b)) j) (hitSet M t h' (groupOf δ b)) := by
      simpa [q] using And.intro hgroupValid hmassBound
    have hbStar : b ∈ starOf a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
    have hbFactor : b ∈ (starOf a).filter (fun b' => groupOf δ b' = q) :=
      Finset.mem_filter.mpr ⟨hbStar, rfl⟩
    have hlabelProductNe : labelFactor q (⟨t q.1, j⟩ : ClIdx M) ≠ 0 := by
      simpa [q] using (ne_of_gt hlabelProductPos)
    have hlabAtomNe :
        (labLaw M t h' b (⟨t q.1, j⟩ : ClIdx M)).w (ω b) ≠ 0 := by
      unfold labelFactor at hlabelProductNe
      exact (Finset.prod_ne_zero_iff.mp hlabelProductNe) b hbFactor
    have hlabAtomPos : 0 <
        (labLaw M t h' b (⟨t q.1, j⟩ : ClIdx M)).w (ω b) :=
      lt_of_le_of_ne
        ((labLaw M t h' b (⟨t q.1, j⟩ : ClIdx M)).nonneg (ω b))
        (Ne.symm hlabAtomNe)
    have hmassPos : 0 < lawMassOn (maskedCluster M (t q.1) (h'.mask q) j)
        (hitSet M t h' q) := lt_of_lt_of_le (Real.exp_pos _) hmassBound
    have hlabEq : labLaw M t h' b (⟨t q.1, j⟩ : ClIdx M) =
        restrictOrSelf (maskedCluster M (t q.1) (h'.mask q) j)
          (hitSet M t h' q) := by
      unfold labLaw
      rw [ite_eq_left hlawCond]
    have hrestrictedPos : 0 <
        (restrictOrSelf (maskedCluster M (t q.1) (h'.mask q) j)
          (hitSet M t h' q)).w (ω b) := by
      rw [← hlabEq]
      exact hlabAtomPos
    have hωHit : ω b ∈ hitSet M t h' q := by
      by_contra hy
      have hz : (restrictOrSelf (maskedCluster M (t q.1) (h'.mask q) j)
          (hitSet M t h' q)).w (ω b) = 0 := by
        simp [restrictOrSelf, hmassPos, Law.restrict, hy]
      rw [hz] at hrestrictedPos
      exact (lt_irrefl 0 hrestrictedPos)
    let s : Site n δ := evenSite δ a
    have hsEnv : s ∈ p10_1kProjectedNeighborEnvelope q := by
      simpa [s, q, evenSite, groupOf] using
        p10_1k_evenSite_mem_oddGroupEnvelope_of_adjacent (mS_le n δ) a b hadj
    have hsSlice : s.2 ∈ sliceSites δ s.1 := by
      change p10_1k_projectedWord (n - mS n δ)
          (p10_1kResidualWord (mS_le n δ) a.1) ∈
        p10_1kProjectedEvenSites (mS_le n δ)
          (p10_1kSpecialSlice (mS_le n δ) a.1)
      exact p10_1kProjectedEvenRole_mem_sites (mS_le n δ) a
    have hsInc : s ∈ incidentSites δ q := by
      unfold incidentSites
      exact Finset.mem_filter.mpr ⟨hsEnv, hsSlice⟩
    have hrealized : c ∈ realizedList M t h' q := by
      cases hs : selected M t h' s with
      | none =>
        have hselNone : selected M t h' (evenSite δ a) = none := by
          simpa [s] using hs
        have hfalse : False := by
          simpa [centerOf, hselNone] using hgate.1
        exact hfalse.elim
      | some loc =>
        have hpair : (s.1, loc) = c := by
          simpa [centerOf, s, hs] using hgate.1
        have hloc : loc = c.2 := congrArg Prod.snd hpair
        have hsel : selected M t h' s = some c.2 := by
          simp [hs, hloc]
        have hId : (s.1, c.2) = c := by
          calc
            (s.1, c.2) = (s.1, loc) := by rw [hloc]
            _ = c := hpair
        unfold realizedList
        apply Finset.mem_biUnion.mpr
        refine ⟨s, hsInc, ?_⟩
        simp [hsel, hId]
    have hcommon : ∀ c' ∈ realizedList M t h' q, ∀ i,
        Hits E G (History.tup h' c' i) (ω b) := by
      simpa [hitSet] using (Finset.mem_filter.mp hωHit).2
    have hhit := hcommon c hrealized ii
    simpa [h', History.tup, History.setTuple, hwi] using hhit
  · intro a h ω ω' hag
    exact propext (hPredictiveEq a h ω ω' hag)
  · intro a h x ω ω' hag
    exact hEvenRowEq h a x ω ω' hag
  · intro y b
    unfold oddMean
    apply mul_nonneg (Nat.cast_nonneg N)
    apply expect_nonneg
    intro h
    exact oddRow_nonneg h b y
  · intro x a
    unfold evenMean
    apply mul_nonneg (Nat.cast_nonneg N)
    apply expect_nonneg
    intro h
    apply Finset.sum_nonneg
    intro c hc
    apply mul_nonneg ((FinProb.pi (clusterLaw M t h)).nonneg c)
    apply expect_nonneg
    intro ω
    exact (show 0 ≤ evenRow M t h ω a x from by
      unfold evenRow
      cases centerOf M t h a <;> simp
      split_ifs with hp
      · exact div_nonneg
          (avgMarginal_nonneg h a _ ω x hp.1.2.1)
          (le_of_lt hp.1.2.2.2)
      · exact le_rfl)

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

set_option maxHeartbeats 4000000 in
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
  classical
  have hδζ : δ < ζ / 2000 := by
    have hmin : min (min η₀ ζ) 1 ≤ ζ :=
      (min_le_left _ _).trans (min_le_right _ _)
    exact lt_of_lt_of_le hδsmall (div_le_div_of_nonneg_right hmin (by norm_num))
  have hNpow : 500 * δ < ζ := by nlinarith [hδζ]
  have hCountPow := Lane_q_s10_d3.eventually_power_gap
    (a := 0) (b := 200 * δ) (c := 2) (by linarith) (by norm_num)
  have hConstPow := Lane_q_s10_d3.eventually_power_gap
    (a := 0) (b := ζ) (c := 8) (by linarith) (by norm_num)
  have hTiltPow := Lane_q_s10_d3.eventually_power_gap
    (a := 500 * δ) (b := ζ) (c := 72) hNpow (by norm_num)
  have hLogPow := Lane_q_s10_d3.eventually_log_fiber_gap hζ
  have hBudgetPow := Lane_q_s10_d3.eventually_retainedBudgetUpper_lt_half hδ
  have hBasic : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  have hEvents : ∀ᶠ n : ℕ in Filter.atTop,
      2 ≤ n ∧ 8 ≤ (n : ℝ) ^ ζ ∧ 72 * (n : ℝ) ^ (500 * δ) ≤ (n : ℝ) ^ ζ ∧
        2 * ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤ (n : ℝ) ^ ζ / 8 ∧
          Lane_q_s10_d3.retainedBudgetUpper n δ < 1 / 2 ∧
            2 ≤ (n : ℝ) ^ (200 * δ) := by
    filter_upwards [hBasic, hConstPow, hTiltPow, hLogPow, hBudgetPow, hCountPow]
      with n hn2 hconst htilt hlog hbudget hcount
    exact ⟨hn2, by simpa using hconst, htilt, hlog, hbudget, by simpa using hcount⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hEvents
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y G M t hN
  rcases hn₀ n hn with ⟨hn2, hconst, htilt, hlog, hbudgetSmall, hcountPow⟩
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity : 0 < 2 ^ n) hN
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnζ : 0 < (n : ℝ) ^ ζ := Real.rpow_pos_of_pos hnreal ζ
  have hlogTwo : Real.log 2 ≤ (n : ℝ) ^ ζ / 8 := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    nlinarith [hconst, hlog2]
  have hTiltBound : 9 * (n : ℝ) ^ (500 * δ) ≤ (n : ℝ) ^ ζ / 8 := by
    nlinarith [htilt]
  have hscale := p10_1kFixedListScale_rounding_bounds n δ hn2 hδ
  have hkUpper : (kT n δ : ℝ) ≤ 2 * (n : ℝ) ^ (300 * δ) := hscale.2.1
  have hblockUpper : (p10_1kFixedListBlockCount n δ : ℝ) ≤
      3 * (n : ℝ) ^ (200 * δ) := hscale.2.2
  have hspecial : mS n δ ≤ p10_1kSpecialCount n δ := min_le_left _ _
  have hlistScaleNat : TT n δ + mS n δ ≤ p10_1kFixedListBlockCount n δ := by
    dsimp [p10_1kFixedListBlockCount, TT]
    omega
  have hlistScale : (TT n δ + mS n δ : ℝ) ≤ 3 * (n : ℝ) ^ (200 * δ) := by
    calc
      (TT n δ + mS n δ : ℝ) ≤ (p10_1kFixedListBlockCount n δ : ℝ) := by
        exact_mod_cast hlistScaleNat
      _ ≤ 3 * (n : ℝ) ^ (200 * δ) := hblockUpper
  have hkr : (kT n δ : ℝ) * (TT n δ + mS n δ : ℝ) ≤
      6 * (n : ℝ) ^ (500 * δ) := by
    calc
      (kT n δ : ℝ) * (TT n δ + mS n δ : ℝ) ≤
          (2 * (n : ℝ) ^ (300 * δ)) * (3 * (n : ℝ) ^ (200 * δ)) :=
        mul_le_mul hkUpper hlistScale (by positivity) (by positivity)
      _ = 6 * ((n : ℝ) ^ (300 * δ) * (n : ℝ) ^ (200 * δ)) := by ring
      _ = 6 * (n : ℝ) ^ (500 * δ) := by
        rw [← Real.rpow_add hnreal]
        rw [show 300 * δ + 200 * δ = 500 * δ by ring]

  have flip_of_dist : ∀ {d : ℕ} (s z : Fin d → Bool), _root_.hammingDist s z = 1 →
      ∃ i : Fin d, z = p10_1kFlipCoordinate s i := by
    intro d s z hdist
    classical
    have hcard : (Finset.univ.filter (fun i : Fin d => s i ≠ z i)).card = 1 := by
      simpa [_root_.hammingDist] using hdist
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    refine ⟨i, ?_⟩
    funext j
    have hj : s j ≠ z j ↔ j = i := by
      have hmem : j ∈ Finset.univ.filter (fun k : Fin d => s k ≠ z k) ↔ j = i := by
        rw [hi]
        simp
      simpa using hmem
    by_cases hji : j = i
    · subst j
      have hne : s i ≠ z i := hj.2 rfl
      cases hs : s i <;> cases hz : z i <;> simp_all [p10_1kFlipCoordinate]
    · have heq : s j = z j := by
        by_contra hne
        exact hji (hj.1 hne)
      simp [p10_1kFlipCoordinate, hji, heq]

  have hListCard : ∀ h q, groupValid M t h q →
      (realizedList M t h q).card ≤ TT n δ + mS n δ := by
    intro h q hgv
    rcases hgv with ⟨_, _, _, hL, _, _⟩
    let L := realizedList M t h q
    rcases (Finset.mem_filter.mp hL).2 with ⟨hOwn, hAdj, hOne⟩
    let own := L.filter (fun c => c.1 = q.1)
    let exts := L.filter (fun c => c.1 ≠ q.1)
    have hpart : L = own ∪ exts := by
      ext c
      by_cases hc : c ∈ L <;> by_cases hq : c.1 = q.1 <;>
        simp [own, exts, hc, hq]
    have hdisj : Disjoint own exts := by
      apply Finset.disjoint_left.mpr
      intro c hcOwn hcExt
      exact (Finset.mem_filter.mp hcExt).2 (Finset.mem_filter.mp hcOwn).2
    have hcardPart : L.card = own.card + exts.card := by
      rw [hpart, Finset.card_union_of_disjoint hdisj]
    let B := exts.image (fun c : ID n δ => c.1)
    let Adj := (Finset.univ : Finset (Fin (mS n δ))).image
      (fun i => p10_1kFlipCoordinate q.1 i)
    have hcover : ∀ c ∈ exts, c.1 ∈ B := by
      intro c hc
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    have hsumFib : exts.card = ∑ z ∈ B, (exts.filter (fun c => c.1 = z)).card := by
      simpa [B] using Finset.card_eq_sum_card_fiberwise hcover
    have hBsub : B ⊆ Adj := by
      intro z hz
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
      have hcL : c ∈ L := (Finset.mem_filter.mp hc).1
      have hcNot : c.1 ≠ q.1 := (Finset.mem_filter.mp hc).2
      have hdist : _root_.hammingDist c.1 q.1 = 1 := by
        rcases hAdj c hcL with hsame | hfar
        · exact False.elim (hcNot hsame)
        · exact hfar
      have hdist' : _root_.hammingDist q.1 c.1 = 1 := by
        rw [_root_.hammingDist_comm]
        exact hdist
      obtain ⟨i, hflip⟩ := flip_of_dist q.1 c.1 hdist'
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hflip.symm⟩
    have hcardExt : exts.card ≤ mS n δ := by
      calc
        exts.card = B.card := by
          rw [hsumFib]
          calc
            (∑ z ∈ B, (exts.filter (fun c => c.1 = z)).card) =
                ∑ z ∈ B, 1 := by
              apply Finset.sum_congr rfl
              intro z hz
              obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
              have hdist : _root_.hammingDist c.1 q.1 = 1 := by
                rcases hAdj c (Finset.mem_filter.mp hc).1 with hsame | hfar
                · exact False.elim ((Finset.mem_filter.mp hc).2 hsame)
                · exact hfar
              have hnot : c.1 ≠ q.1 := by
                intro heq
                rw [heq] at hdist
                simp at hdist
              have hone := hOne c.1 hdist
              have hfilt : exts.filter (fun c' => c'.1 = c.1) =
                  L.filter (fun c' => c'.1 = c.1) := by
                ext c'
                simp only [Finset.mem_filter]
                constructor
                · rintro ⟨hcExt', hcEq⟩
                  exact ⟨(Finset.mem_filter.mp hcExt').1, hcEq⟩
                · rintro ⟨hcL', hcEq⟩
                  have hcNot' : c'.1 ≠ q.1 := by
                    rw [hcEq]
                    exact hnot
                  exact ⟨Finset.mem_filter.mpr ⟨hcL', hcNot'⟩, hcEq⟩
              rw [hfilt]
              exact hone
            _ = B.card := by simp
        _ ≤ Adj.card := Finset.card_le_card hBsub
        _ ≤ mS n δ := by
          calc
            Adj.card ≤ (Finset.univ : Finset (Fin (mS n δ))).card := Finset.card_image_le
            _ = mS n δ := by simp
    calc
      L.card = own.card + exts.card := hcardPart
      _ ≤ TT n δ + mS n δ := Nat.add_le_add hOwn hcardExt

  have hListPositive : ∀ h q, groupValid M t h q → 1 ≤ (realizedList M t h q).card := by
    intro h q hgv
    rcases hgv with ⟨_, _, _, hL, _, _⟩
    let L := realizedList M t h q
    rcases (Finset.mem_filter.mp hL).2 with ⟨_, _, hOne⟩
    have hspecial : 1 ≤ p10_1kSpecialCount n δ := by
      have hfloor : (n : ℝ) ^ (200 * δ) <
          (p10_1kSpecialCount n δ : ℝ) + 1 := by
        dsimp [p10_1kSpecialCount]
        exact Nat.lt_floor_add_one _
      have hcast : (1 : ℝ) ≤ (p10_1kSpecialCount n δ : ℝ) := by
        nlinarith [hcountPow, hfloor]
      exact_mod_cast hcast
    have hmpos : 0 < mS n δ := by
      dsimp [mS]
      omega
    let i : Fin (mS n δ) := ⟨0, hmpos⟩
    let z := p10_1kFlipCoordinate q.1 i
    have hback : p10_1kFlipCoordinate z i = q.1 := by
      funext j
      by_cases hji : j = i <;> simp [z, p10_1kFlipCoordinate, hji]
    have hdist : _root_.hammingDist z q.1 = 1 := by
      rw [← hback]
      exact p10_1kFlipCoordinate_hammingDist (mS n δ) z i
    have hcard := hOne z hdist
    have hnon : (L.filter (fun c => c.1 = z)).Nonempty := by
      exact Finset.card_pos.mp (by rw [hcard]; norm_num)
    obtain ⟨c, hc⟩ := hnon
    have hLnon : L.Nonempty := ⟨c, (Finset.mem_filter.mp hc).1⟩
    have hpos : 0 < L.card := Finset.card_pos.mpr hLnon
    simpa [L] using (Nat.succ_le_iff.mpr hpos)

  have hMaskAgg : ∀ (h : History n N δ) (q : Site n δ) (y : Fin N),
      ∑ j, (maskedPrior M (t q.1) (h.mask q)).w j *
        (maskedCluster M (t q.1) (h.mask q) j).w y ≤
          4 * Real.exp ((n : ℝ) ^ δ) / N := by
    intro h q y
    let i := t q.1
    let S := h.mask q
    by_cases hPerm : Permitted M i S
    · let ρ₀ := prior M i
      let D₀ := M.D i
      let R := keptClusters M i S
      let ν := Law.mix ρ₀ D₀
      have hR : (1 / 2 : ℝ) ≤ FinProb.pr ρ₀ (fun j => j ∈ R) := by
        simpa [Permitted, ρ₀, R, prior] using hPerm
      have hRpos : 0 < FinProb.pr ρ₀ (fun j => j ∈ R) :=
        lt_of_lt_of_le (by norm_num) hR
      let ρc := FinProb.cond ρ₀ (fun j => j ∈ R) hRpos
      have hmask : ∀ j ∈ R, (1 / 2 : ℝ) ≤ lawMassOn (D₀ j) S := by
        intro j hj
        simpa [R, keptClusters] using (Finset.mem_filter.mp hj).2
      have hagg : ∀ z, ∑ j, ρ₀.w j * (D₀ j).w z ≤ 1 * ν.w z := by
        intro z
        have heq : (∑ j, ρ₀.w j * (D₀ j).w z) = ν.w z := by
          simp [ν, ρ₀, prior, Law.mix]
        rw [heq]
        change ν.w z ≤ 1 * ν.w z
        simp
      have hpriorEq (j : Fin (M.K i)) :
          (maskedPrior M i S).w j = ρc.w j := by
        simp [maskedPrior, hPerm, ρc, ρ₀, R, prior]
      let y₀ : Fin N := ⟨0, by omega⟩
      have hlawEq (j : Fin (M.K i)) (hj : j ∈ R) :
          (maskedCluster M i S j).w y =
            (p10_1kMaskClusterLaw D₀ S y₀ j).w y := by
        have hhalf := hmask j hj
        have hmass : 0 < lawMassOn (D₀ j) S :=
          lt_of_lt_of_le (by norm_num) hhalf
        simp [maskedCluster, hPerm, S, R, ρ₀, D₀, prior, hj,
          p10_1kMaskClusterLaw, restrictOrSelf, hmass, y₀]
      have hsumEq :
          (∑ j, (maskedPrior M i S).w j * (maskedCluster M i S j).w y) =
            ∑ j, ρc.w j * (p10_1kMaskClusterLaw D₀ S y₀ j).w y := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjR : j ∈ R
        · rw [hpriorEq j, hlawEq j hjR]
        · have hc : ρc.w j = 0 := by simp [ρc, FinProb.cond, hjR]
          rw [hpriorEq j]
          simp [hc]
      have hhelper := p10_1k_maskedClusterAggregate_le
        ρ₀ D₀ ν S R y₀ 1 hR hmask hagg y
      have hνwidth : ν.w y ≤ Real.exp ((n : ℝ) ^ δ) / N := by
        simpa [ν, ρ₀, prior, Law.mix] using M.ν_width i y
      have hhelper' :
          (∑ j, ρc.w j * (p10_1kMaskClusterLaw D₀ S y₀ j).w y) ≤
            4 * ν.w y := by simpa using hhelper
      calc
        (∑ j, (maskedPrior M i S).w j * (maskedCluster M i S j).w y) =
            ∑ j, ρc.w j * (p10_1kMaskClusterLaw D₀ S y₀ j).w y := hsumEq
        _ ≤ 4 * ν.w y := hhelper'
        _ ≤ 4 * Real.exp ((n : ℝ) ^ δ) / N := by
          calc
            4 * ν.w y ≤ 4 * (Real.exp ((n : ℝ) ^ δ) / N) :=
              mul_le_mul_of_nonneg_left hνwidth (by norm_num)
            _ = 4 * Real.exp ((n : ℝ) ^ δ) / N := by ring
    · have hbase : (∑ j, (maskedPrior M i S).w j *
          (maskedCluster M i S j).w y) = ∑ j, M.lam i j * (M.D i j).w y := by
        simp [maskedPrior, maskedCluster, hPerm, prior, i, S]
      have hwidth := M.ν_width i y
      have hnonneg : 0 ≤ Real.exp ((n : ℝ) ^ δ) / N :=
        div_nonneg (Real.exp_nonneg _) (by positivity)
      calc
        (∑ j, (maskedPrior M i S).w j * (maskedCluster M i S j).w y) =
            ∑ j, M.lam i j * (M.D i j).w y := hbase
        _ ≤ Real.exp ((n : ℝ) ^ δ) / N := hwidth
        _ ≤ 4 * Real.exp ((n : ℝ) ^ δ) / N := by
          calc
            Real.exp ((n : ℝ) ^ δ) / N ≤ 4 * (Real.exp ((n : ℝ) ^ δ) / N) :=
              by nlinarith [hnonneg]
            _ = 4 * Real.exp ((n : ℝ) ^ δ) / N := by ring

  have hMaskAtom : ∀ (h : History n N δ) (q : Site n δ) (i : M.I)
      (j : Fin (M.K i)) (y : Fin N),
      (maskedCluster M i (h.mask q) j).w y ≤ 2 * Real.exp (-(n : ℝ) ^ ζ) := by
    intro h q i j y
    let S := h.mask q
    by_cases hPerm : Permitted M i S
    · by_cases hj : j ∈ keptClusters M i S
      · have hhalf : (1 / 2 : ℝ) ≤ lawMassOn (M.D i j) S := by
          simpa [keptClusters] using (Finset.mem_filter.mp hj).2
        have hmass : 0 < lawMassOn (M.D i j) S :=
          lt_of_lt_of_le (by norm_num) hhalf
        have hrestr := p10_1k_restrict_atom_le_two (M.D i j) S hhalf y
        have hcluster : maskedCluster M i S j = Law.restrict (M.D i j) S hmass := by
          simp [maskedCluster, hPerm, hj, restrictOrSelf, hmass]
        rw [hcluster]
        calc
          (Law.restrict (M.D i j) S hmass).w y ≤ 2 * (M.D i j).w y := hrestr
          _ ≤ 2 * Real.exp (-(n : ℝ) ^ ζ) :=
            mul_le_mul_of_nonneg_left (M.D_atom i j y) (by norm_num)
      · have hcluster : maskedCluster M i S j = M.D i j := by
          simp [maskedCluster, hPerm, hj, S]
        rw [hcluster]
        calc
          (M.D i j).w y ≤ Real.exp (-(n : ℝ) ^ ζ) := M.D_atom i j y
          _ ≤ 2 * Real.exp (-(n : ℝ) ^ ζ) := by
            nlinarith [Real.exp_nonneg (-(n : ℝ) ^ ζ)]
    · have hcluster : maskedCluster M i S j = M.D i j := by
        simp [maskedCluster, hPerm, S]
      rw [hcluster]
      calc
        (M.D i j).w y ≤ Real.exp (-(n : ℝ) ^ ζ) := M.D_atom i j y
        _ ≤ 2 * Real.exp (-(n : ℝ) ^ ζ) := by
          nlinarith [Real.exp_nonneg (-(n : ℝ) ^ ζ)]

  have hLabStrong : ∀ (h : History n N δ) (b : OddRole n)
      (c : ClIdx M) (y : Fin N),
      (labLaw M t h b c).w y ≤
        2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) := by
    intro h b c y
    let q := groupOf δ b
    let F := hitSet M t h q
    let D := maskedCluster M c.1 (h.mask q) c.2
    by_cases hgate : groupValid M t h q ∧
        Real.exp (-(3 / 2 : ℝ) * kT n δ * (realizedList M t h q).card) ≤
          lawMassOn D F
    · have hcard := hListCard h q hgate.1
      have hL : (3 / 2 : ℝ) * kT n δ * (realizedList M t h q).card ≤
          (n : ℝ) ^ ζ / 8 := by
        calc
          (3 / 2 : ℝ) * kT n δ * (realizedList M t h q).card ≤
              (3 / 2 : ℝ) * (kT n δ : ℝ) * (TT n δ + mS n δ : ℝ) := by
            have hkpos : 0 ≤ (kT n δ : ℝ) := Nat.cast_nonneg _
            have hcardR : ((realizedList M t h q).card : ℝ) ≤
                (TT n δ + mS n δ : ℝ) := by exact_mod_cast hcard
            exact mul_le_mul_of_nonneg_left
              hcardR (mul_nonneg (by norm_num) hkpos)
          _ ≤ 9 * (n : ℝ) ^ (500 * δ) := by nlinarith [hkr]
          _ ≤ (n : ℝ) ^ ζ / 8 := hTiltBound
      let Lcap : ℝ := (3 / 2 : ℝ) * (kT n δ : ℝ) *
        (realizedList M t h q).card
      have hMassGate : Real.exp (-Lcap) ≤ lawMassOn D F := by
        simpa [Lcap, mul_assoc, mul_left_comm, mul_comm] using hgate.2
      have hrestricted := p10_1k_restrict_atom_le_of_mass_lower D F
        Lcap hMassGate y
      have hAtom := hMaskAtom h q c.1 c.2 y
      have hEq :
          (labLaw M t h b c).w y ≤
            2 * Real.exp ((3 / 2 : ℝ) * kT n δ *
              (realizedList M t h q).card - (n : ℝ) ^ ζ) := by
        have hMassPos : 0 < lawMassOn D F :=
          lt_of_lt_of_le (Real.exp_pos _) hMassGate
        have hLabEq : labLaw M t h b c = restrictOrSelf D F := by
          unfold labLaw
          have hcond : groupValid M t h (groupOf δ b) ∧
              Real.exp (-(3 / 2 : ℝ) * kT n δ *
                (realizedList M t h (groupOf δ b)).card) ≤
                lawMassOn (maskedCluster M c.1 (h.mask (groupOf δ b)) c.2)
                  (hitSet M t h (groupOf δ b)) := by
            simpa [q, F, D] using hgate
          rw [if_pos hcond]
        have hLabAtom : (labLaw M t h b c).w y =
            (Law.restrict D F hMassPos).w y := by
          have hweight := congrArg (fun L : Law N => L.w y) hLabEq
          simpa [restrictOrSelf, hMassPos] using hweight
        have hLaw : (labLaw M t h b c).w y ≤
            Real.exp ((3 / 2 : ℝ) * kT n δ * (realizedList M t h q).card) * D.w y := by
          rw [hLabAtom]
          exact hrestricted
        calc
          (labLaw M t h b c).w y ≤
              Real.exp ((3 / 2 : ℝ) * kT n δ * (realizedList M t h q).card) * D.w y := hLaw
          _ ≤ Real.exp ((3 / 2 : ℝ) * kT n δ * (realizedList M t h q).card) *
              (2 * Real.exp (-(n : ℝ) ^ ζ)) :=
            mul_le_mul_of_nonneg_left hAtom (Real.exp_nonneg _)
          _ = 2 * Real.exp ((3 / 2 : ℝ) * kT n δ *
              (realizedList M t h q).card - (n : ℝ) ^ ζ) := by
            calc
              _ = 2 * (Real.exp ((3 / 2 : ℝ) * kT n δ *
                  (realizedList M t h q).card) * Real.exp (-(n : ℝ) ^ ζ)) := by ring
              _ = 2 * Real.exp ((3 / 2 : ℝ) * kT n δ *
                  (realizedList M t h q).card - (n : ℝ) ^ ζ) := by
                rw [← Real.exp_add]
                have harg :
                    ((3 / 2 : ℝ) * kT n δ * (realizedList M t h q).card) +
                        (-(n : ℝ) ^ ζ) =
                      (3 / 2 : ℝ) * kT n δ * (realizedList M t h q).card -
                        (n : ℝ) ^ ζ := by ring
                rw [harg]
      calc
        (labLaw M t h b c).w y ≤
            2 * Real.exp ((3 / 2 : ℝ) * kT n δ *
              (realizedList M t h q).card - (n : ℝ) ^ ζ) := hEq
        _ ≤ 2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.exp_le_exp.mpr (by linarith)
    · have hfalse : (labLaw M t h b c).w y = D.w y := by
        unfold labLaw
        have hcond : ¬ (groupValid M t h (groupOf δ b) ∧
            Real.exp (-(3 / 2 : ℝ) * kT n δ *
              (realizedList M t h (groupOf δ b)).card) ≤
              lawMassOn (maskedCluster M c.1 (h.mask (groupOf δ b)) c.2)
                (hitSet M t h (groupOf δ b))) := by
          simpa [q, F, D] using hgate
        rw [if_neg hcond]
      rw [hfalse]
      have hAtom := hMaskAtom h q c.1 c.2 y
      calc
        D.w y ≤ 2 * Real.exp (-(n : ℝ) ^ ζ) := hAtom
        _ ≤ 2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.exp_le_exp.mpr (by linarith)

  have hLabCap : ∀ h b c y,
      (labLaw M t h b c).w y ≤ Real.exp (-(n : ℝ) ^ ζ / 2) := by
    intro h b c y
    have hStrong := hLabStrong h b c y
    have hsmall : 2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) ≤
        Real.exp (-(n : ℝ) ^ ζ / 2) := by
      have heq : 2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) =
          Real.exp (Real.log 2 + ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) := by
        calc
          2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) =
              Real.exp (Real.log 2) * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          _ = Real.exp (Real.log 2 + ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) := by
            rw [← Real.exp_add]
      rw [heq]
      exact Real.exp_le_exp.mpr (by nlinarith [hlogTwo])
    exact hStrong.trans hsmall

  have hRowCap : ∀ h b y, (N : ℝ) * oddRow M t h b y ≤
      8 * Real.exp (2 * kT n δ * (TT n δ + mS n δ) + (n : ℝ) ^ δ) := by
    intro h b y
    let q := groupOf δ b
    by_cases hvalid : groupValid M t h q
    · have hgv : groupValid M t h q := hvalid
      rcases hvalid with ⟨_, _, _, hLmem, hpass, hret⟩
      let L := realizedList M t h q
      let ρ := maskedPrior M (t q.1) (h.mask q)
      let D := maskedCluster M (t q.1) (h.mask q)
      let F := hitSet M t h q
      let r := L.card
      let μL : Fin r → Law N := fun j => M.μ (t (L.equivFin.symm j).1.1)
      let W : Fin r → Fin (kT n δ) → Fin N := fun j => h.tup (L.equivFin.symm j).1
      have hF : fixedListHitSet E G W = F := by
        ext z
        simp only [fixedListHitSet, F, hitSet, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · intro hfix c hc i
          let j : Fin r := L.equivFin ⟨c, hc⟩
          have h := hfix j i
          simpa [W, j, L] using h
        · intro hhit j i
          exact hhit (L.equivFin.symm j).1 (L.equivFin.symm j).2 i
      have hFminus (c : ID n δ) (hc : c ∈ L) :
          fixedListHitSetWithout E G W (L.equivFin ⟨c, hc⟩) =
            hitSetWithout M t h q c := by
        ext z
        simp only [fixedListHitSetWithout, hitSetWithout, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · intro hfix c' hc' hne i
          let j : Fin r := L.equivFin ⟨c', hc'⟩
          have hjne : j ≠ L.equivFin ⟨c, hc⟩ := by
            intro heq
            have heq' : L.equivFin ⟨c', hc'⟩ = L.equivFin ⟨c, hc⟩ := by
              simpa [j] using heq
            exact hne (congrArg Subtype.val (L.equivFin.injective heq'))
          have h := hfix j hjne i
          simpa [W, j, L] using h
        · intro hhit j hjne i
          let c' : ID n δ := (L.equivFin.symm j).1
          have hc' : c' ∈ L := (L.equivFin.symm j).2
          have hne : c' ≠ c := by
            intro heq
            apply hjne
            have hsub : L.equivFin.symm j = ⟨c, hc⟩ := Subtype.ext heq
            calc
              j = L.equivFin (L.equivFin.symm j) := by simp
              _ = L.equivFin ⟨c, hc⟩ := congrArg L.equivFin hsub
          have h := hhit c' hc' hne i
          simpa [W, c', L] using h
      have hsuccess : ¬ fixedListFailure E G ρ D μL (aG n δ) W := by
        simpa [listFails, ρ, D, μL, W, L, q] using hpass
      have hAfullLowerFix :=
        (p10_1k_successfulFixedList_test_bounds E G ρ D μL (aG n δ) W hsuccess).1
      have hAfullLower :
          Real.exp (-2 * (kT n δ : ℝ) * (r : ℝ)) ≤ squaredClusterMass ρ D F := by
        simpa [hF, r, mul_assoc, mul_left_comm, mul_comm] using hAfullLowerFix
      have hrpos : 1 ≤ r := by simpa [r, L] using hListPositive h q hgv
      have hrNat : r ≤ p10_1kFixedListBlockCount n δ := by
        calc
          r ≤ TT n δ + mS n δ := by simpa [r, L] using hListCard h q hgv
          _ ≤ p10_1kFixedListBlockCount n δ := hlistScaleNat
      have hrupper : (r : ℝ) ≤ 3 * (n : ℝ) ^ (200 * δ) := by
        calc
          (r : ℝ) ≤ (p10_1kFixedListBlockCount n δ : ℝ) := by exact_mod_cast hrNat
          _ ≤ 3 * (n : ℝ) ^ (200 * δ) := hblockUpper
      have hkLower : (n : ℝ) ^ (300 * δ) ≤ (kT n δ : ℝ) := by
        simpa [kT, p10_1kTupleListLength] using
          (Nat.le_ceil ((n : ℝ) ^ (300 * δ)))
      have hkrLower : (n : ℝ) ^ (300 * δ) ≤ (kT n δ : ℝ) * (r : ℝ) := by
        calc
          (n : ℝ) ^ (300 * δ) ≤ (kT n δ : ℝ) := hkLower
          _ ≤ (kT n δ : ℝ) * (r : ℝ) := by
            have hrreal : 1 ≤ (r : ℝ) := by exact_mod_cast hrpos
            calc
              (kT n δ : ℝ) = (kT n δ : ℝ) * 1 := by ring
              _ ≤ (kT n δ : ℝ) * (r : ℝ) :=
                mul_le_mul_of_nonneg_left hrreal (by positivity)
      have hgainK : (n : ℝ) ^ (299 * δ) ≤ aG n δ * (kT n δ : ℝ) := by
        have hpEq : (n : ℝ) ^ (-δ) * (n : ℝ) ^ (300 * δ) =
            (n : ℝ) ^ (299 * δ) := by
          rw [← Real.rpow_add hnreal]
          rw [show -δ + 300 * δ = 299 * δ by ring]
        calc
          (n : ℝ) ^ (299 * δ) =
              (n : ℝ) ^ (-δ) * (n : ℝ) ^ (300 * δ) := hpEq.symm
          _ ≤ (n : ℝ) ^ (-δ) * (kT n δ : ℝ) :=
            mul_le_mul_of_nonneg_left hkLower (Real.rpow_nonneg (le_of_lt hnreal) _)
          _ = aG n δ * (kT n δ : ℝ) := by rfl
      have hbudget :
          Real.exp (-((kT n δ : ℝ) * (r : ℝ))) + (r : ℝ) *
            (Real.exp (-((6 / 25 : ℝ) * aG n δ * (kT n δ : ℝ))) +
              Real.exp (-((2 / 5 : ℝ) * (kT n δ : ℝ)))) ≤ 1 / 2 := by
        have hfirst : Real.exp (-((kT n δ : ℝ) * (r : ℝ))) ≤
            Real.exp (-(n : ℝ) ^ (300 * δ)) := by
          exact Real.exp_le_exp.mpr (by linarith [hkrLower])
        have hownExp : Real.exp (-((6 / 25 : ℝ) * aG n δ *
            (kT n δ : ℝ))) ≤ Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hgainK]
        have hownTerm : (r : ℝ) * Real.exp (-((6 / 25 : ℝ) * aG n δ *
            (kT n δ : ℝ))) ≤ 3 * (n : ℝ) ^ (200 * δ) *
              Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) := by
          calc
            (r : ℝ) * Real.exp (-((6 / 25 : ℝ) * aG n δ * (kT n δ : ℝ))) ≤
                (r : ℝ) * Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) :=
              mul_le_mul_of_nonneg_left hownExp (by positivity)
            _ ≤ 3 * (n : ℝ) ^ (200 * δ) *
                Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) :=
              mul_le_mul_of_nonneg_right hrupper (Real.exp_nonneg _)
        have hexternalExp : Real.exp (-((2 / 5 : ℝ) * (kT n δ : ℝ))) ≤
            Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ))) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hkLower]
        have hexternalTerm : (r : ℝ) * Real.exp (-((2 / 5 : ℝ) * (kT n δ : ℝ))) ≤
            3 * (n : ℝ) ^ (200 * δ) *
              Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ))) := by
          calc
            (r : ℝ) * Real.exp (-((2 / 5 : ℝ) * (kT n δ : ℝ))) ≤
                (r : ℝ) * Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ))) :=
              mul_le_mul_of_nonneg_left hexternalExp (by positivity)
            _ ≤ 3 * (n : ℝ) ^ (200 * δ) *
                Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ))) :=
              mul_le_mul_of_nonneg_right hrupper (Real.exp_nonneg _)
        have hbudgetParts : (r : ℝ) *
            (Real.exp (-((6 / 25 : ℝ) * aG n δ * (kT n δ : ℝ))) +
              Real.exp (-((2 / 5 : ℝ) * (kT n δ : ℝ)))) ≤
              3 * (n : ℝ) ^ (200 * δ) *
                Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) +
              3 * (n : ℝ) ^ (200 * δ) *
                Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ))) := by
          rw [mul_add]
          exact add_le_add hownTerm hexternalTerm
        have hbudgetStep :
            Real.exp (-((kT n δ : ℝ) * (r : ℝ))) +
                (r : ℝ) *
                  (Real.exp (-((6 / 25 : ℝ) * aG n δ * (kT n δ : ℝ))) +
                    Real.exp (-((2 / 5 : ℝ) * (kT n δ : ℝ)))) ≤
              Real.exp (-(n : ℝ) ^ (300 * δ)) +
                (3 * (n : ℝ) ^ (200 * δ) *
                  Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) +
                  3 * (n : ℝ) ^ (200 * δ) *
                    Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ)))) := by
          linarith [hfirst, hbudgetParts]
        calc
          Real.exp (-((kT n δ : ℝ) * (r : ℝ))) + (r : ℝ) *
              (Real.exp (-((6 / 25 : ℝ) * aG n δ * (kT n δ : ℝ))) +
                Real.exp (-((2 / 5 : ℝ) * (kT n δ : ℝ)))) ≤
              Real.exp (-(n : ℝ) ^ (300 * δ)) +
                (3 * (n : ℝ) ^ (200 * δ) *
                  Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) +
                    3 * (n : ℝ) ^ (200 * δ) *
                  Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ)))) := hbudgetStep
          _ = Lane_q_s10_d3.retainedBudgetUpper n δ := by
            simp only [Lane_q_s10_d3.retainedBudgetUpper]
            ring
          _ ≤ 1 / 2 := le_of_lt hbudgetSmall
      let A := squaredClusterMass ρ D F
      let hA : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hAfullLower
      obtain ⟨hAfix, hRfix⟩ := p10_1k_successfulFixedList_retainedTilt_half_mass
        E G ρ D μL (aG n δ) W hsuccess hbudget
      let massBad : Fin (M.K (t q.1)) → Prop := fun j =>
        lawMassOn (D j) F < Real.exp (-(3 / 2 : ℝ) *
          ((kT n δ : ℝ) * (r : ℝ)))
      let ratioBad : Fin r → Fin (M.K (t q.1)) → Prop := fun b' j =>
        (FixedListOwnBlock E G ρ D (μL b') (aG n δ) ∧
          lawMassOn (D j) F /
            lawMassOn (D j) (fixedListHitSetWithout E G W b') <
              Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * aG n δ) * (kT n δ : ℝ))) ∨
        (¬ FixedListOwnBlock E G ρ D (μL b') (aG n δ) ∧
          lawMassOn (D j) F /
            lawMassOn (D j) (fixedListHitSetWithout E G W b') <
              Real.exp (-(6 / 5 : ℝ) * (kT n δ : ℝ)))

      let Rgood := p10_1kTiltGoodClusterSet massBad ratioBad
      have hAfixF : 0 < squaredClusterMass ρ D F := by
        simpa [hF] using hAfix
      have hAfixEq : hAfixF = hA := Subsingleton.elim _ _
      have hRfixF : (1 / 2 : ℝ) ≤ FinProb.pr
          (p10_1kSquaredTiltPrior ρ D F hAfixF)
          (fun j => j ∈ p10_1kTiltGoodClusterSet massBad ratioBad) := by
        simpa [hF, massBad, ratioBad, p10_1kTiltGoodClusterSet] using hRfix
      have hRfixA := hRfixF
      rw [hAfixEq] at hRfixA
      have hRgood : (1 / 2 : ℝ) ≤ FinProb.pr
          (p10_1kSquaredTiltPrior ρ D F hA)
          (fun j => j ∈ Rgood) := by
        simpa [Rgood] using hRfixA

      have hPriorPos (j : Fin (M.K (t q.1))) (hj : 0 < ρ.w j) :
          0 < M.lam (t q.1) j := by
        let i := t q.1
        let S := h.mask q
        by_cases hPerm : Permitted M i S
        · let R := keptClusters M i S
          have hhalf : (1 / 2 : ℝ) ≤ FinProb.pr (prior M i) (fun j => j ∈ R) := by
            simpa [Permitted, R, prior, i, S] using hPerm
          have hden : 0 < FinProb.pr (prior M i) (fun j => j ∈ R) :=
            lt_of_lt_of_le (by norm_num) hhalf
          by_cases hkeep : j ∈ R
          ·
            have hweight : ρ.w j = (prior M i).w j /
                FinProb.pr (prior M i) (fun j => j ∈ R) := by
              dsimp [ρ, maskedPrior]
              rw [dif_pos hPerm]
              change (FinProb.cond (prior M i) (fun k => k ∈ R) hden).w j = _
              simp [FinProb.cond, hkeep]
            rw [hweight] at hj
            have hpriorPos : 0 < (prior M i).w j :=
              (div_pos_iff_of_pos_right hden).mp hj
            simpa [prior] using hpriorPos
          · have hz : ρ.w j = 0 := by
              dsimp [ρ, maskedPrior]
              rw [dif_pos hPerm]
              change (FinProb.cond (prior M i) (fun k => k ∈ R) hden).w j = 0
              simp [FinProb.cond, hkeep]
            rw [hz] at hj
            norm_num at hj
        · have hpriorPos : 0 < (prior M i).w j := by
            have hρeq : ρ.w j = (prior M i).w j := by
              dsimp [ρ, maskedPrior]
              rw [dif_neg hPerm]
            rw [hρeq] at hj
            exact hj
          simpa [prior] using hpriorPos

      have hClusterPos (j : Fin (M.K (t q.1))) (z : Fin N)
          (hj : 0 < (D j).w z) : 0 < (M.D (t q.1) j).w z := by
        let i := t q.1
        let S := h.mask q
        by_cases hPerm : Permitted M i S
        · let R := keptClusters M i S
          by_cases hkeep : j ∈ R
          · have hhalf : (1 / 2 : ℝ) ≤ lawMassOn (M.D i j) S := by
              simpa [R, keptClusters] using (Finset.mem_filter.mp hkeep).2
            have hmass : 0 < lawMassOn (M.D i j) S :=
              lt_of_lt_of_le (by norm_num) hhalf
            have hclusterEq : D j = Law.restrict (M.D i j) S hmass := by
              simp [D, maskedCluster, hPerm, R, hkeep, S, i,
                restrictOrSelf, hmass]
            have hrestrPos : 0 < (Law.restrict (M.D i j) S hmass).w z := by
              rw [← hclusterEq]
              exact hj
            by_cases hz : z ∈ S
            · have hweight : (Law.restrict (M.D i j) S hmass).w z =
                  (M.D i j).w z / lawMassOn (M.D i j) S := by
                have hmassEq : lawMassOn (M.D i j) S =
                    ∑ y ∈ S, (M.D i j).w y := rfl
                calc
                  (Law.restrict (M.D i j) S hmass).w z =
                      (M.D i j).w z / (∑ y ∈ S, (M.D i j).w y) := by
                    simp only [Law.restrict, if_pos hz]
                  _ = (M.D i j).w z / lawMassOn (M.D i j) S := by
                    rw [hmassEq]
              rw [hweight] at hrestrPos
              exact (div_pos_iff_of_pos_right hmass).mp hrestrPos
            · simp [Law.restrict, hz] at hrestrPos
          · simpa [D, maskedCluster, hPerm, R, hkeep, S, i] using hj
        · simpa [D, maskedCluster, hPerm, S, i] using hj

      have hOwnSlice (b' : Fin r)
          (hslice : (L.equivFin.symm b').1.1 = q.1) :
          FixedListOwnBlock E G ρ D (μL b') (aG n δ) := by
        intro j hρj z z' hz hz'
        have hlamPos := hPriorPos j hρj
        have hDz := hClusterPos j z hz
        have hDz' := hClusterPos j z' hz'
        have hcode := M.codegree (t q.1) j hlamPos z z' hDz hDz'
        simpa [μL, aG, hslice] using hcode

      have hRsubset : Rgood ⊆ tiltKept M t h q := by
        intro j hj
        classical
        have hgoodMem : ¬ massBad j ∧ ∀ b', ¬ ratioBad b' j := by
          change j ∈ p10_1kTiltGoodClusterSet massBad ratioBad at hj
          simpa [p10_1kTiltGoodClusterSet] using hj
        rcases hgoodMem with ⟨hMassGood, hRatioGood⟩
        have hAbs : Real.exp (-(3 / 2 : ℝ) * kT n δ * L.card) ≤
            lawMassOn (D j) F := by
          apply le_of_not_gt
          intro hlt
          have hlt' : massBad j := by
            dsimp [massBad, r, L]
            convert hlt using 1 <;> congr 1 <;> ring
          exact hMassGood hlt'
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        refine ⟨?_, ?_⟩
        · simpa [L] using hAbs
        · intro c hc
          let b' : Fin r := L.equivFin ⟨c, hc⟩
          have hnotRatio0 := hRatioGood b'
          have hnotRatio :
              ¬ ((FixedListOwnBlock E G ρ D (μL b') (aG n δ) ∧
                    lawMassOn (D j) F / lawMassOn (D j)
                      (hitSetWithout M t h q c) <
                        Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * aG n δ) *
                          (kT n δ : ℝ))) ∨
                  (¬ FixedListOwnBlock E G ρ D (μL b') (aG n δ) ∧
                    lawMassOn (D j) F / lawMassOn (D j)
                      (hitSetWithout M t h q c) <
                        Real.exp (-(6 / 5 : ℝ) * (kT n δ : ℝ)))) := by
            intro hbad
            apply hRatioGood b'
            dsimp [ratioBad]
            rcases hbad with hown | hext
            · have hratio : lawMassOn (D j) F /
                  lawMassOn (D j) (fixedListHitSetWithout E G W b') <
                    Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * aG n δ) *
                      (kT n δ : ℝ)) := by
                rw [hFminus c hc]
                exact hown.2
              exact Or.inl ⟨hown.1, hratio⟩
            · have hratio : lawMassOn (D j) F /
                  lawMassOn (D j) (fixedListHitSetWithout E G W b') <
                    Real.exp (-(6 / 5 : ℝ) * (kT n δ : ℝ)) := by
                rw [hFminus c hc]
                exact hext.2
              exact Or.inr ⟨hext.1, hratio⟩
          have hdenNonneg : 0 ≤ lawMassOn (D j) (hitSetWithout M t h q c) := by
            unfold lawMassOn
            apply Finset.sum_nonneg
            intro z hz
            exact (D j).nonneg z
          have hratioMul {a : ℝ} (ha : 0 < a)
              (hratio : a ≤ lawMassOn (D j) F /
                lawMassOn (D j) (hitSetWithout M t h q c)) :
              a * lawMassOn (D j) (hitSetWithout M t h q c) ≤
                lawMassOn (D j) F := by
            have hdenPos : 0 < lawMassOn (D j) (hitSetWithout M t h q c) := by
              by_contra hnot
              have hzero : lawMassOn (D j) (hitSetWithout M t h q c) = 0 :=
                le_antisymm (le_of_not_gt hnot) hdenNonneg
              rw [hzero, div_zero] at hratio
              exact (not_le_of_gt ha) hratio
            exact (le_div_iff₀ hdenPos).mp hratio
          have hprod :
              (if c.1 = q.1 then
                Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) * (kT n δ : ℝ))
               else Real.exp (-(6 / 5 : ℝ) * (kT n δ : ℝ))) *
                lawMassOn (D j) (hitSetWithout M t h q c) ≤ lawMassOn (D j) F := by
            by_cases hcOwn : c.1 = q.1
            · have hown : FixedListOwnBlock E G ρ D (μL b') (aG n δ) :=
                hOwnSlice b' (by simpa [b'] using hcOwn)
              have hnot : ¬ lawMassOn (D j) F /
                    lawMassOn (D j) (hitSetWithout M t h q c) <
                      Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * aG n δ) *
                        (kT n δ : ℝ)) := by
                intro hlt
                exact hnotRatio (Or.inl ⟨hown, hlt⟩)
              have hratio :
                  Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * aG n δ) *
                    (kT n δ : ℝ)) ≤ lawMassOn (D j) F /
                      lawMassOn (D j) (hitSetWithout M t h q c) :=
                le_of_not_gt hnot
              have hratio' :
                  Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) *
                    (kT n δ : ℝ)) ≤ lawMassOn (D j) F /
                      lawMassOn (D j) (hitSetWithout M t h q c) := by
                simpa only [show (2 / 25 : ℝ) = 8 / 100 by norm_num] using hratio
              simpa [hcOwn] using hratioMul (Real.exp_pos _) hratio'
            · by_cases hOwn : FixedListOwnBlock E G ρ D (μL b') (aG n δ)
              · have hlog2 : Real.log 2 ≤ 1 := by
                  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
                  linarith
                have hthreshold :
                    Real.exp (-(6 / 5 : ℝ) * (kT n δ : ℝ)) ≤
                      Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) *
                        (kT n δ : ℝ)) := by
                  apply Real.exp_le_exp.mpr
                  have hgain : 0 ≤ aG n δ := Real.rpow_nonneg (le_of_lt hnreal) _
                  nlinarith [hlog2, hgain]
                have hnot : ¬ lawMassOn (D j) F /
                    lawMassOn (D j) (hitSetWithout M t h q c) <
                      Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) *
                        (kT n δ : ℝ)) := by
                  intro hlt
                  have hlt' : lawMassOn (D j) F /
                      lawMassOn (D j) (hitSetWithout M t h q c) <
                        Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * aG n δ) *
                          (kT n δ : ℝ)) := by
                    simpa only [show (2 / 25 : ℝ) = 8 / 100 by norm_num] using hlt
                  exact hnotRatio (Or.inl ⟨hOwn, hlt'⟩)
                have hratio :
                    Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * aG n δ) *
                      (kT n δ : ℝ)) ≤ lawMassOn (D j) F /
                        lawMassOn (D j) (hitSetWithout M t h q c) :=
                  le_of_not_gt hnot
                have hratio' := hratioMul (Real.exp_pos _) hratio
                simpa [hcOwn] using le_trans
                  (mul_le_mul_of_nonneg_right hthreshold hdenNonneg) hratio'
              · have hnot : ¬ lawMassOn (D j) F /
                    lawMassOn (D j) (hitSetWithout M t h q c) <
                      Real.exp (-(6 / 5 : ℝ) * (kT n δ : ℝ)) := by
                  intro hlt
                  exact hnotRatio (Or.inr ⟨hOwn, hlt⟩)
                have hratio :
                    Real.exp (-(6 / 5 : ℝ) * (kT n δ : ℝ)) ≤ lawMassOn (D j) F /
                      lawMassOn (D j) (hitSetWithout M t h q c) :=
                  le_of_not_gt hnot
                simpa [hcOwn] using hratioMul (Real.exp_pos _) hratio
          exact hprod
      have hRprob : (1 / 2 : ℝ) ≤ FinProb.pr
          (p10_1kSquaredTiltPrior ρ D F hA)
          (fun j => j ∈ tiltKept M t h q) := by
        have hmono : FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
            (fun j => j ∈ Rgood) ≤ FinProb.pr
              (p10_1kSquaredTiltPrior ρ D F hA)
              (fun j => j ∈ tiltKept M t h q) := by
          unfold FinProb.pr
          apply Finset.sum_le_sum
          intro j hj
          by_cases hjg : j ∈ Rgood
          · have hjk := hRsubset hjg
            simp [hjg, hjk]
          · by_cases hjk : j ∈ tiltKept M t h q
            · simpa [hjg, hjk] using
                (p10_1kSquaredTiltPrior ρ D F hA).nonneg j
            · simp [hjg, hjk]
        exact hRgood.trans hmono
      let Aret := ∑ j, tiltWeight M t h q j
      have hprEq : FinProb.pr (p10_1kSquaredTiltPrior ρ D F hA)
          (fun j => j ∈ tiltKept M t h q) = Aret / A := by
        unfold FinProb.pr
        calc
          _ = ∑ j, tiltWeight M t h q j / A := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hjk : j ∈ tiltKept M t h q
            · rw [if_pos hjk]
              have hweight : (p10_1kSquaredTiltPrior ρ D F hA).w j =
                  ρ.w j * (lawMassOn (D j) F) ^ 2 / A := by
                rfl
              rw [hweight]
              simp [tiltWeight, ρ, D, F, hjk]
            · simp [tiltWeight, hjk]
          _ = Aret / A := by
            rw [← Finset.sum_div]
      have hAretPos : 0 < Aret := by simpa [Aret] using hret
      have hAretLower : A / 2 ≤ Aret := by
        rw [hprEq] at hRprob
        have hprod : (1 / 2 : ℝ) * A ≤ (Aret / A) * A :=
          mul_le_mul_of_nonneg_right hRprob hA.le
        have hcancel : (Aret / A) * A = Aret := by
          field_simp [ne_of_gt hA]
        nlinarith [hprod, hcancel]
      have hAretExp : Real.exp (-2 * (kT n δ : ℝ) * (r : ℝ)) / 2 ≤ Aret := by
        calc
          Real.exp (-2 * (kT n δ : ℝ) * (r : ℝ)) / 2 ≤ A / 2 :=
            div_le_div_of_nonneg_right hAfullLower (by norm_num)
          _ = A / 2 := rfl
          _ ≤ Aret := hAretLower
      have hrecip : 1 / Aret ≤
          2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ)) := by
        apply (div_le_iff₀ hAretPos).2
        have hcancel :
            Real.exp (2 * (kT n δ : ℝ) * (r : ℝ)) *
              Real.exp (-2 * (kT n δ : ℝ) * (r : ℝ)) = 1 := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
          simp
        calc
          1 = (2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ))) *
                (Real.exp (-2 * (kT n δ : ℝ) * (r : ℝ)) / 2) := by
            calc
              1 = (2 / 2) *
                  (Real.exp (2 * (kT n δ : ℝ) * (r : ℝ)) *
                    Real.exp (-2 * (kT n δ : ℝ) * (r : ℝ))) := by
                rw [hcancel]
                norm_num
              _ = (2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ))) *
                    (Real.exp (-2 * (kT n δ : ℝ) * (r : ℝ)) / 2) := by ring
          _ ≤ (2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ))) * Aret :=
            mul_le_mul_of_nonneg_left hAretExp (by positivity)
      have hagg : 0 ≤ ∑ j, ρ.w j * (D j).w y := by
        apply Finset.sum_nonneg
        intro j hj
        exact mul_nonneg (ρ.nonneg j) ((D j).nonneg y)
      have hterm (j : Fin (M.K (t q.1))) :
          (tiltWeight M t h q j / Aret) *
              (labLaw M t h b (⟨t q.1, j⟩ : ClIdx M)).w y ≤
            ρ.w j * (D j).w y / Aret := by
        by_cases hj : j ∈ tiltKept M t h q
        · have hkeep := (Finset.mem_filter.mp hj).2
          have hMassGate : Real.exp (-(3 / 2 : ℝ) * kT n δ *
              (realizedList M t h q).card) ≤ lawMassOn (D j) F := by
            simpa [q, F, D] using hkeep.1
          have hmassPos : 0 < lawMassOn (D j) F :=
            lt_of_lt_of_le (Real.exp_pos _) hMassGate
          have hmassPosRestrict : 0 < ∑ z ∈ F, (D j).w z := by
            simpa [lawMassOn] using hmassPos
          have hMassLe : lawMassOn (D j) F ≤ 1 :=
            p10_1k_lawMassOn_le_one (D j) F
          have hLabEq :
              (labLaw M t h b (⟨t q.1, j⟩ : ClIdx M)).w y =
                (Law.restrict (D j) F hmassPosRestrict).w y := by
            have hcond : groupValid M t h (groupOf δ b) ∧
                Real.exp (-(3 / 2 : ℝ) * kT n δ *
                  (realizedList M t h (groupOf δ b)).card) ≤
                  lawMassOn (maskedCluster M (t q.1) (h.mask q) j)
                    (hitSet M t h (groupOf δ b)) := by
              exact ⟨hgv, by simpa [q, F, D] using hMassGate⟩
            have hLawEq : labLaw M t h b (⟨t q.1, j⟩ : ClIdx M) =
                restrictOrSelf (D j) F := by
              unfold labLaw
              rw [if_pos hcond]
            have hweight := congrArg (fun L : Law N => L.w y) hLawEq
            simpa [restrictOrSelf, hmassPos] using hweight
          have hlabelLE : (Law.restrict (D j) F hmassPosRestrict).w y ≤
              (D j).w y / lawMassOn (D j) F := by
            by_cases hy : y ∈ F
            · simp [Law.restrict, lawMassOn, hy]
            · simp [Law.restrict, hy]
              exact div_nonneg ((D j).nonneg y) hmassPos.le
          have hNum : ρ.w j * (lawMassOn (D j) F) ^ 2 *
              (labLaw M t h b (⟨t q.1, j⟩ : ClIdx M)).w y ≤
                ρ.w j * (D j).w y := by
            calc
              ρ.w j * (lawMassOn (D j) F) ^ 2 *
                  (labLaw M t h b (⟨t q.1, j⟩ : ClIdx M)).w y =
                  ρ.w j * (lawMassOn (D j) F) ^ 2 *
                    (Law.restrict (D j) F hmassPosRestrict).w y := by rw [hLabEq]
              _ ≤
                  ρ.w j * (lawMassOn (D j) F) ^ 2 *
                    ((D j).w y / lawMassOn (D j) F) :=
                mul_le_mul_of_nonneg_left hlabelLE
                  (mul_nonneg (ρ.nonneg j) (sq_nonneg _))
              _ = (ρ.w j * lawMassOn (D j) F) * (D j).w y := by
                field_simp [ne_of_gt hmassPos] <;> ring
              _ ≤ ρ.w j * (D j).w y := by
                apply mul_le_mul_of_nonneg_right _ ((D j).nonneg y)
                nlinarith [ρ.nonneg j, hMassLe]
          simp only [tiltWeight, if_pos hj]
          have hdiv := div_le_div_of_nonneg_right hNum hAretPos.le
          convert hdiv using 1 <;> ring
        · simp only [tiltWeight, if_neg hj]
          calc
            (0 / Aret) * (labLaw M t h b (⟨t q.1, j⟩ : ClIdx M)).w y = 0 := by simp
            _ ≤ ρ.w j * (D j).w y / Aret :=
              div_nonneg (mul_nonneg (ρ.nonneg j) ((D j).nonneg y)) hAretPos.le
      have hrowEq : oddRow M t h b y =
          (clusterLaw M t h q).expect
            (fun c => (labLaw M t h b c).w y) := by
        simp [oddRow, q, hgv]
      have hclusterEq : (clusterLaw M t h q).expect
          (fun c => (labLaw M t h b c).w y) =
            ∑ j, tiltWeight M t h q j / Aret *
              (labLaw M t h b (⟨t q.1, j⟩ : ClIdx M)).w y := by
        rw [clusterLaw, dif_pos ⟨hgv, hret⟩,
          Lane_q_s10_d3.expect_map]
        rfl
      have hrowAgg : oddRow M t h b y ≤
          (∑ j, ρ.w j * (D j).w y) / Aret := by
        rw [hrowEq, hclusterEq]
        calc
          (∑ j, tiltWeight M t h q j / Aret *
              (labLaw M t h b (⟨t q.1, j⟩ : ClIdx M)).w y) ≤
              ∑ j, ρ.w j * (D j).w y / Aret := by
            apply Finset.sum_le_sum
            intro j hj
            exact hterm j
          _ = (∑ j, ρ.w j * (D j).w y) / Aret := by rw [Finset.sum_div]
      have hrowSmall : oddRow M t h b y ≤
          2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ)) *
            (∑ j, ρ.w j * (D j).w y) := by
        calc
          oddRow M t h b y ≤ (∑ j, ρ.w j * (D j).w y) / Aret := hrowAgg
          _ = (∑ j, ρ.w j * (D j).w y) * (1 / Aret) := by ring
          _ ≤ (∑ j, ρ.w j * (D j).w y) *
              (2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ))) :=
            mul_le_mul_of_nonneg_left hrecip hagg
          _ = 2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ)) *
              (∑ j, ρ.w j * (D j).w y) := by ring
      have hNagg : (N : ℝ) * (∑ j, ρ.w j * (D j).w y) ≤
          4 * Real.exp ((n : ℝ) ^ δ) := by
        have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
        have hNratio : (N : ℝ) / N = 1 := div_self (ne_of_gt hNreal)
        calc
          (N : ℝ) * (∑ j, ρ.w j * (D j).w y) ≤
              (N : ℝ) * (4 * Real.exp ((n : ℝ) ^ δ) / N) :=
            mul_le_mul_of_nonneg_left (hMaskAgg h q y) (Nat.cast_nonneg _)
          _ = 4 * Real.exp ((n : ℝ) ^ δ) := by
            calc
              (N : ℝ) * (4 * Real.exp ((n : ℝ) ^ δ) / N) =
                  4 * Real.exp ((n : ℝ) ^ δ) * ((N : ℝ) / N) := by ring
              _ = 4 * Real.exp ((n : ℝ) ^ δ) := by rw [hNratio]; ring
      have hrExp : Real.exp (2 * (kT n δ : ℝ) * (r : ℝ)) ≤
          Real.exp (2 * (kT n δ : ℝ) * (TT n δ + mS n δ : ℝ)) := by
        have hcardR : (r : ℝ) ≤ (TT n δ + mS n δ : ℝ) := by
          exact_mod_cast (by simpa [r, L] using hListCard h q hgv)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hcardR
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      calc
        (N : ℝ) * oddRow M t h b y ≤
            (N : ℝ) * (2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ)) *
              (∑ j, ρ.w j * (D j).w y)) :=
          mul_le_mul_of_nonneg_left hrowSmall (Nat.cast_nonneg _)
        _ = 2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ)) *
              ((N : ℝ) * (∑ j, ρ.w j * (D j).w y)) := by ring
        _ ≤ 2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ)) *
              (4 * Real.exp ((n : ℝ) ^ δ)) :=
          mul_le_mul_of_nonneg_left hNagg (by positivity)
        _ ≤ 8 * Real.exp (2 * (kT n δ : ℝ) *
              (TT n δ + mS n δ : ℝ) + (n : ℝ) ^ δ) := by
          calc
            2 * Real.exp (2 * (kT n δ : ℝ) * (r : ℝ)) *
                (4 * Real.exp ((n : ℝ) ^ δ)) ≤
                2 * Real.exp (2 * (kT n δ : ℝ) *
                  (TT n δ + mS n δ : ℝ)) * (4 * Real.exp ((n : ℝ) ^ δ)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hrExp (by norm_num))
                (by positivity)
            _ = 8 * Real.exp (2 * (kT n δ : ℝ) *
                (TT n δ + mS n δ : ℝ) + (n : ℝ) ^ δ) := by
              calc
                _ = 8 * (Real.exp (2 * (kT n δ : ℝ) *
                    (TT n δ + mS n δ : ℝ)) * Real.exp ((n : ℝ) ^ δ)) := by ring
                _ = 8 * Real.exp (2 * (kT n δ : ℝ) *
                    (TT n δ + mS n δ : ℝ) + (n : ℝ) ^ δ) := by
                  rw [← Real.exp_add]
    · have hzero : oddRow M t h b y = 0 := by
        unfold oddRow
        have hcond : ¬ groupValid M t h (groupOf δ b) := by simpa [q] using hvalid
        rw [if_neg hcond]
      rw [hzero]
      simp
      positivity

  have hGroupCap : ∀ h q c y,
      ∑ b ∈ Finset.univ.filter (fun b => groupOf δ b = q),
        (labLaw M t h b c).w y ≤ Real.exp (-(n : ℝ) ^ ζ / 2) := by
    intro h q c y
    let B : Finset (OddRole n) := Finset.univ.filter (fun b => groupOf δ b = q)
    let Bp := p10_1kOddGroupRoles (mS_le n δ) q
    let d := n - mS n δ
    let S := ∑ i : Fin d.bitIndices.length, d.bitIndices.get i
    have hBpeq : Bp = B := by
      ext b
      simp [Bp, B, p10_1kOddGroupRoles, groupOf, p10_1kProjectedVertex] <;> rfl
    have hcardEq' : Fintype.card Bp = B.card := by
      calc
        Fintype.card Bp = Bp.card := by simpa using (Fintype.card_coe Bp)
        _ = B.card := congrArg Finset.card hBpeq
    have hgroupNat : B.card ≤ 2 ^ S := by
      rw [← hcardEq']
      exact p10_1k_oddGroup_card_le n (mS n δ) (mS_le n δ) q
    have hlogMono : Nat.log 2 d ≤ Nat.log 2 n := by
      exact Nat.log_mono_right (Nat.sub_le n (mS n δ))
    have hSbound : S ≤ (Nat.log 2 n + 1) ^ 2 := by
      calc
        S ≤ (Nat.log 2 d + 1) ^ 2 :=
          Lane_q_s10_d3.bitIndicesExponent_le (d := d)
        _ ≤ (Nat.log 2 n + 1) ^ 2 := by gcongr
    have hSboundR : (S : ℝ) ≤ ((Nat.log 2 n : ℝ) + 1) ^ 2 := by
      exact_mod_cast hSbound
    have hSexp : 2 * (S : ℝ) ≤ (n : ℝ) ^ ζ / 8 := by
      nlinarith [hlog, hSboundR]
    have hcardExp : (B.card : ℝ) ≤ Real.exp ((n : ℝ) ^ ζ / 8) := by
      calc
        (B.card : ℝ) ≤ (2 : ℝ) ^ S := by exact_mod_cast hgroupNat
        _ ≤ Real.exp (2 * (S : ℝ)) := Lane_q_s10_d3.twoPow_le_exp_two S
        _ ≤ Real.exp ((n : ℝ) ^ ζ / 8) := Real.exp_le_exp.mpr hSexp
    have hsumBound :
        (∑ b ∈ B, (labLaw M t h b c).w y) ≤
          (B.card : ℝ) * (2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) := by
      calc
        (∑ b ∈ B, (labLaw M t h b c).w y) ≤
            ∑ b ∈ B, 2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) := by
          apply Finset.sum_le_sum
          intro b hb
          exact hLabStrong h b c y
        _ = (B.card : ℝ) *
            (2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) := by simp
    have hprod : Real.exp ((n : ℝ) ^ ζ / 8) *
        (2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) ≤
          Real.exp (-(n : ℝ) ^ ζ / 2) := by
      have htwo : 2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) =
          Real.exp (Real.log 2 + ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) := by
        calc
          2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) =
              Real.exp (Real.log 2) * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          _ = Real.exp (Real.log 2 + ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) := by
            rw [← Real.exp_add]
      calc
        Real.exp ((n : ℝ) ^ ζ / 8) *
            (2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) =
            Real.exp (Real.log 2 + (n : ℝ) ^ ζ / 8 +
              ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) := by
          rw [htwo, ← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-(n : ℝ) ^ ζ / 2) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hlogTwo]
    calc
      (∑ b ∈ Finset.univ.filter (fun b => groupOf δ b = q),
          (labLaw M t h b c).w y) = ∑ b ∈ B, (labLaw M t h b c).w y := rfl
      _ ≤ (B.card : ℝ) *
          (2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) := hsumBound
      _ ≤ Real.exp ((n : ℝ) ^ ζ / 8) *
          (2 * Real.exp ((n : ℝ) ^ ζ / 8 - (n : ℝ) ^ ζ)) :=
        mul_le_mul_of_nonneg_right hcardExp (by positivity)
      _ ≤ Real.exp (-(n : ℝ) ^ ζ / 2) := hprod

  exact ⟨hRowCap, hLabCap, hGroupCap⟩

/-- **d4** = P10.1f (10:150–153; ~300 lines; lemma-level). A good mask strategy
exists: cheap-label masks from the prices `c_s(y)` (`p10_1f_mask_price_separation`,
`p10_1k_mask_price_response`), chosen per group from the tags at its slice and the
adjacent slices. -/
theorem d4_mask_strategy (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ),
      2 ^ n ≤ N → ∃ σ : MaskStrategy M, GoodStrategy M σ := by
  sorry

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
