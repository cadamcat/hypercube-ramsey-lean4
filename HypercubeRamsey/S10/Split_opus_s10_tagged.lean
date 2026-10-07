import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k
import HypercubeRamsey.S10.Split_opus_s10_tagged_q_s10_d7

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

set_option maxHeartbeats 5000000 in
/-- **d7b** = P10.1i(iii) (10:246–250; ~150 lines; lemma-level): the even row
cap `N p_v^X ≤ e^{(log 2 - .01a)n}` (light part and its mass `c₆a`). -/
theorem d7b_even_row_cap (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
      (G : Colour) (M : MenuData n N E X Y G ζ δ κ) (t : Slice n δ → M.I),
      2 ^ n ≤ N → ∀ h ω a x,
      (N : ℝ) * evenRow M t h ω a x ≤ Real.exp ((Real.log 2 - (1 / 100 : ℝ) * aG n δ) * n) := by
  classical
  obtain ⟨n6, h6⟩ := d6_likelihood_comparison η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
  obtain ⟨nS, hS⟩ := Filter.eventually_atTop.1
    (Lane_q_s10_d7.evenRow_scales_eventually δ hδ (by
      have hmin : min (min η₀ ζ) 1 ≤ 1 := min_le_right _ _
      exact lt_of_lt_of_le hδsmall (div_le_div_of_nonneg_right hmin (by norm_num))))
  refine ⟨max n6 nS, ?_⟩
  intro n hn N E X Y G M t hN h ω a x
  have hn6 : n6 ≤ n := le_trans (le_max_left _ _) hn
  have hnS : nS ≤ n := le_trans (le_max_right _ _) hn
  have hsc := hS n hnS
  have h6spec := h6 n hn6 N E X Y G M t hN
  have hBig : 1000000000000000 ≤ n := hsc.1
  have hδbound : δ < (1 : ℝ) / 2000 := by
    have hmin : min (min η₀ ζ) 1 ≤ 1 := min_le_right _ _
    exact lt_of_lt_of_le hδsmall (div_le_div_of_nonneg_right hmin (by norm_num))
  have hnNat : 0 < n := by omega
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hnOne : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hNnat : 0 < N := by
    have hp : 0 < 2 ^ n := Nat.pow_pos (by omega)
    omega
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hNnat
  let k : ℕ := kT n δ
  let a0 : ℝ := aG n δ
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hcontr : 200 < a0 * (k : ℝ) := by simpa [k, a0, aG] using hsc.2.2.2
    norm_num [k, hk0] at hcontr
  have hkRpos : 0 < (k : ℝ) := Nat.cast_pos.mpr hkpos
  have haPos : 0 < a0 := by
    dsimp [a0, aG]
    exact Real.rpow_pos_of_pos hnPos _
  have haLeOne : a0 ≤ 1 := by
    have hpow : (n : ℝ) ^ (-δ) ≤ (n : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnOne (by linarith [hδ])
    simpa [a0, aG, Real.rpow_zero] using hpow
  have haNid : a0 * (n : ℝ) = (n : ℝ) ^ (1 - δ) := by
    dsimp [a0, aG]
    calc
      (n : ℝ) ^ (-δ) * (n : ℝ) =
          (n : ℝ) ^ (-δ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ (-δ + 1) := by rw [← Real.rpow_add hnPos]
      _ = (n : ℝ) ^ (1 - δ) := by congr 1 <;> ring
  have hscaleWidth : (n : ℝ) ^ δ < a0 * (n : ℝ) / 200 := by
    have h := hsc.2.1
    dsimp [a0, aG] at h ⊢
    nlinarith
  have hscaleLog : Real.log 2 < a0 * (n : ℝ) / 200 := by
    have h := hsc.2.2.1
    dsimp [a0, aG] at h ⊢
    nlinarith
  have hak200 : 200 < a0 * (k : ℝ) := by
    simpa [a0, k, aG] using hsc.2.2.2
  have hakOne : 1 ≤ a0 * (k : ℝ) := by linarith
  have hlog2half : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hanOne : 1 ≤ a0 * (n : ℝ) := by
    have hlarge : 1 < 200 * Real.log 2 := by nlinarith [hlog2half]
    linarith [hscaleLog]
  have haLower : (1 : ℝ) / n ≤ a0 := by
    apply (div_le_iff₀ hnPos).2
    nlinarith [hanOne]
  have haInv : a0⁻¹ ≤ (n : ℝ) := by
    have hdiv : (1 : ℝ) / a0 ≤ (n : ℝ) := by
      apply (div_le_iff₀ haPos).2
      nlinarith [hanOne]
    simpa [one_div] using hdiv
  have hsqrtLower : Real.sqrt (n : ℝ) ≤ a0 * (n : ℝ) := by
    have hpow : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 - δ) :=
      Real.rpow_le_rpow_of_exponent_le hnOne (by linarith [hδbound])
    have hsqrt : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      simpa using Real.sqrt_eq_rpow (n : ℝ)
    rw [hsqrt, haNid]
    exact hpow
  have hnNonneg : 0 ≤ (n : ℝ) := le_of_lt hnPos
  have hdenPos : 0 < (100 : ℝ) ^ 4 * 256 := by positivity
  have hBigR : (1000000000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hBig
  have hlargeDen : 400 * ((100 : ℝ) ^ 4 * 256) ≤ (n : ℝ) := by
    exact le_trans (by norm_num :
      400 * ((100 : ℝ) ^ 4 * 256) ≤ (1000000000000000 : ℝ)) hBigR
  have hquarticNat := Lane_q_s10_d7.exp_quartic_lower
    (x := (n : ℝ) / 100) (by positivity)
  have hquarticNatNum : 400 * (n : ℝ) ≤ ((n : ℝ) / 100) ^ 4 / 256 := by
    have heq : ((n : ℝ) / 100) ^ 4 / 256 = (n : ℝ) ^ 4 / ((100 : ℝ) ^ 4 * 256) := by
      field_simp
      <;> ring
    have hsq : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1)]
    rw [heq]
    apply (le_div_iff₀ hdenPos).2
    calc
      400 * (n : ℝ) * ((100 : ℝ) ^ 4 * 256) ≤ (n : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hlargeDen hnNonneg]
      _ ≤ (n : ℝ) ^ 4 := hsq
  have hexpNat : 400 * (n : ℝ) ≤ Real.exp ((n : ℝ) / 100) :=
    le_trans hquarticNatNum hquarticNat
  have hsqrtQuartic := Lane_q_s10_d7.exp_quartic_lower
    (x := Real.sqrt (n : ℝ) / 100) (by positivity)
  have hsqrtPow : (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) ^ 2 := by
    calc
      (Real.sqrt (n : ℝ)) ^ 4 = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
      _ = (n : ℝ) ^ 2 := by rw [Real.sq_sqrt hnNonneg]
  have hsqrtQuarticNum : 400 * (n : ℝ) ≤
      (Real.sqrt (n : ℝ) / 100) ^ 4 / 256 := by
    have heq : (Real.sqrt (n : ℝ) / 100) ^ 4 / 256 =
        (n : ℝ) ^ 2 / ((100 : ℝ) ^ 4 * 256) := by
      rw [div_pow, hsqrtPow]
      field_simp
      <;> ring
    rw [heq]
    apply (le_div_iff₀ hdenPos).2
    have hmul := mul_le_mul_of_nonneg_right hlargeDen hnNonneg
    calc
      400 * (n : ℝ) * ((100 : ℝ) ^ 4 * 256) ≤ (n : ℝ) ^ 2 := by nlinarith [hmul]
      _ = (n : ℝ) ^ 2 := rfl
  have hexpNorm : 400 * (n : ℝ) ≤ Real.exp (a0 * (n : ℝ) / 100) := by
    calc
      400 * (n : ℝ) ≤ Real.exp (Real.sqrt (n : ℝ) / 100) :=
        le_trans hsqrtQuarticNum hsqrtQuartic
      _ ≤ Real.exp (a0 * (n : ℝ) / 100) :=
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hsqrtLower (by norm_num))
  have haNorm : 400 / a0 ≤ Real.exp (a0 * (n : ℝ) / 100) := by
    calc
      400 / a0 ≤ 400 * (n : ℝ) := by
        change 400 * a0⁻¹ ≤ 400 * (n : ℝ)
        exact mul_le_mul_of_nonneg_left haInv (by norm_num)
      _ ≤ Real.exp (a0 * (n : ℝ) / 100) := hexpNorm

  have local_cap (c : ID n δ) (ω : OddRole n → Fin N)
      (hp : predOK M t h a c ω) :
      ∀ x : Fin N, x ∉ heavy M t h a c ω →
        (N : ℝ) * avgMarginal M t h a c ω x / lightMass M t h a c ω ≤
          Real.exp ((Real.log 2 - (1 / 100 : ℝ) * a0) * n) := by
    intro x hxlight
    have hstar_nonneg (h' : History n N δ) : 0 ≤ starLik M t h' a ω := by
      unfold starLik
      apply Finset.prod_nonneg
      intro q hq
      apply Lane_q_s10_d7.finprob_expect_nonneg
      intro j
      apply Finset.prod_nonneg
      intro b hb
      exact (labLaw M t h' b j).nonneg (ω b)
    have hsub_nonneg (w : Fin k → Fin N) : 0 ≤ subLik M t h a c w ω := by
      by_cases hg : gate M t (h.setTuple c w) a c
      · simpa [subLik, hg] using hstar_nonneg (h.setTuple c w)
      · simp [subLik, hg]
    have hposterior_nonneg (w : Fin k → Fin N) :
        0 ≤ posterior M t h a c ω w := by
      unfold posterior
      exact div_nonneg (mul_nonneg ((tuplePrior M t c).nonneg w) (hsub_nonneg w)) hp.2.1.le
    let Q : HypercubeRamsey.FinProb (Fin k → Fin N) := {
      w := fun w => posterior M t h a c ω w
      nonneg := by
        intro w
        exact hposterior_nonneg w
      sum_eq_one := by
        have hsum :
            (∑ w : Fin k → Fin N,
              (tuplePrior M t c).w w * subLik M t h a c w ω) = predMass M t h a c ω := by
          unfold predMass HypercubeRamsey.FinProb.expect
          rfl
        change ∑ w : Fin k → Fin N,
          ((tuplePrior M t c).w w * subLik M t h a c w ω) /
            predMass M t h a c ω = 1
        rw [← Finset.sum_div, hsum, div_self hp.2.1.ne']
    }
    have havgEq (y : Fin N) :
        avgMarginal M t h a c ω y =
          HypercubeRamsey.averageCoordinateMarginal Q y := by
      classical
      unfold avgMarginal HypercubeRamsey.averageCoordinateMarginal
      have hcount (w : Fin k → Fin N) :
          ((Finset.univ.filter fun i : Fin k => w i = y).card : ℝ) =
            ∑ i : Fin k, (if w i = y then (1 : ℝ) else 0) := by
        rw [Finset.card_filter]
        simp
      have hfreq (w : Fin k → Fin N) :
          (((Finset.univ.filter fun i : Fin k => w i = y).card : ℝ) / (k : ℝ)) =
            (k : ℝ)⁻¹ * ∑ i : Fin k, (if w i = y then (1 : ℝ) else 0) := by
        rw [hcount, div_eq_mul_inv]
        ring
      calc
        ∑ w : Fin k → Fin N, posterior M t h a c ω w *
            (((Finset.univ.filter fun i : Fin k => w i = y).card : ℝ) / (k : ℝ)) =
          ∑ w : Fin k → Fin N, (k : ℝ)⁻¹ *
            ∑ i : Fin k, (if w i = y then posterior M t h a c ω w else 0) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [hfreq]
          calc
            posterior M t h a c ω w *
                ((k : ℝ)⁻¹ * ∑ i : Fin k, (if w i = y then (1 : ℝ) else 0)) =
              (k : ℝ)⁻¹ * (posterior M t h a c ω w *
                ∑ i : Fin k, (if w i = y then (1 : ℝ) else 0)) := by ring_nf
            _ = (k : ℝ)⁻¹ * ∑ i : Fin k,
                posterior M t h a c ω w * (if w i = y then (1 : ℝ) else 0) := by
              rw [Finset.mul_sum]
            _ = (k : ℝ)⁻¹ * ∑ i : Fin k,
                (if w i = y then posterior M t h a c ω w else 0) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              by_cases heq : w i = y <;> simp [heq]
        _ = (k : ℝ)⁻¹ * ∑ i : Fin k,
              ∑ w : Fin k → Fin N, (if w i = y then posterior M t h a c ω w else 0) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
        _ = (k : ℝ)⁻¹ * ∑ i : Fin k, Q.pr (fun w => w i = y) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          unfold HypercubeRamsey.FinProb.pr
          apply Finset.sum_congr rfl
          intro w hw
          simp [Q]
    have htotal :
        ∑ y : Fin N, avgMarginal M t h a c ω y = 1 := by
      calc
        ∑ y : Fin N, avgMarginal M t h a c ω y =
            ∑ y : Fin N, HypercubeRamsey.averageCoordinateMarginal Q y := by
          apply Finset.sum_congr rfl
          intro y hy
          exact havgEq y
        _ = 1 := Lane_q_s10_d7.averageCoordinateMarginal_sum_one Q hkpos
    have hHeavyEq : heavy M t h a c ω =
        HypercubeRamsey.heavyCoordinateSet Q
          ((Real.log 2 - (2 / 100 : ℝ) * a0) * n) := by
      ext y
      simp [heavy, HypercubeRamsey.heavyCoordinateSet, havgEq, a0]
    let u : ℝ := a0 * (k : ℝ) / 100
    let q : ℕ := k - Nat.floor u
    have hfloorLower : a0 * (k : ℝ) / 200 ≤ (Nat.floor u : ℝ) := by
      have hu2 : 2 ≤ u := by dsimp [u]; nlinarith [hak200]
      have hfloor : u < (Nat.floor u : ℝ) + 1 := Nat.lt_floor_add_one u
      dsimp [u] at hfloor hu2 ⊢
      nlinarith
    have hfloorLe : (Nat.floor u : ℕ) ≤ k := by
      have huNonneg : 0 ≤ u := by dsimp [u]; positivity
      have hfloorU : (Nat.floor u : ℝ) ≤ u := Nat.floor_le huNonneg
      have huK : u ≤ (k : ℝ) := by
        dsimp [u]
        nlinarith [haLeOne]
      exact_mod_cast (le_trans hfloorU huK)
    have hqCast : (q : ℝ) = (k : ℝ) - (Nat.floor u : ℝ) := by
      dsimp [q]
      rw [Nat.cast_sub hfloorLe]
    have hqLe : q ≤ k := by dsimp [q]; exact Nat.sub_le _ _
    have hqLower : (1 - a0 / 100) * (k : ℝ) ≤ (q : ℝ) := by
      rw [hqCast]
      have hfloorUpper : (Nat.floor u : ℝ) ≤ a0 * (k : ℝ) / 100 := by
        exact Nat.floor_le (by dsimp [u]; positivity)
      dsimp [u] at hfloorUpper
      nlinarith
    have hqFrac : (q : ℝ) / (k : ℝ) ≤ 1 - a0 / 200 := by
      rw [hqCast]
      apply (div_le_iff₀ hkRpos).2
      have hfloor := hfloorLower
      nlinarith
    have hBpos : 0 < (Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ) := by
      have hlog2 : (1 / 2 : ℝ) < Real.log 2 := hlog2half
      have hcoef : 0 < Real.log 2 - (2 / 100 : ℝ) * a0 := by
        nlinarith [haLeOne]
      exact mul_pos hcoef hnPos
    have hcoef :
        (Real.log 2 - (5 / 100 : ℝ) * a0) -
            (Real.log 2 - (2 / 100 : ℝ) * a0) * (1 - a0 / 100) ≤
          -(2 / 100 : ℝ) * a0 := by
      have hlog2 : Real.log 2 ≤ 1 := by
        have h := Real.log_two_lt_d9
        linarith
      have haLog := mul_le_mul_of_nonneg_left hlog2 haPos.le
      nlinarith [sq_nonneg a0]
    have hlogScaled : (k : ℝ) * Real.log 2 ≤ a0 * (n : ℝ) * (k : ℝ) / 200 := by
      have h := le_of_lt hscaleLog
      have hm := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg k)
      nlinarith
    have hwidthScaled : (k : ℝ) * (n : ℝ) ^ δ ≤
        a0 * (n : ℝ) * (k : ℝ) / 200 := by
      have h := le_of_lt hscaleWidth
      have hm := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg k)
      nlinarith
    have hcoefScaled :
        (k : ℝ) * (n : ℝ) *
            ((Real.log 2 - (5 / 100 : ℝ) * a0) -
              (Real.log 2 - (2 / 100 : ℝ) * a0) * (1 - a0 / 100)) ≤
          (k : ℝ) * (n : ℝ) * (-(2 / 100 : ℝ) * a0) :=
      mul_le_mul_of_nonneg_left hcoef (mul_nonneg (Nat.cast_nonneg k) hnPos.le)
    have harg :
        (k : ℝ) * Real.log 2 +
            ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ) +
              (k : ℝ) * (n : ℝ) ^ δ) -
            ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ) * (q : ℝ)) ≤
          -(1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ) := by
      have hqB := mul_le_mul_of_nonneg_left hqLower hBpos.le
      calc
        _ ≤ (k : ℝ) * Real.log 2 +
            ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ) +
              (k : ℝ) * (n : ℝ) ^ δ) -
            ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ) *
              ((1 - a0 / 100) * (k : ℝ))) := by nlinarith [hqB]
        _ ≤ -(1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ) := by
          nlinarith [hlogScaled, hwidthScaled, hcoefScaled]
    have hpow2 : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
      calc
        (2 : ℝ) ^ k = Real.exp (Real.log ((2 : ℝ) ^ k)) := by
          rw [Real.exp_log (by positivity)]
        _ = Real.exp ((k : ℝ) * Real.log 2) := by rw [Real.log_pow]
    have htailExp :
        (2 : ℝ) ^ k * Real.exp
            ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ) +
              (k : ℝ) * (n : ℝ) ^ δ) *
            Real.exp (-((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) * (q : ℝ)) ≤
          Real.exp (-(1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ)) := by
      rw [hpow2]
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      convert harg using 1 <;> ring
    have htailToN :
        Real.exp (-(1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ)) ≤
          Real.exp (-((n : ℝ) / 100)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hakOne]
    have hinvNat : (Real.exp ((n : ℝ) / 100))⁻¹ ≤ (400 * (n : ℝ))⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hexpNat
    have htailSmall :
        Real.exp (-(1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ)) ≤ a0 / 400 := by
      calc
        _ ≤ Real.exp (-((n : ℝ) / 100)) := htailToN
        _ = (Real.exp ((n : ℝ) / 100))⁻¹ := by rw [Real.exp_neg]
        _ ≤ (400 * (n : ℝ))⁻¹ := hinvNat
        _ = ((1 : ℝ) / (n : ℝ)) / 400 := by field_simp <;> ring
        _ ≤ a0 / 400 := div_le_div_of_nonneg_right haLower (by norm_num)
    have hheavy := HypercubeRamsey.heavyTruncation hNnat hkpos Q
      ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ) +
        (k : ℝ) * (n : ℝ) ^ δ)
      ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ))
      (by
        intro w
        have hlik : subLik M t h a c w ω ≤
            Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) *
              refQ M t h a c ω := h6spec h a c w ω
        have hratio : subLik M t h a c w ω / predMass M t h a c ω ≤
            Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) := by
          have heps : (0 : ℝ) ≤ Real.exp (-((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ))) :=
            Real.exp_nonneg _
          have hs : (0 : ℝ) ≤ Real.exp
              ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) := Real.exp_nonneg _
          have hmul :
              subLik M t h a c w ω *
                  Real.exp (-((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ))) ≤
                Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) *
                  predMass M t h a c ω := by
            have hpLower :
                Real.exp (-((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ))) *
                    refQ M t h a c ω ≤ predMass M t h a c ω := by
              simpa [a0, k] using hp.2.2.1
            calc
              _ ≤ (Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) *
                    refQ M t h a c ω) *
                  Real.exp (-((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ))) :=
                mul_le_mul_of_nonneg_right hlik heps
              _ = Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) *
                    (Real.exp (-((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ))) *
                      refQ M t h a c ω) := by ring
              _ ≤ Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) *
                    predMass M t h a c ω :=
                mul_le_mul_of_nonneg_left hpLower hs
          have hnum : subLik M t h a c w ω ≤
              Real.exp (((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ))) *
                predMass M t h a c ω := by
            have hmul' := mul_le_mul_of_nonneg_right hmul
              (Real.exp_nonneg ((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ)))
            have hcancel :
                Real.exp (-((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ))) *
                    Real.exp ((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ)) = 1 := by
              rw [← Real.exp_add]
              simp
            calc
              subLik M t h a c w ω = subLik M t h a c w ω * 1 := by ring
              _ = subLik M t h a c w ω *
                    (Real.exp (-((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ))) *
                      Real.exp ((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ))) := by rw [hcancel]
              _ = (subLik M t h a c w ω *
                    Real.exp (-((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ)))) *
                      Real.exp ((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ)) := by ring
              _ ≤ (Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) *
                    predMass M t h a c ω) *
                    Real.exp ((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ)) := hmul'
              _ = (Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) *
                    Real.exp ((1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ))) *
                    predMass M t h a c ω := by ring
              _ = Real.exp (((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) +
                    (1 / 100 : ℝ) * a0 * (k : ℝ) * (n : ℝ)) *
                    predMass M t h a c ω := by rw [← Real.exp_add]
              _ = Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) *
                    predMass M t h a c ω := by congr 1 <;> ring
          apply (div_le_iff₀ hp.2.1).2
          exact hnum
        have hratioNN : 0 ≤ subLik M t h a c w ω / predMass M t h a c ω :=
          div_nonneg (hsub_nonneg w) hp.2.1.le
        have htuple : (N : ℝ) ^ k * (tuplePrior M t c).w w ≤
            Real.exp ((k : ℝ) * (n : ℝ) ^ δ) := by
          have hμcap (i : Fin k) :
              (N : ℝ) * (M.μ (t c.1)).w (w i) ≤ Real.exp ((n : ℝ) ^ δ) := by
            calc
              (N : ℝ) * (M.μ (t c.1)).w (w i) ≤
                  (N : ℝ) * (Real.exp ((n : ℝ) ^ δ) / N) :=
                mul_le_mul_of_nonneg_left (M.μ_width (t c.1) (w i)) (Nat.cast_nonneg N)
              _ = Real.exp ((n : ℝ) ^ δ) := by field_simp [ne_of_gt hNpos]
          have hprod : (N : ℝ) ^ k * (tuplePrior M t c).w w =
              ∏ i : Fin k, (N : ℝ) * (M.μ (t c.1)).w (w i) := by
            rw [tuplePrior, p10_1kBlockTupleArrayLaw_weight,
              p10_1kBlockTupleArrayWeight]
            calc
              (N : ℝ) ^ k * ∏ i : Fin k, (M.μ (t c.1)).w (w i) =
                  (∏ i : Fin k, (N : ℝ)) *
                    ∏ i : Fin k, (M.μ (t c.1)).w (w i) := by simp
              _ = ∏ i : Fin k, (N : ℝ) * (M.μ (t c.1)).w (w i) := by
                rw [← Finset.prod_mul_distrib]
          rw [hprod]
          calc
            ∏ i : Fin k, (N : ℝ) * (M.μ (t c.1)).w (w i) ≤
                ∏ _i : Fin k, Real.exp ((n : ℝ) ^ δ) := by
              apply Finset.prod_le_prod₀
              · intro i hi
                exact mul_nonneg (Nat.cast_nonneg N) ((M.μ (t c.1)).nonneg (w i))
              · intro i hi
                exact hμcap i
            _ = Real.exp ((k : ℝ) * (n : ℝ) ^ δ) := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
                ← Real.exp_nat_mul]
        calc
          (N : ℝ) ^ k * Q.w w =
              ((N : ℝ) ^ k * (tuplePrior M t c).w w) *
                (subLik M t h a c w ω / predMass M t h a c ω) := by
                  simp [Q, posterior]
                  ring
          _ ≤ Real.exp ((k : ℝ) * (n : ℝ) ^ δ) *
                Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ)) :=
              mul_le_mul htuple hratio hratioNN (Real.exp_nonneg _)
          _ = Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ) +
                (k : ℝ) * (n : ℝ) ^ δ) := by rw [← Real.exp_add]; congr 1 <;> ring)
    have htail := hheavy.2 q hqLe
    have hHeavyMass :
        (∑ y ∈ heavy M t h a c ω, avgMarginal M t h a c ω y) ≤
          (q : ℝ) / (k : ℝ) +
            (2 : ℝ) ^ k *
              Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ) +
                (k : ℝ) * (n : ℝ) ^ δ) *
              Real.exp (-((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) * (q : ℝ)) := by
      simpa [hHeavyEq, havgEq] using htail
    have htailBound :
        (2 : ℝ) ^ k *
            Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ) +
              (k : ℝ) * (n : ℝ) ^ δ) *
            Real.exp (-((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) * (q : ℝ)) ≤
          a0 / 400 := le_trans htailExp htailSmall
    have hHeavyUpper :
        (∑ y ∈ heavy M t h a c ω, avgMarginal M t h a c ω y) ≤ 1 - a0 / 400 := by
      calc
        _ ≤ (q : ℝ) / (k : ℝ) + a0 / 400 := by
          calc
            _ ≤ (q : ℝ) / (k : ℝ) +
                (2 : ℝ) ^ k *
                  Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * (n : ℝ) +
                    (k : ℝ) * (n : ℝ) ^ δ) *
                  Real.exp (-((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) * (q : ℝ)) := hHeavyMass
            _ ≤ (q : ℝ) / (k : ℝ) + a0 / 400 := by linarith [htailBound]
        _ ≤ 1 - a0 / 400 := by
          calc
            (q : ℝ) / (k : ℝ) + a0 / 400 ≤ (1 - a0 / 200) + a0 / 400 :=
              by linarith [hqFrac]
            _ = 1 - a0 / 400 := by ring
    have hlightEq : lightMass M t h a c ω =
        ∑ y ∈ (heavy M t h a c ω)ᶜ, avgMarginal M t h a c ω y := by
      unfold lightMass
      have hset : Finset.univ \ heavy M t h a c ω = (heavy M t h a c ω)ᶜ := by
        ext y
        simp
      rw [hset]
    have hparts :
        (∑ y ∈ heavy M t h a c ω, avgMarginal M t h a c ω y) +
            lightMass M t h a c ω = 1 := by
      calc
        _ = (∑ y ∈ heavy M t h a c ω, avgMarginal M t h a c ω y) +
            ∑ y ∈ (heavy M t h a c ω)ᶜ, avgMarginal M t h a c ω y := by rw [hlightEq]
        _ = ∑ y, avgMarginal M t h a c ω y := by rw [Finset.sum_add_sum_compl]
        _ = 1 := htotal
    have hlightLower : a0 / 400 ≤ lightMass M t h a c ω := by linarith [hparts, hHeavyUpper]
    have havgCap :
        (N : ℝ) * avgMarginal M t h a c ω x ≤
          Real.exp ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) := by
      have hy : ¬ Real.exp ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) <
          (N : ℝ) * avgMarginal M t h a c ω x := by
        intro hlt
        apply hxlight
        change x ∈ Finset.univ.filter
          (fun z => Real.exp ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) <
            (N : ℝ) * avgMarginal M t h a c ω z)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      exact le_of_not_gt hy
    have hnumNonneg : 0 ≤ Real.exp ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) :=
      Real.exp_nonneg _
    have hlocal :
        (N : ℝ) * avgMarginal M t h a c ω x / lightMass M t h a c ω ≤
          Real.exp ((Real.log 2 - (1 / 100 : ℝ) * a0) * (n : ℝ)) := by
      calc
        (N : ℝ) * avgMarginal M t h a c ω x / lightMass M t h a c ω ≤
            Real.exp ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) /
              lightMass M t h a c ω :=
          div_le_div_of_nonneg_right havgCap hp.2.2.2.le
        _ ≤ Real.exp ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) / (a0 / 400) :=
          div_le_div_of_nonneg_left hnumNonneg (by positivity) hlightLower
        _ = (400 / a0) * Real.exp ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) := by
          field_simp [ne_of_gt haPos]
          <;> ring
        _ ≤ Real.exp (a0 * (n : ℝ) / 100) *
              Real.exp ((Real.log 2 - (2 / 100 : ℝ) * a0) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right haNorm (Real.exp_nonneg _)
        _ = Real.exp ((Real.log 2 - (1 / 100 : ℝ) * a0) * (n : ℝ)) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
    exact hlocal
  unfold evenRow
  cases hcenter : centerOf M t h a with
  | none =>
    simp
    positivity
  | some c =>
    change (N : ℝ) *
        (if predOK M t h a c ω ∧ x ∉ heavy M t h a c ω then
          avgMarginal M t h a c ω x / lightMass M t h a c ω else 0) ≤ _
    by_cases hsuccess : predOK M t h a c ω ∧ x ∉ heavy M t h a c ω
    · have hlocal := local_cap c ω hsuccess.1 x hsuccess.2
      simp [hsuccess]
      have heq :
          (N : ℝ) * (avgMarginal M t h a c ω x / lightMass M t h a c ω) =
            (N : ℝ) * avgMarginal M t h a c ω x / lightMass M t h a c ω := by
        ring_nf
      rw [heq]
      simpa [a0, one_div] using hlocal
    · simp [hsuccess]
      positivity

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
