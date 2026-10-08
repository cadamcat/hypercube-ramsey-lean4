import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k
import HypercubeRamsey.S10.Split_opus_s10_tagged_q_s10_d10

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

set_option maxHeartbeats 400000 in
/-- **d8d** (10:39, 10:267, 10:271; ~300 lines; lemma-level counting): the near
fractions. Residual: special ball of radius 8 times a residual ball of radius
`2R_loc + 16` times projection fibres, at most `e^{n^{1-2δ}} 2^{-n}`; tags: at most
`(m+1)^9 2^{-m}`. -/
theorem d8d_near_fractions (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 2000) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      oddFracOf n δ ≤ Real.exp ((n : ℝ) ^ (1 - 2 * δ)) / 2 ^ n ∧
      evenFracOf n δ ≤ Real.exp ((n : ℝ) ^ (1 - 2 * δ)) / 2 ^ n ∧
      tagFracOf n δ ≤ ((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ) := by
  classical
  let β : ℝ := 1 - 7 * δ
  let γ : ℝ := 1 - 2 * δ
  have hβ : 0 < β := by dsimp [β]; nlinarith [hδsmall]
  have hγ : 0 < γ := by dsimp [γ]; nlinarith [hδsmall]
  have hsmall : δ < 1 / 2000 := hδsmall
  have htop0 := Lane_q_s10_d10.topScale_power_bound δ (8 * δ) hδ (by nlinarith [hsmall])
  have htop : ∀ᶠ n : ℕ in atTop,
      (HypercubeRamsey.topScale n δ (8 * δ) : ℝ) ≤ 4 * (n : ℝ) ^ β := by
    filter_upwards [htop0] with n hn
    have hexp : 1 - 8 * δ + δ = β := by dsimp [β]; ring
    rw [hexp] at hn
    exact hn
  have hlog0 := Lane_q_s10_d10.natLog_add_one_le_rpow_eventually δ hδ
  let Cgap : ℝ := 3472 / δ
  have hCgap : 0 < Cgap := by positivity
  have hgap : ∀ᶠ n : ℕ in atTop, Cgap ≤ (n : ℝ) ^ (4 * δ) := by
    have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (4 * δ)) atTop atTop :=
      (_root_.tendsto_rpow_atTop (by positivity : 0 < 4 * δ)).comp
        tendsto_natCast_atTop_atTop
    exact htend.eventually_ge_atTop Cgap
  have hγlarge : ∀ᶠ n : ℕ in atTop, 4 ≤ (n : ℝ) ^ γ := by
    have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ γ) atTop atTop :=
      (_root_.tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop
    exact htend.eventually_ge_atTop 4
  have hsmallN : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (Filter.Eventually.and htop (Filter.Eventually.and hlog0
      (Filter.Eventually.and hgap (Filter.Eventually.and hγlarge hsmallN))))
  refine ⟨n₀, ?_⟩
  intro n hn
  rcases hn₀ n hn with ⟨htopN, hlogN, hgapN, hγN, hn2⟩
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : 0 < (n : ℝ) := by positivity
  have hpowβ : 1 ≤ (n : ℝ) ^ β := Real.one_le_rpow hnreal hβ.le
  have hpowδβ : (n : ℝ) ^ (2 * δ) ≤ (n : ℝ) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hnreal (by dsimp [β]; nlinarith [hsmall])
  have hmpos : 1 ≤ mS n δ := by
    dsimp [mS]
    apply le_min
    · dsimp [p10_1kSpecialCount]
      apply Nat.le_floor
      exact_mod_cast Real.one_le_rpow hnreal (by positivity : 0 ≤ 200 * δ)
    · omega
  have hmle := mS_le n δ
  let d : ℕ := n - mS n δ
  have hrfloor : ((hp n δ).r : ℝ) ≤ (n : ℝ) ^ (1 - 10 * δ) := by
    dsimp [hp, p10_1kHeightParams]
    exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ (n : ℝ) ^ (1 - 10 * δ)))
  have hrpow : (n : ℝ) ^ (1 - 10 * δ) ≤ (n : ℝ) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hnreal (by dsimp [β]; nlinarith [hδ])
  have hheight : ((hp n δ).H : ℝ) ≤ 4 * (n : ℝ) ^ β := by
    simpa [hp, p10_1kHeightParams] using htopN
  have hRloc : (Rloc n δ : ℝ) ≤ 204 * (n : ℝ) ^ β := by
    dsimp [Rloc]
    push_cast
    have hlogle : (Nat.log 2 n : ℝ) + 1 ≤ (n : ℝ) ^ (2 * δ) := hlogN
    have hlogβ : (Nat.log 2 n : ℝ) + 1 ≤ (n : ℝ) ^ β := hlogle.trans hpowδβ
    nlinarith [hrfloor.trans hrpow, hheight, hlogβ]
  let nearRadius : ℕ := 2 * Rloc n δ + 24 + 2 * (Nat.log 2 n + 1)
  have hnearRadius : (nearRadius : ℝ) ≤ 434 * (n : ℝ) ^ β := by
    dsimp [nearRadius]
    push_cast
    have hlogle : (Nat.log 2 n : ℝ) + 1 ≤ (n : ℝ) ^ (2 * δ) := hlogN
    have hlogβ : (Nat.log 2 n : ℝ) + 1 ≤ (n : ℝ) ^ β := hlogle.trans hpowδβ
    nlinarith [hRloc, hlogβ, hpowβ]
  have hlogNplusPos : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by linarith [hnreal])
  have hlogNplus : Real.log ((n : ℝ) + 1) ≤ (2 / δ) * (n : ℝ) ^ δ := by
    have hNpow : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hnreal hδ.le
    have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ :=
      Real.log_natCast_le_rpow_div n hδ
    have hlogtwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hmul : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by nlinarith
    have hlogmul : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hnpos)
    have hδle : δ ≤ 1 := by linarith [hsmall]
    calc
      Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
        Real.log_le_log (by positivity) hmul
      _ = Real.log 2 + Real.log (n : ℝ) := hlogmul
      _ ≤ 1 + (n : ℝ) ^ δ / δ := add_le_add hlogtwo hlogn
      _ ≤ (2 / δ) * (n : ℝ) ^ δ := by
        have hcoef : 1 ≤ 1 / δ := (le_div_iff₀ hδ).2 (by linarith)
        have hmul : 1 ≤ (1 / δ) * (n : ℝ) ^ δ := by
          calc
            1 = 1 * 1 := by ring
            _ ≤ (1 / δ) * (n : ℝ) ^ δ :=
              mul_le_mul hcoef hNpow (by norm_num) (by positivity)
        rw [show (2 / δ) * (n : ℝ) ^ δ =
            (n : ℝ) ^ δ / δ + (1 / δ) * (n : ℝ) ^ δ by field_simp; ring]
        nlinarith [hmul]
  have hdecay : 2 * (nearRadius : ℝ) * Real.log ((n : ℝ) + 1) ≤
      ((n : ℝ) ^ γ) / 2 := by
    have hprod : 2 * (nearRadius : ℝ) * Real.log ((n : ℝ) + 1) ≤
        (1736 / δ) * (n : ℝ) ^ (1 - 6 * δ) := by
      calc
        2 * (nearRadius : ℝ) * Real.log ((n : ℝ) + 1) ≤
            2 * (434 * (n : ℝ) ^ β) * ((2 / δ) * (n : ℝ) ^ δ) := by
          calc
            2 * (nearRadius : ℝ) * Real.log ((n : ℝ) + 1) ≤
                2 * (434 * (n : ℝ) ^ β) * Real.log ((n : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hnearRadius (by norm_num)) hlogNplusPos
            _ ≤ 2 * (434 * (n : ℝ) ^ β) * ((2 / δ) * (n : ℝ) ^ δ) :=
              mul_le_mul_of_nonneg_left hlogNplus (by positivity)
        _ = (1736 / δ) * (n : ℝ) ^ (1 - 6 * δ) := by
          calc
            2 * (434 * (n : ℝ) ^ β) * ((2 / δ) * (n : ℝ) ^ δ) =
                (1736 / δ) * ((n : ℝ) ^ β * (n : ℝ) ^ δ) := by ring
            _ = (1736 / δ) * (n : ℝ) ^ (β + δ) := by rw [← Real.rpow_add hnpos]
            _ = (1736 / δ) * (n : ℝ) ^ (1 - 6 * δ) := by congr 2 <;> dsimp [β] <;> ring
    have hcoeff : 1736 / δ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (4 * δ) := by
      dsimp [Cgap] at hgapN
      have hgapMul : 3472 ≤ (n : ℝ) ^ (4 * δ) * δ :=
        (div_le_iff₀ hδ).1 hgapN
      apply (div_le_iff₀ hδ).2
      nlinarith [hgapMul]
    calc
      2 * (nearRadius : ℝ) * Real.log ((n : ℝ) + 1) ≤
          (1736 / δ) * (n : ℝ) ^ (1 - 6 * δ) := hprod
      _ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (4 * δ) * (n : ℝ) ^ (1 - 6 * δ) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = (n : ℝ) ^ γ / 2 := by
        calc
          (1 / 2 : ℝ) * (n : ℝ) ^ (4 * δ) * (n : ℝ) ^ (1 - 6 * δ) =
          (1 / 2 : ℝ) * ((n : ℝ) ^ (4 * δ) * (n : ℝ) ^ (1 - 6 * δ)) := by ring
          _ = (1 / 2 : ℝ) * (n : ℝ) ^ (4 * δ + (1 - 6 * δ)) := by
            rw [← Real.rpow_add hnpos]
          _ = (n : ℝ) ^ γ / 2 := by
            have hexp : 4 * δ + (1 - 6 * δ) = γ := by dsimp [γ]; ring
            rw [hexp]
            ring
  have hroleCards (q : ℕ) (hq : 0 < q) :
      Fintype.card (OddRole q) = 2 ^ (q - 1) ∧
        Fintype.card (EvenRole q) = 2 ^ (q - 1) := by
    have hp := HypercubeRamsey.parity_class_card hq
    have heqEven : Fintype.card (EvenRole q) =
        (HypercubeRamsey.evenRoleSet q).card := by
      simpa [EvenRole, HypercubeRamsey.evenRoleSet] using
        (Fintype.card_coe (HypercubeRamsey.evenRoleSet q))
    have heqOdd : Fintype.card (OddRole q) =
        (Finset.univ \ HypercubeRamsey.evenRoleSet q).card := by
      simpa [OddRole, HypercubeRamsey.evenRoleSet] using
        (Fintype.card_coe (Finset.univ \ HypercubeRamsey.evenRoleSet q))
    exact ⟨heqOdd.trans hp.2, heqEven.trans hp.1⟩
  have hroles := hroleCards n (by omega)
  have hoddCard : (Fintype.card (OddRole n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast hroles.1
  have hevenCard : (Fintype.card (EvenRole n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast hroles.2
  have hpowN : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1 + 1) := by congr 1; omega
      _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (n - 1) := by ring
  have hballExp (v : CubeVertex n) :
      2 * ((Finset.univ.filter fun u : CubeVertex n =>
        _root_.hammingDist v u ≤ nearRadius).card : ℝ) ≤
          Real.exp ((n : ℝ) ^ γ) := by
    let B : Finset (CubeVertex n) := Finset.univ.filter fun u =>
      _root_.hammingDist v u ≤ nearRadius
    have hBcard := Lane_q_s10_d10.hammingBall_card_le_pow (R := nearRadius) v
    have hBreal : (B.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ nearRadius := by
      exact_mod_cast hBcard
    have hlogpow : Real.log (((n + 1 : ℕ) : ℝ) ^ nearRadius) =
        (nearRadius : ℝ) * Real.log ((n : ℝ) + 1) := by
      rw [Real.log_pow]
      norm_cast
    have hpowExp : ((n + 1 : ℕ) : ℝ) ^ nearRadius ≤
        Real.exp (((n : ℝ) ^ γ) / 4) := by
      apply (Real.log_le_iff_le_exp (by positivity)).mp
      rw [hlogpow]
      nlinarith [hdecay]
    have hquarter : 1 ≤ ((n : ℝ) ^ γ) / 4 := by linarith [hγN]
    have htwo : 2 ≤ Real.exp (((n : ℝ) ^ γ) / 4) := by
      have h := Real.add_one_le_exp (((n : ℝ) ^ γ) / 4)
      linarith
    have hmul : 2 * ((n + 1 : ℕ) : ℝ) ^ nearRadius ≤
        Real.exp (((n : ℝ) ^ γ) / 4) * Real.exp (((n : ℝ) ^ γ) / 4) :=
      mul_le_mul htwo hpowExp (by positivity) (by positivity)
    have hexpAdd : Real.exp (((n : ℝ) ^ γ) / 4) *
        Real.exp (((n : ℝ) ^ γ) / 4) = Real.exp (((n : ℝ) ^ γ) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hle : Real.exp (((n : ℝ) ^ γ) / 2) ≤ Real.exp ((n : ℝ) ^ γ) := by
      apply Real.exp_le_exp.mpr
      have hpowNonneg : 0 ≤ (n : ℝ) ^ γ := by positivity
      nlinarith [hpowNonneg]
    calc
      2 * (B.card : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) ^ nearRadius :=
        mul_le_mul_of_nonneg_left hBreal (by norm_num)
      _ ≤ Real.exp (((n : ℝ) ^ γ) / 4) * Real.exp (((n : ℝ) ^ γ) / 4) := hmul
      _ = Real.exp (((n : ℝ) ^ γ) / 2) := hexpAdd
      _ ≤ Real.exp ((n : ℝ) ^ γ) := hle
  have projectedNearBound (u v : CubeVertex n)
      (hspecial : _root_.hammingDist
        (p10_1kSpecialSlice (mS_le n δ) u) (p10_1kSpecialSlice (mS_le n δ) v) ≤ 8)
      (hprojected : _root_.hammingDist
        (p10_1k_projectedWord d (p10_1kResidualWord (mS_le n δ) u))
        (p10_1k_projectedWord d (p10_1kResidualWord (mS_le n δ) v)) ≤
          2 * Rloc n δ + 16) :
      _root_.hammingDist u v ≤ nearRadius := by
    have hchunks : Fintype.card (Fin d.bitIndices.length) ≤ Nat.log 2 n + 1 := by
      have hlen := Lane_q_s10_d10.bitIndices_length_le_log d
      have hmono : Nat.log 2 d ≤ Nat.log 2 n := Nat.log_mono_right (Nat.sub_le n (mS n δ))
      calc
        Fintype.card (Fin d.bitIndices.length) = d.bitIndices.length := by simp
        _ ≤ Nat.log 2 d + 1 := hlen
        _ ≤ Nat.log 2 n + 1 := Nat.add_le_add_right hmono 1
    have hcomm {e : ℕ} (x y : CubeVertex e) :
        _root_.hammingDist x y = _root_.hammingDist y x := by
      unfold _root_.hammingDist
      congr 1
      ext i
      simp [ne_comm]
    let ru := p10_1kResidualWord (mS_le n δ) u
    let rv := p10_1kResidualWord (mS_le n δ) v
    let pu := p10_1k_projectedWord d ru
    let pv := p10_1k_projectedWord d rv
    have hpu : _root_.hammingDist ru pu = Fintype.card (Fin d.bitIndices.length) := by
      exact p10_1k_projectedWord_hammingDist d ru
    have hpv : _root_.hammingDist rv pv = Fintype.card (Fin d.bitIndices.length) := by
      exact p10_1k_projectedWord_hammingDist d rv
    have hpv' : _root_.hammingDist pv rv = Fintype.card (Fin d.bitIndices.length) := by
      rw [hcomm, hpv]
    have hres : _root_.hammingDist ru rv ≤
        (2 * Rloc n δ + 16) + 2 * Fintype.card (Fin d.bitIndices.length) := by
      have htri₁ := _root_.hammingDist_triangle ru pu rv
      have htri₂ := _root_.hammingDist_triangle pu pv rv
      have hpr : _root_.hammingDist pu rv ≤
          (2 * Rloc n δ + 16) + Fintype.card (Fin d.bitIndices.length) := by
        calc
          _root_.hammingDist pu rv ≤
              _root_.hammingDist pu pv + _root_.hammingDist pv rv := htri₂
          _ ≤ (2 * Rloc n δ + 16) + Fintype.card (Fin d.bitIndices.length) := by
            rw [hpv'] at *
            exact Nat.add_le_add hprojected le_rfl
      calc
        _root_.hammingDist ru rv ≤
            _root_.hammingDist ru pu + _root_.hammingDist pu rv := htri₁
        _ ≤ Fintype.card (Fin d.bitIndices.length) +
              ((2 * Rloc n δ + 16) + Fintype.card (Fin d.bitIndices.length)) :=
          Nat.add_le_add hpu.le hpr
        _ = (2 * Rloc n δ + 16) + 2 * Fintype.card (Fin d.bitIndices.length) := by omega
    calc
      _root_.hammingDist u v =
          _root_.hammingDist (p10_1kSpecialSlice (mS_le n δ) u)
            (p10_1kSpecialSlice (mS_le n δ) v) +
          _root_.hammingDist ru rv :=
        p10_1kSliceHammingDist (mS_le n δ) u v
      _ ≤ 8 + ((2 * Rloc n δ + 16) +
            2 * Fintype.card (Fin d.bitIndices.length)) := Nat.add_le_add hspecial hres
      _ ≤ nearRadius := by dsimp [nearRadius]; omega
  have nearRoleCount {Role : Type} [Fintype Role] [DecidableEq Role]
      (near : Finset Role) (center : Slice n δ)
      (f : Role → Slice n δ × CubeVertex d)
      (hinj : Function.Injective f)
      (hnear : ∀ x ∈ near, _root_.hammingDist center (f x).1 ≤ 8) :
      near.card ≤ (Finset.univ.filter fun z : Slice n δ =>
        _root_.hammingDist center z ≤ 8).card * 2 ^ d := by
    let Z : Finset (Slice n δ) := Finset.univ.filter fun z =>
      _root_.hammingDist center z ≤ 8
    let Q : Finset (Slice n δ × CubeVertex d) := Z ×ˢ Finset.univ
    have himage : near.card = (near.image f).card :=
      (Finset.card_image_of_injective near hinj).symm
    have hsub : near.image f ⊆ Q := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear r hr⟩,
        Finset.mem_univ _⟩
    calc
      near.card = (near.image f).card := himage
      _ ≤ Q.card := Finset.card_le_card hsub
      _ = Z.card * 2 ^ d := by simp [Q, Z, CubeVertex]
  have nearSliceCard (center : Slice n δ) :
      (Finset.univ.filter fun z : Slice n δ =>
        _root_.hammingDist center z ≤ 8).card ≤ (mS n δ + 1) ^ 8 := by
    exact Lane_q_s10_d10.hammingBall_card_le_pow center
  have tagRoleFraction {Role : Type} [Fintype Role]
      (near : Finset Role) (count : near.card ≤ (mS n δ + 1) ^ 8 * 2 ^ d)
      (hrole : (Fintype.card Role : ℝ) = (2 : ℝ) ^ (n - 1)) :
      (near.card : ℝ) / Fintype.card Role ≤
        ((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ) := by
    have hcount : (near.card : ℝ) ≤ ((mS n δ : ℝ) + 1) ^ 8 * (2 : ℝ) ^ d := by
      exact_mod_cast count
    have hx : 2 ≤ (mS n δ : ℝ) + 1 := by exact_mod_cast (show 2 ≤ mS n δ + 1 by omega)
    have hpoly : 2 * ((mS n δ : ℝ) + 1) ^ 8 ≤ ((mS n δ : ℝ) + 1) ^ 9 := by
      rw [pow_succ]
      have hmul := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ ((mS n δ : ℝ) + 1) ^ 8)
      nlinarith
    have hpowDen : (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ d * (2 : ℝ) ^ (mS n δ - 1) := by
      have hnat : n - 1 = d + (mS n δ - 1) := by dsimp [d]; omega
      rw [hnat, pow_add]
    have hpowm : (2 : ℝ) ^ (mS n δ) = 2 * (2 : ℝ) ^ (mS n δ - 1) := by
      calc
        (2 : ℝ) ^ (mS n δ) = (2 : ℝ) ^ (mS n δ - 1 + 1) := by congr 1; omega
        _ = (2 : ℝ) ^ (mS n δ - 1) * 2 := by rw [pow_succ]
        _ = 2 * (2 : ℝ) ^ (mS n δ - 1) := by ring
    have hrolePos : 0 < (Fintype.card Role : ℝ) := by rw [hrole]; positivity
    have hpowMPos : 0 < (2 : ℝ) ^ (mS n δ) := by positivity
    calc
      (near.card : ℝ) / Fintype.card Role ≤
          (((mS n δ : ℝ) + 1) ^ 8 * (2 : ℝ) ^ d) / Fintype.card Role :=
        div_le_div_of_nonneg_right hcount hrolePos.le
      _ = (((mS n δ : ℝ) + 1) ^ 8 * (2 : ℝ) ^ d) / (2 : ℝ) ^ (n - 1) := by
        rw [hrole]
      _ = (2 * ((mS n δ : ℝ) + 1) ^ 8) / (2 : ℝ) ^ (mS n δ) := by
        rw [hpowDen, hpowm]
        field_simp
        <;> ring
      _ ≤ ((mS n δ : ℝ) + 1) ^ 9 / (2 : ℝ) ^ (mS n δ) :=
        div_le_div_of_nonneg_right hpoly hpowMPos.le
  have nbhdOverlapDist {s t : Slice n δ}
      (h : ¬ Disjoint (tagNbhd δ s) (tagNbhd δ t)) :
      _root_.hammingDist s t ≤ 8 := by
    have hmeet : ∃ z, z ∈ tagNbhd δ s ∧ z ∈ tagNbhd δ t := by
      by_contra hnone
      apply h
      rw [Finset.disjoint_left]
      intro z hz hzt
      exact hnone ⟨z, hz, hzt⟩
    rcases hmeet with ⟨z, hzs, hzt⟩
    have hs : _root_.hammingDist s z ≤ 4 :=
      (Finset.mem_filter.mp hzs).2
    have ht : _root_.hammingDist t z ≤ 4 :=
      (Finset.mem_filter.mp hzt).2
    have hcomm : _root_.hammingDist z t = _root_.hammingDist t z := by
      unfold _root_.hammingDist
      congr 1
      ext i
      simp [ne_comm]
    calc
      _root_.hammingDist s t ≤
          _root_.hammingDist s z + _root_.hammingDist z t :=
        _root_.hammingDist_triangle s z t
      _ ≤ 8 := by rw [hcomm]; omega
  let oddTagMap : OddRole n → Slice n δ × CubeVertex d := fun b =>
    ((groupOf δ b).1, p10_1kResidualWord (mS_le n δ) b.1)
  have hoddTagMapInj : Function.Injective oddTagMap := by
    intro x y hxy
    apply Subtype.ext
    apply (p10_1kSliceWordEquiv (mS_le n δ)).injective
    apply Prod.ext
    · simpa [oddTagMap, groupOf, p10_1kProjectedVertex, p10_1kSpecialSlice] using
        congrArg Prod.fst hxy
    · simpa [oddTagMap, p10_1kResidualWord] using congrArg Prod.snd hxy
  have hoddTagBound (b : OddRole n) :
      ((oddTagNear δ b).card : ℝ) / Fintype.card (OddRole n) ≤
        ((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ) := by
    have hcount := nearRoleCount (oddTagNear δ b) ((groupOf δ b).1) oddTagMap
      hoddTagMapInj (by
        intro b' hb'
        exact nbhdOverlapDist ((Finset.mem_filter.mp hb').2))
    have hcount' : (oddTagNear δ b).card ≤ (mS n δ + 1) ^ 8 * 2 ^ d :=
      hcount.trans (Nat.mul_le_mul_right (2 ^ d) (nearSliceCard ((groupOf δ b).1)))
    exact tagRoleFraction (oddTagNear δ b) hcount' hoddCard
  let evenTagMap : EvenRole n → Slice n δ × CubeVertex d := fun a =>
    ((evenSite δ a).1, p10_1kResidualWord (mS_le n δ) a.1)
  have hevenTagMapInj : Function.Injective evenTagMap := by
    intro x y hxy
    apply Subtype.ext
    apply (p10_1kSliceWordEquiv (mS_le n δ)).injective
    apply Prod.ext
    · simpa [evenTagMap, evenSite, p10_1kProjectedVertex, p10_1kSpecialSlice] using
        congrArg Prod.fst hxy
    · simpa [evenTagMap, p10_1kResidualWord] using congrArg Prod.snd hxy
  have hevenTagBound (a : EvenRole n) :
      ((evenTagNear δ a).card : ℝ) / Fintype.card (EvenRole n) ≤
        ((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ) := by
    have hcount := nearRoleCount (evenTagNear δ a) ((evenSite δ a).1) evenTagMap
      hevenTagMapInj (by
        intro a' ha'
        exact nbhdOverlapDist ((Finset.mem_filter.mp ha').2))
    have hcount' : (evenTagNear δ a).card ≤ (mS n δ + 1) ^ 8 * 2 ^ d :=
      hcount.trans (Nat.mul_le_mul_right (2 ^ d) (nearSliceCard ((evenSite δ a).1)))
    exact tagRoleFraction (evenTagNear δ a) hcount' hevenCard
  have hoddNearBound (b : OddRole n) :
      ((oddNear δ b).card : ℝ) / Fintype.card (OddRole n) ≤
        Real.exp ((n : ℝ) ^ γ) / 2 ^ n := by
    let B : Finset (CubeVertex n) := Finset.univ.filter fun u =>
      _root_.hammingDist b.1 u ≤ nearRadius
    let I := (oddNear δ b).image (fun b' => b'.1)
    have hinj : Function.Injective (fun b' : OddRole n => b'.1) := fun _ _ h => Subtype.ext h
    have himage : I.card = (oddNear δ b).card :=
      Finset.card_image_of_injective _ hinj
    have hsub : I ⊆ B := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨b', hb', rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hnear := (Finset.mem_filter.mp hb').2
      apply projectedNearBound b.1 b'.1
      · simpa [groupOf, p10_1kProjectedVertex] using hnear.1
      · simpa [groupOf, p10_1kProjectedVertex] using hnear.2
    have hcard : (oddNear δ b).card ≤ B.card := by
      rw [← himage]
      exact Finset.card_le_card hsub
    have hcardR : ((oddNear δ b).card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hcard
    have hden : 0 < (Fintype.card (OddRole n) : ℝ) := by rw [hoddCard]; positivity
    calc
      ((oddNear δ b).card : ℝ) / Fintype.card (OddRole n) ≤
          (B.card : ℝ) / Fintype.card (OddRole n) :=
        div_le_div_of_nonneg_right hcardR (by positivity)
      _ = (2 * (B.card : ℝ)) / 2 ^ n := by
        rw [hoddCard, hpowN]
        field_simp
        <;> ring
      _ ≤ Real.exp ((n : ℝ) ^ γ) / 2 ^ n :=
        div_le_div_of_nonneg_right (hballExp b.1) (by positivity)
  have hevenNearBound (a : EvenRole n) :
      ((evenNear δ a).card : ℝ) / Fintype.card (EvenRole n) ≤
        Real.exp ((n : ℝ) ^ γ) / 2 ^ n := by
    let B : Finset (CubeVertex n) := Finset.univ.filter fun u =>
      _root_.hammingDist a.1 u ≤ nearRadius
    let I := (evenNear δ a).image (fun a' => a'.1)
    have hinj : Function.Injective (fun a' : EvenRole n => a'.1) := fun _ _ h => Subtype.ext h
    have himage : I.card = (evenNear δ a).card :=
      Finset.card_image_of_injective _ hinj
    have hsub : I ⊆ B := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨a', ha', rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hnear := (Finset.mem_filter.mp ha').2
      apply projectedNearBound a.1 a'.1
      · simpa [evenSite, p10_1kProjectedVertex] using hnear.1
      · simpa [evenSite, p10_1kProjectedVertex] using hnear.2
    have hcard : (evenNear δ a).card ≤ B.card := by
      rw [← himage]
      exact Finset.card_le_card hsub
    have hcardR : ((evenNear δ a).card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hcard
    calc
      ((evenNear δ a).card : ℝ) / Fintype.card (EvenRole n) ≤
          (B.card : ℝ) / Fintype.card (EvenRole n) :=
        div_le_div_of_nonneg_right hcardR (by positivity)
      _ = (2 * (B.card : ℝ)) / 2 ^ n := by
        rw [hevenCard, hpowN]
        field_simp
        <;> ring
      _ ≤ Real.exp ((n : ℝ) ^ γ) / 2 ^ n :=
        div_le_div_of_nonneg_right (hballExp a.1) (by positivity)
  have hoddFrac : oddFracOf n δ ≤ Real.exp ((n : ℝ) ^ γ) / 2 ^ n := by
    unfold oddFracOf
    apply Real.iSup_le
    intro b
    exact hoddNearBound b
    positivity
  have hevenFrac : evenFracOf n δ ≤ Real.exp ((n : ℝ) ^ γ) / 2 ^ n := by
    unfold evenFracOf
    apply Real.iSup_le
    intro a
    exact hevenNearBound a
    positivity
  have htagFrac : tagFracOf n δ ≤ ((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ) := by
    unfold tagFracOf
    apply max_le
    · apply Real.iSup_le
      intro b
      exact hoddTagBound b
      positivity
    · apply Real.iSup_le
      intro a
      exact hevenTagBound a
      positivity
  refine ⟨?_, ?_, ?_⟩
  · simpa [γ] using hoddFrac
  · simpa [γ] using hevenFrac
  · exact htagFrac

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

set_option maxHeartbeats 1000000 in
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
  classical
  let typThr : ℝ := 8 * (4 / κ + 1)
  let oddThr : ℝ := 1 / (10 ^ 9 : ℝ)
  let Cconst : ℝ := max 1 (max (4 * (typThr + 1) / oddThr) (4 * (typThr + 1)))
  have htyp : 0 < typThr := by positivity
  have hoddThr : 0 < oddThr := by positivity
  have hCone : 1 ≤ Cconst := by
    change 1 ≤ max 1 (max (4 * (typThr + 1) / oddThr) (4 * (typThr + 1)))
    exact le_max_left _ _
  have hCodd : 4 * (typThr + 1) / oddThr ≤ Cconst := by
    change 4 * (typThr + 1) / oddThr ≤
      max 1 (max (4 * (typThr + 1) / oddThr) (4 * (typThr + 1)))
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hCeven : 4 * (typThr + 1) ≤ Cconst := by
    change 4 * (typThr + 1) ≤
      max 1 (max (4 * (typThr + 1) / oddThr) (4 * (typThr + 1)))
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hCpos : 0 < Cconst := lt_of_lt_of_le (by norm_num) hCone
  have hδsmall' : δ < 1 / 2000 := by
    have hmin : min (min η₀ ζ) 1 ≤ 1 := min_le_right _ _
    nlinarith [hδsmall]
  let s : ℝ := 200 * δ
  let α : ℝ := 500 * δ
  let γ : ℝ := 1 - 2 * δ
  let ρ : ℝ := 1 - δ
  let q : ℝ := 1 + 299 * δ
  have hs : 0 < s := by dsimp [s]; positivity
  have hsle : s ≤ 1 := by dsimp [s]; nlinarith [hδsmall']
  have hα : α < 1 / 4 := by dsimp [α]; nlinarith [hδsmall']
  have hγpos : 0 < γ := by dsimp [γ]; nlinarith [hδ]
  have hγlt : γ < 1 := by dsimp [γ]; nlinarith [hδ]
  have hρpos : 0 < ρ := by dsimp [ρ]; nlinarith [hδsmall']
  have hγρ : γ < ρ := by dsimp [γ, ρ]; nlinarith [hδ]
  have hq : 1 < q := by dsimp [q]; nlinarith [hδ]
  have hsc := p10_1b_scale_separation η₀ ζ δ hη₀ hζ hδ hδsmall
  have hscThird : ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ s < (n : ℝ) ^ (1 - δ) := by
    filter_upwards [hsc] with n h
    simpa [s] using h.2.2.1
  have hn8 : ∀ᶠ n : ℕ in atTop, 8 ≤ n :=
    Filter.eventually_atTop.mpr ⟨8, fun _ hn => hn⟩
  have hn512 : ∀ᶠ n : ℕ in atTop, 512 ≤ n :=
    Filter.eventually_atTop.mpr ⟨512, fun _ hn => hn⟩
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2gt : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have powTwoExp (j : ℕ) : (2 : ℝ) ^ j = Real.exp ((j : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ j = (Real.exp (Real.log 2)) ^ j := by rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((j : ℝ) * Real.log 2) := (Real.exp_nat_mul (Real.log 2) j).symm
  have hExpA : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) ^ ζ / 2) ≤ (n : ℝ) ^ (-A) := by
    have hdecay := Lane_q_s10_d10.power_exp_decay (a := ζ) (b := A) (c := 1 / 2)
      hζ (by norm_num)
    filter_upwards [hn8, hdecay.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn hsmall
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hsmall' : (n : ℝ) ^ A * Real.exp (-(n : ℝ) ^ ζ / 2) < 1 := by
      convert hsmall using 1 <;> congr 2 <;> ring
    have hmul : (n : ℝ) ^ A * Real.exp (-(n : ℝ) ^ ζ / 2) ≤ 1 := le_of_lt hsmall'
    have hmul' : Real.exp (-(n : ℝ) ^ ζ / 2) * (n : ℝ) ^ A ≤ 1 := by
      calc
        Real.exp (-(n : ℝ) ^ ζ / 2) * (n : ℝ) ^ A =
            (n : ℝ) ^ A * Real.exp (-(n : ℝ) ^ ζ / 2) := by ring
        _ ≤ 1 := hmul
    have hpowpos : 0 < (n : ℝ) ^ A := Real.rpow_pos_of_pos hnpos _
    have hdiv : Real.exp (-(n : ℝ) ^ ζ / 2) ≤ 1 / ((n : ℝ) ^ A) :=
      (le_div_iff₀ hpowpos).2 hmul'
    have hdiv' : Real.exp (-(n : ℝ) ^ ζ / 2) ≤ ((n : ℝ) ^ A)⁻¹ := by
      simpa [one_div] using hdiv
    rw [Real.rpow_neg hnpos.le]
    exact hdiv'
  have hTagSmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ)) *
        Real.exp ((mS n δ : ℝ) / 10) ≤ 1 := by
    have hxlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ s := by
      have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ s) atTop atTop :=
        (_root_.tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
      exact htend.eventually_ge_atTop 2
    have htail := Lane_q_s10_d10.power_exp_decay (a := s) (b := 11) (c := 1 / 5)
      hs (by norm_num)
    have htailEv : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ 11 * Real.exp (-(1 / 5 : ℝ) * (n : ℝ) ^ s) < 1 := by
      filter_upwards [htail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
      simpa [Real.rpow_natCast] using hn
    filter_upwards [hscThird, hxlarge, hn512, htailEv] with n hscN hxN hnN htailN
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hnpos : 0 < (n : ℝ) := by positivity
    let x : ℝ := (n : ℝ) ^ s
    have hx : 2 ≤ x := by simpa [x] using hxN
    have hpowρ : (n : ℝ) ^ (1 - δ) ≤ (n : ℝ) := by
      calc
        (n : ℝ) ^ (1 - δ) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnreal (by linarith [hδ])
        _ = (n : ℝ) := by rw [Real.rpow_one]
    have h4x : 4 * x < n := by
      dsimp [x]
      exact hscN.trans_le hpowρ
    have hspecialUpper : (p10_1kSpecialCount n δ : ℝ) ≤ x := by
      dsimp [p10_1kSpecialCount, x]
      exact Nat.floor_le (by positivity)
    have hspecialLt : p10_1kSpecialCount n δ < n := by
      have hreal : (p10_1kSpecialCount n δ : ℝ) < (n : ℝ) := by nlinarith
      exact_mod_cast hreal
    have hmEq : mS n δ = p10_1kSpecialCount n δ := by
      dsimp [mS]
      exact min_eq_left hspecialLt.le
    have hfloorHalf : x / 2 ≤ (p10_1kSpecialCount n δ : ℝ) := by
      have hf : x < (p10_1kSpecialCount n δ : ℝ) + 1 := by
        dsimp [p10_1kSpecialCount, x, s]
        exact Nat.lt_floor_add_one ((n : ℝ) ^ (200 * δ))
      have hfloor : x - 1 < (p10_1kSpecialCount n δ : ℝ) := by linarith
      nlinarith [hx, hfloor]
    have hmlo : x / 2 ≤ (mS n δ : ℝ) := by
      rw [hmEq]
      exact hfloorHalf
    have hmhi : (mS n δ : ℝ) ≤ x := by rw [hmEq]; exact hspecialUpper
    have hmplus : (mS n δ : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      have hnat : mS n δ + 1 ≤ 2 * n := by have := mS_le n δ; omega
      exact_mod_cast hnat
    have hlogGap : Real.log 2 - 1 / 10 ≥ 2 / 5 := by linarith [hlog2gt]
    have hnegative : (mS n δ : ℝ) / 10 - (mS n δ : ℝ) * Real.log 2 ≤
        -(1 / 5 : ℝ) * x := by
      have hmnonneg : 0 ≤ (mS n δ : ℝ) := by positivity
      have hmul : (2 / 5 : ℝ) * (mS n δ : ℝ) ≤
          (mS n δ : ℝ) * (Real.log 2 - 1 / 10) :=
        by nlinarith [mul_le_mul_of_nonneg_left hlogGap hmnonneg]
      nlinarith
    have hpow2m : (2 : ℝ) ^ (mS n δ) =
        Real.exp ((mS n δ : ℝ) * Real.log 2) := powTwoExp _
    have hratio : Real.exp ((mS n δ : ℝ) / 10) / (2 : ℝ) ^ (mS n δ) ≤
        Real.exp (-(1 / 5 : ℝ) * x) := by
      rw [hpow2m, ← Real.exp_sub]
      exact Real.exp_le_exp.mpr hnegative
    have hpoly : ((mS n δ : ℝ) + 1) ^ 9 ≤ 512 * (n : ℝ) ^ 9 := by
      calc
        ((mS n δ : ℝ) + 1) ^ 9 ≤ (2 * (n : ℝ)) ^ 9 := by gcongr
        _ = 512 * (n : ℝ) ^ 9 := by ring
    have htagpow : ((mS n δ : ℝ) + 1) ^ 9 *
        (Real.exp ((mS n δ : ℝ) / 10) / (2 : ℝ) ^ (mS n δ)) ≤
        512 * (n : ℝ) ^ 9 * Real.exp (-(1 / 5 : ℝ) * x) := by
      calc
        _ ≤ 512 * (n : ℝ) ^ 9 * Real.exp (-(1 / 5 : ℝ) * x) :=
          mul_le_mul hpoly hratio (by positivity) (by positivity)
        _ = _ := by rfl
    have hupper : (n : ℝ) * (((mS n δ : ℝ) + 1) ^ 9 /
          (2 : ℝ) ^ (mS n δ)) * Real.exp ((mS n δ : ℝ) / 10) ≤
        512 * (n : ℝ) ^ 10 * Real.exp (-(1 / 5 : ℝ) * x) := by
      calc
        _ = (n : ℝ) * (((mS n δ : ℝ) + 1) ^ 9 *
              (Real.exp ((mS n δ : ℝ) / 10) / (2 : ℝ) ^ (mS n δ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left htagpow (by positivity)
        _ = _ := by
          calc
            (n : ℝ) * (512 * (n : ℝ) ^ 9 * Real.exp (-(1 / 5 : ℝ) * x)) =
                512 * ((n : ℝ) ^ 9 * (n : ℝ)) * Real.exp (-(1 / 5 : ℝ) * x) := by ring
            _ = 512 * (n : ℝ) ^ 10 * Real.exp (-(1 / 5 : ℝ) * x) := by
              rw [show (n : ℝ) ^ 10 = (n : ℝ) ^ 9 * (n : ℝ) by rw [pow_succ]]
              <;> ring
    have htail' : (n : ℝ) ^ 11 * Real.exp (-(1 / 5 : ℝ) * (n : ℝ) ^ s) < 1 := by
      simpa [x] using htailN
    have hNpow : 512 * (n : ℝ) ^ 10 ≤ (n : ℝ) ^ 11 := by
      have h512 : (512 : ℝ) ≤ n := by exact_mod_cast hnN
      calc
        512 * (n : ℝ) ^ 10 ≤ (n : ℝ) * (n : ℝ) ^ 10 :=
          mul_le_mul_of_nonneg_right h512 (by positivity)
        _ = (n : ℝ) ^ 11 := by rw [show (n : ℝ) ^ 11 = (n : ℝ) ^ 10 * (n : ℝ) by rw [pow_succ]]; ring
    have hres : (n : ℝ) * (((mS n δ : ℝ) + 1) ^ 9 /
        (2 : ℝ) ^ (mS n δ)) * Real.exp ((mS n δ : ℝ) / 10) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right hNpow
        (by positivity : 0 ≤ Real.exp (-(1 / 5 : ℝ) * x))
      exact hupper.trans (hmul.trans (le_of_lt htail'))
    simpa [x] using hres
  have hOddSmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
        (8 * Real.exp (13 * (n : ℝ) ^ α)) ≤ 1 := by
    have hq : max γ α < 1 := max_lt hγlt (by linarith [hα])
    have hlinear := Lane_q_s10_d10.power_le_linear_eventually
      (a := max γ α) (c := 28 / Real.log 2) hq (by positivity)
    have htail := Lane_q_s10_d10.power_exp_decay (a := 1) (b := 1)
      (c := Real.log 2 / 2) (by norm_num) (by positivity)
    have htailEv : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) < 1 / 8 := by
      filter_upwards [htail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))]
        with n hn
      simpa [Real.rpow_one] using hn
    filter_upwards [hlinear, htailEv, hn8] with n hlin htailN hnN
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hpowγ : (n : ℝ) ^ γ ≤ (n : ℝ) ^ max γ α :=
      Real.rpow_le_rpow_of_exponent_le hnreal (le_max_left _ _)
    have hpowα : (n : ℝ) ^ α ≤ (n : ℝ) ^ max γ α :=
      Real.rpow_le_rpow_of_exponent_le hnreal (le_max_right _ _)
    have hlinear' : (28 / Real.log 2) * (n : ℝ) ^ max γ α ≤ (n : ℝ) := hlin
    have hlinear'' : 28 * (n : ℝ) ^ max γ α ≤ Real.log 2 * (n : ℝ) := by
      calc
        28 * (n : ℝ) ^ max γ α =
            ((28 / Real.log 2) * (n : ℝ) ^ max γ α) * Real.log 2 := by
              field_simp [ne_of_gt hlog2pos]
              <;> ring
        _ ≤ (n : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hlinear' hlog2pos.le
        _ = Real.log 2 * (n : ℝ) := by ring
    have hlinear''' : 14 * (n : ℝ) ^ max γ α ≤ (Real.log 2 / 2) * (n : ℝ) := by
      have hhalf := mul_le_mul_of_nonneg_right hlinear'' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      calc
        14 * (n : ℝ) ^ max γ α =
            (28 * (n : ℝ) ^ max γ α) * (1 / 2 : ℝ) := by ring
        _ ≤ (Real.log 2 * (n : ℝ)) * (1 / 2 : ℝ) := hhalf
        _ = (Real.log 2 / 2) * (n : ℝ) := by ring
    have hsumPow : (n : ℝ) ^ γ + 13 * (n : ℝ) ^ α ≤
        14 * (n : ℝ) ^ max γ α := by nlinarith [hpowγ, hpowα]
    have hexpBound : (n : ℝ) ^ γ + 13 * (n : ℝ) ^ α -
        (n : ℝ) * Real.log 2 ≤ -(Real.log 2 / 2) * n := by
      linarith [hsumPow, hlinear''']
    have hratio : Real.exp ((n : ℝ) ^ γ) / (2 : ℝ) ^ n *
        (8 * Real.exp (13 * (n : ℝ) ^ α)) =
        8 * Real.exp ((n : ℝ) ^ γ + 13 * (n : ℝ) ^ α -
          (n : ℝ) * Real.log 2) := by
      rw [powTwoExp]
      calc
        Real.exp ((n : ℝ) ^ γ) / Real.exp ((n : ℝ) * Real.log 2) *
            (8 * Real.exp (13 * (n : ℝ) ^ α)) =
            8 * (Real.exp ((n : ℝ) ^ γ) / Real.exp ((n : ℝ) * Real.log 2) *
              Real.exp (13 * (n : ℝ) ^ α)) := by ring
        _ = 8 * (Real.exp ((n : ℝ) ^ γ - (n : ℝ) * Real.log 2) *
              Real.exp (13 * (n : ℝ) ^ α)) := by rw [← Real.exp_sub]
        _ = 8 * Real.exp ((n : ℝ) ^ γ - (n : ℝ) * Real.log 2 +
              13 * (n : ℝ) ^ α) := by rw [← Real.exp_add]
        _ = _ := by congr 2 <;> ring
    calc
      (n : ℝ) * (Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
          (8 * Real.exp (13 * (n : ℝ) ^ α)) =
          8 * (n : ℝ) * Real.exp ((n : ℝ) ^ γ + 13 * (n : ℝ) ^ α -
            (n : ℝ) * Real.log 2) := by
        calc
          _ = (n : ℝ) * ((Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
              (8 * Real.exp (13 * (n : ℝ) ^ α))) := by ring
          _ = (n : ℝ) * (8 * Real.exp ((n : ℝ) ^ γ + 13 * (n : ℝ) ^ α -
              (n : ℝ) * Real.log 2)) := by rw [hratio]
          _ = _ := by ring
      _ ≤ 8 * (n : ℝ) * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := by
        gcongr
      _ ≤ 1 := by
        have hstrict : 8 * (n : ℝ) * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) < 1 := by
          calc
            8 * (n : ℝ) * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) =
                8 * ((n : ℝ) * Real.exp (-(Real.log 2 / 2) * (n : ℝ))) := by ring
            _ < 8 * (1 / 8 : ℝ) := mul_lt_mul_of_pos_left htailN (by norm_num)
            _ = 1 := by norm_num
        exact le_of_lt hstrict
  have hEvenSmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
        Real.exp ((Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ (-δ)) * n) ≤ 1 := by
    have hpower := Lane_q_s10_d10.power_le_power_eventually
      (a := γ) (b := ρ) (c := 1000) hγρ (by norm_num)
    have htail := Lane_q_s10_d10.power_exp_decay (a := ρ) (b := 1) (c := 9 / 1000)
      hρpos (by norm_num)
    have htailEv : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * Real.exp (-(9 / 1000 : ℝ) * (n : ℝ) ^ ρ) < 1 := by
      filter_upwards [htail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
        with n hn
      simpa [Real.rpow_one] using hn
    filter_upwards [hpower, htailEv, hn8] with n hpowerN htailN hnN
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hnpos : 0 < (n : ℝ) := by positivity
    have hpowγ : (n : ℝ) ^ γ ≤ (1 / 1000 : ℝ) * (n : ℝ) ^ ρ := by
      nlinarith [hpowerN]
    have hexp : (n : ℝ) ^ γ - (1 / 100 : ℝ) * (n : ℝ) ^ ρ ≤
        -(9 / 1000 : ℝ) * (n : ℝ) ^ ρ := by nlinarith [hpowγ]
    have hcancel : Real.exp ((n : ℝ) ^ γ) / (2 : ℝ) ^ n *
        Real.exp ((Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ (-δ)) * n) =
        Real.exp ((n : ℝ) ^ γ - (1 / 100 : ℝ) * (n : ℝ) ^ ρ) := by
      rw [powTwoExp, ← Real.exp_sub, ← Real.exp_add]
      congr 1
      have hρeq : (n : ℝ) ^ (-δ) * n = (n : ℝ) ^ ρ := by
        calc
          (n : ℝ) ^ (-δ) * n = (n : ℝ) ^ (-δ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (n : ℝ) ^ (-δ + 1) := by rw [← Real.rpow_add hnpos]
          _ = (n : ℝ) ^ ρ := by
            exact congrArg (fun e : ℝ => (n : ℝ) ^ e) (by dsimp [ρ]; ring)
      have hrow : (Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ (-δ)) * n =
          (n : ℝ) * Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ ρ := by
        calc
          (Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ (-δ)) * n =
              Real.log 2 * n - (1 / 100 : ℝ) * ((n : ℝ) ^ (-δ) * n) := by ring
          _ = (n : ℝ) * Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ ρ := by rw [hρeq]; ring
      calc
        (n : ℝ) ^ γ - (n : ℝ) * Real.log 2 +
            (Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ (-δ)) * n =
            (n : ℝ) ^ γ - (n : ℝ) * Real.log 2 +
              ((n : ℝ) * Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ ρ) := by rw [hrow]
        _ = (n : ℝ) ^ γ - (1 / 100 : ℝ) * (n : ℝ) ^ ρ := by ring
    calc
      (n : ℝ) * (Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
          Real.exp ((Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ (-δ)) * n) =
          (n : ℝ) * Real.exp ((n : ℝ) ^ γ - (1 / 100 : ℝ) * (n : ℝ) ^ ρ) := by
        calc
          _ = (n : ℝ) * ((Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
              Real.exp ((Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ (-δ)) * n)) := by ring
          _ = _ := by rw [hcancel]
      _ ≤ (n : ℝ) * Real.exp (-(9 / 1000 : ℝ) * (n : ℝ) ^ ρ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
      _ ≤ 1 := le_of_lt htailN
  have hRefSmall : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ n * Real.exp (-(1 / 200 : ℝ) * (n : ℝ) ^ q) ≤ 1 / 8 := by
    have hlinear := Lane_q_s10_d10.linear_le_power_eventually (a := q) (c := 400 * Real.log 2)
      (by change 1 < 1 + 299 * δ; linarith [hδ])
      (by positivity)
    filter_upwards [hlinear, hn8] with n hlinearN hnN
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlinearExp : 2 * Real.log 2 * (n : ℝ) ≤
        (1 / 200 : ℝ) * (n : ℝ) ^ q := by nlinarith [hlinearN]
    have hexp : (n : ℝ) * Real.log 2 + -(1 / 200 : ℝ) * (n : ℝ) ^ q ≤
        -(n : ℝ) * Real.log 2 := by nlinarith [hlinearExp]
    have hpow : (2 : ℝ) ^ n * Real.exp (-(1 / 200 : ℝ) * (n : ℝ) ^ q) ≤
        Real.exp (-(n : ℝ) * Real.log 2) := by
      rw [powTwoExp, ← Real.exp_add]
      exact Real.exp_le_exp.mpr hexp
    have hpow8 : (8 : ℝ) ≤ (2 : ℝ) ^ n := by
      have hnat : 3 ≤ n := by omega
      have hpowNat : (2 : ℕ) ^ 3 ≤ (2 : ℕ) ^ n := by gcongr
      exact_mod_cast (by simpa using hpowNat)
    calc
      (2 : ℝ) ^ n * Real.exp (-(1 / 200 : ℝ) * (n : ℝ) ^ q) ≤
          Real.exp (-(n : ℝ) * Real.log 2) := hpow
      _ = 1 / (2 : ℝ) ^ n := by
        calc
          Real.exp (-(n : ℝ) * Real.log 2) =
              (Real.exp ((n : ℝ) * Real.log 2))⁻¹ := by
                rw [show -(n : ℝ) * Real.log 2 = -((n : ℝ) * Real.log 2) by ring,
                  Real.exp_neg]
          _ = ((2 : ℝ) ^ n)⁻¹ := by rw [← powTwoExp]
          _ = 1 / (2 : ℝ) ^ n := by rw [one_div]
      _ ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hpow8
  have hClockSmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (2 : ℝ) ^ n *
        Real.exp (-(1 / 10 ^ 9 : ℝ) * Real.exp ((n : ℝ) ^ ζ / 2)) ≤ 1 / 8 := by
    have hlog := Lane_q_s10_d10.log_nat_le_rpow_eventually (a := ζ / 2)
      (by positivity)
    have hpowGap := Lane_q_s10_d10.power_le_power_eventually
      (a := ζ / 2) (b := ζ) (c := 4) (by linarith [hζ]) (by norm_num)
    let cClock : ℝ := 1 / 10 ^ 9
    have hcClockPos : 0 < cClock := by positivity
    have hquadLinear := Lane_q_s10_d10.linear_le_power_eventually
      (a := 2) (c := 2 / cClock) (by norm_num : (1 : ℝ) < 2) (by positivity)
    have htail := Lane_q_s10_d10.power_exp_decay (a := 2) (b := 1) (c := cClock / 2)
      (by norm_num) (by positivity)
    have htailEv : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * Real.exp (-(cClock / 2) * (n : ℝ) ^ 2) < 1 / 8 := by
      filter_upwards [htail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))]
        with n hn
      simpa [Real.rpow_one] using hn
    filter_upwards [hlog, hpowGap, hquadLinear, htailEv, hn8] with
      n hlogN hpowN hquadN htailN hnN
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hnpos : 0 < (n : ℝ) := by positivity
    have hlogsq : Real.log ((n : ℝ) ^ 2) ≤ (n : ℝ) ^ ζ / 2 := by
      rw [Real.log_pow]
      have hsmall : (n : ℝ) ^ (ζ / 2) ≤ (n : ℝ) ^ ζ / 4 := by nlinarith [hpowN]
      nlinarith [hlogN, hsmall]
    have hquad : (n : ℝ) ^ 2 ≤ Real.exp ((n : ℝ) ^ ζ / 2) :=
      (Real.log_le_iff_le_exp (by positivity)).mp hlogsq
    have hlinExp : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
      rw [powTwoExp]
      have hlogN : (n : ℝ) * Real.log 2 ≤ n := by
        calc
          (n : ℝ) * Real.log 2 ≤ (n : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hlog2le (by positivity)
          _ = n := by ring
      exact Real.exp_le_exp.mpr hlogN
    have hcomp : (n : ℝ) * (2 : ℝ) ^ n *
        Real.exp (-cClock * Real.exp ((n : ℝ) ^ ζ / 2)) ≤
        (n : ℝ) * Real.exp (n - cClock * (n : ℝ) ^ 2) := by
      have hexpLow : Real.exp (-cClock * Real.exp ((n : ℝ) ^ ζ / 2)) ≤
          Real.exp (-cClock * (n : ℝ) ^ 2) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hquad (neg_nonpos.mpr hcClockPos.le))
      have hprod := mul_le_mul hlinExp hexpLow (by positivity) (by positivity)
      calc
        (n : ℝ) * (2 : ℝ) ^ n *
            Real.exp (-cClock * Real.exp ((n : ℝ) ^ ζ / 2)) ≤
            (n : ℝ) * (Real.exp (n : ℝ) * Real.exp (-cClock * (n : ℝ) ^ 2)) :=
          by simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (n : ℝ))
        _ = (n : ℝ) * Real.exp (n - cClock * (n : ℝ) ^ 2) := by
          rw [← Real.exp_add]
          congr 2
          ring
    have hlinearQuad : (n : ℝ) ≤ (cClock / 2) * (n : ℝ) ^ 2 := by
      have hmulRaw := mul_le_mul_of_nonneg_left hquadN
        (by positivity : 0 ≤ cClock / 2)
      have hmul : (cClock / 2) * (2 / cClock * (n : ℝ)) ≤
          (cClock / 2) * (n : ℝ) ^ 2 := by
        rw [← Real.rpow_natCast (n : ℝ) 2]
        exact hmulRaw
      have hfactor : (cClock / 2) * (2 / cClock) = 1 := by
        field_simp [ne_of_gt hcClockPos] <;> ring
      have heq : (cClock / 2) * (2 / cClock * (n : ℝ)) = (n : ℝ) := by
        calc
          (cClock / 2) * (2 / cClock * (n : ℝ)) =
              ((cClock / 2) * (2 / cClock)) * (n : ℝ) := by ring
          _ = 1 * (n : ℝ) := by rw [hfactor]
          _ = (n : ℝ) := by ring
      simpa only [heq] using hmul
    have hneg : (n : ℝ) - cClock * (n : ℝ) ^ 2 ≤
        -(cClock / 2) * (n : ℝ) ^ 2 := by
      calc
        (n : ℝ) - cClock * (n : ℝ) ^ 2 ≤
            (cClock / 2) * (n : ℝ) ^ 2 - cClock * (n : ℝ) ^ 2 :=
          sub_le_sub_right hlinearQuad _
        _ = -(cClock / 2) * (n : ℝ) ^ 2 := by ring
    calc
      (n : ℝ) * (2 : ℝ) ^ n *
          Real.exp (-(1 / 10 ^ 9 : ℝ) * Real.exp ((n : ℝ) ^ ζ / 2)) ≤
          (n : ℝ) * Real.exp (n - cClock * (n : ℝ) ^ 2) := by
        simpa [cClock] using hcomp
      _ ≤ (n : ℝ) * Real.exp (-(cClock / 2) * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) (by positivity)
      _ ≤ 1 / 8 := le_of_lt htailN
  have hpowAux : ∀ j : ℕ, j + 8 ≤ 2 ^ (j + 4) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      calc
        j + 1 + 8 ≤ 2 * (j + 8) := by omega
        _ ≤ 2 * 2 ^ (j + 4) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (j + 5) := by rw [pow_succ]; ring
  have hEvents : ∀ᶠ n : ℕ in atTop,
      (8 ≤ n) ∧
      (Real.exp (-(n : ℝ) ^ ζ / 2) ≤ (n : ℝ) ^ (-A)) ∧
      ((n : ℝ) * (((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ)) *
        Real.exp ((mS n δ : ℝ) / 10) ≤ 1) ∧
      ((n : ℝ) * (Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
        (8 * Real.exp (13 * (n : ℝ) ^ α)) ≤ 1) ∧
      ((n : ℝ) * (Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
        Real.exp ((Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ (-δ)) * n) ≤ 1) ∧
      ((2 : ℝ) ^ n * Real.exp (-(1 / 200 : ℝ) * (n : ℝ) ^ q) ≤ 1 / 8) ∧
      ((n : ℝ) * (2 : ℝ) ^ n *
        Real.exp (-(1 / 10 ^ 9 : ℝ) * Real.exp ((n : ℝ) ^ ζ / 2)) ≤ 1 / 8) := by
    exact Filter.Eventually.and hn8 <| Filter.Eventually.and hExpA <|
      Filter.Eventually.and hTagSmall <| Filter.Eventually.and hOddSmall <|
      Filter.Eventually.and hEvenSmall <| Filter.Eventually.and hRefSmall hClockSmall
  obtain ⟨n₀, hEventsN⟩ := Filter.eventually_atTop.1 hEvents
  refine ⟨n₀, Cconst, ?_⟩
  intro n N hLarge
  rcases hEventsN n hLarge.1 with
    ⟨hn8N, hExpAN, hTagN, hOddN, hEvenN, hRefN, hClockN⟩
  rcases hLarge with ⟨hn0, hNlower, hNupper⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hNpositive : 0 < (N : ℝ) := lt_of_lt_of_le
    (mul_pos hCpos (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)) hNlower
  have hNupperR : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hNupper
  have hNlower2 : (2 : ℝ) ^ n ≤ (N : ℝ) := by
    calc
      (2 : ℝ) ^ n ≤ Cconst * (2 : ℝ) ^ n :=
        calc
          (2 : ℝ) ^ n = 1 * (2 : ℝ) ^ n := by ring
          _ ≤ Cconst * (2 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right hCone (by positivity : 0 ≤ (2 : ℝ) ^ n)
      _ ≤ (N : ℝ) := hNlower
  have hpowN : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1 + 1) := by congr 1; omega
      _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (n - 1) := by ring
  have hroleCards (q₀ : ℕ) (hq₀ : 0 < q₀) :
      Fintype.card (OddRole q₀) = 2 ^ (q₀ - 1) ∧
        Fintype.card (EvenRole q₀) = 2 ^ (q₀ - 1) := by
    have hp := HypercubeRamsey.parity_class_card hq₀
    have heqEven : Fintype.card (EvenRole q₀) =
        (HypercubeRamsey.evenRoleSet q₀).card := by
      simpa [EvenRole, HypercubeRamsey.evenRoleSet] using
        (Fintype.card_coe (HypercubeRamsey.evenRoleSet q₀))
    have heqOdd : Fintype.card (OddRole q₀) =
        (Finset.univ \ HypercubeRamsey.evenRoleSet q₀).card := by
      simpa [OddRole, HypercubeRamsey.evenRoleSet] using
        (Fintype.card_coe (Finset.univ \ HypercubeRamsey.evenRoleSet q₀))
    exact ⟨heqOdd.trans hp.2, heqEven.trans hp.1⟩
  have hroles := hroleCards n (by omega)
  have hoddCard : (Fintype.card (OddRole n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast hroles.1
  have hevenCard : (Fintype.card (EvenRole n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast hroles.2
  have hNatPow : n ≤ 2 ^ (n - 4) := by
    have h := hpowAux (n - 8)
    have hdecomp : n - 8 + 8 = n := by omega
    have hexp : n - 8 + 4 = n - 4 := by omega
    simpa [hdecomp, hexp] using h
  have hpowFactor : (2 : ℝ) ^ n = 16 * (2 : ℝ) ^ (n - 4) := by
    rw [show n = n - 4 + 4 by omega, pow_add]
    norm_num
    <;> ring
  have hnPowR : (n : ℝ) ≤ (2 : ℝ) ^ (n - 4) := by exact_mod_cast hNatPow
  have hquarterN : (n : ℝ) / (2 : ℝ) ^ n ≤ 1 / 16 := by
    calc
      (n : ℝ) / (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n - 4) / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_right hnPowR (by positivity)
      _ = 1 / 16 := by rw [hpowFactor]; field_simp
  have htagNratio : (2 * (n : ℝ)) / (2 : ℝ) ^ n ≤ 1 / 8 := by
    calc
      (2 * (n : ℝ)) / (2 : ℝ) ^ n = 2 * ((n : ℝ) / (2 : ℝ) ^ n) := by ring
      _ ≤ 2 * (1 / 16 : ℝ) := mul_le_mul_of_nonneg_left hquarterN (by norm_num)
      _ = 1 / 8 := by norm_num
  have hpowQuarter : (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have hpowEighth : (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n = (1 / 4 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have hhalfInv : (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := one_div_pow 2 n
  have hQuarterOuter : (N : ℝ) * (1 / 4 : ℝ) ^ n ≤ 1 / 16 := by
    calc
      (N : ℝ) * (1 / 4 : ℝ) ^ n ≤
          (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hNupperR (by positivity)
      _ = (n : ℝ) * ((2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := by ring
      _ = (n : ℝ) * (1 / 2 : ℝ) ^ n := by rw [hpowQuarter]
      _ = (n : ℝ) / (2 : ℝ) ^ n := by rw [hhalfInv]; ring
      _ ≤ 1 / 16 := hquarterN
  have hTagOuter : 2 * (N : ℝ) * (1 / 8 : ℝ) ^ n ≤ 1 / 8 := by
    have hNscaled : (N : ℝ) * (1 / 8 : ℝ) ^ n ≤
        (n : ℝ) * (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hNupperR (by positivity)
    calc
      2 * (N : ℝ) * (1 / 8 : ℝ) ^ n =
          2 * ((N : ℝ) * (1 / 8 : ℝ) ^ n) := by ring
      _ ≤ 2 * ((n : ℝ) * (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hNscaled (by norm_num)
      _ = 2 * (n : ℝ) * (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n := by ring
      _ = 2 * (n : ℝ) * ((2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n) := by ring
      _ = 2 * (n : ℝ) * (1 / 4 : ℝ) ^ n := by rw [hpowEighth]
      _ ≤ 2 * (n : ℝ) * (1 / 2 : ℝ) ^ n := by gcongr <;> norm_num
      _ = (2 * (n : ℝ)) / (2 : ℝ) ^ n := by rw [hhalfInv]; ring
      _ ≤ 1 / 8 := htagNratio
  have hcardOverN : (2 : ℝ) ^ (n - 1) / (N : ℝ) ≤ 1 / (2 * Cconst) := by
    have hprod : 2 * Cconst * (2 : ℝ) ^ (n - 1) ≤ (N : ℝ) := by
      calc
        2 * Cconst * (2 : ℝ) ^ (n - 1) = Cconst * (2 : ℝ) ^ n := by rw [hpowN]; ring
        _ ≤ (N : ℝ) := hNlower
    apply (div_le_iff₀ hNpositive).2
    field_simp [ne_of_gt hCpos]
    nlinarith [hprod]
  have hoddCardN : (Fintype.card (OddRole n) : ℝ) / N ≤ 1 / (2 * Cconst) := by
    rw [hoddCard]
    exact hcardOverN
  have hevenCardN : (Fintype.card (EvenRole n) : ℝ) / N ≤ 1 / (2 * Cconst) := by
    rw [hevenCard]
    exact hcardOverN
  refine ⟨?_, ?_⟩
  · refine ⟨by omega, ?_, hExpAN⟩
    exact_mod_cast hNlower2
  · intro εv oddCap groupCap εref rowCap oddFrac evenFrac meanCap tagFrac
      hεv0 hεv1 hoddCap0 hoddCap1 hgroupPos hgroupCap1 hεref0 hεref1
      hrowCap0 hrowCap1 hoddFrac0 hoddFrac1 hevenFrac0 hevenFrac1
      hmean0 hmean1 htag0 htag1
    have htagprod : (n : ℝ) * tagFrac * meanCap ≤ 1 := by
      have hmul : tagFrac * meanCap ≤
          (((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ)) *
            Real.exp ((mS n δ : ℝ) / 10) := by
        exact mul_le_mul htag1 hmean1 hmean0 (by positivity)
      calc
        (n : ℝ) * tagFrac * meanCap ≤
            (n : ℝ) * ((((mS n δ : ℝ) + 1) ^ 9 / 2 ^ (mS n δ)) *
              Real.exp ((mS n δ : ℝ) / 10)) :=
          by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmul (by positivity)
        _ ≤ 1 := by simpa [mul_assoc] using hTagN
    have hOddCapBound :
        8 * Real.exp (2 * kT n δ * (TT n δ + mS n δ) + (n : ℝ) ^ δ) ≤
          8 * Real.exp (13 * (n : ℝ) ^ α) := by
      have hkUpper : (kT n δ : ℝ) ≤ 2 * (n : ℝ) ^ (300 * δ) := by
        dsimp [kT, p10_1kTupleListLength]
        exact (Lane_q_s10_d10.ceil_power_bounds hnreal (by positivity)).2
      have hTUpper : (TT n δ : ℝ) ≤ 2 * (n : ℝ) ^ (141 * δ) := by
        dsimp [TT, p10_1kHeightCount]
        exact (Lane_q_s10_d10.ceil_power_bounds hnreal (by positivity)).2
      have hmNat : mS n δ ≤ p10_1kSpecialCount n δ := by
        dsimp [mS]
        exact min_le_left _ _
      have hmUpper : (mS n δ : ℝ) ≤ (n : ℝ) ^ s := by
        calc
          (mS n δ : ℝ) ≤ (p10_1kSpecialCount n δ : ℝ) := by exact_mod_cast hmNat
          _ ≤ (n : ℝ) ^ s := by
            dsimp [p10_1kSpecialCount, s]
            exact Nat.floor_le (by positivity)
      have hTexponent : 141 * δ ≤ s := by dsimp [s]; linarith [hδ]
      have hTpow : (n : ℝ) ^ (141 * δ) ≤ (n : ℝ) ^ s :=
        Real.rpow_le_rpow_of_exponent_le hnreal hTexponent
      have hTM : (TT n δ + mS n δ : ℝ) ≤ 3 * (n : ℝ) ^ s := by
        calc
          (TT n δ : ℝ) + (mS n δ : ℝ) ≤
              2 * (n : ℝ) ^ (141 * δ) + (n : ℝ) ^ s := add_le_add hTUpper hmUpper
          _ ≤ 2 * (n : ℝ) ^ s + (n : ℝ) ^ s := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hTpow (by norm_num)) (le_refl _)
          _ = 3 * (n : ℝ) ^ s := by ring
      have hpowerMul : (n : ℝ) ^ (300 * δ) * (n : ℝ) ^ s = (n : ℝ) ^ α := by
        rw [← Real.rpow_add hnpos]
        congr 1
        dsimp [s, α]
        ring
      have hexpBound : 2 * (kT n δ : ℝ) * (TT n δ + mS n δ) + (n : ℝ) ^ δ ≤
          13 * (n : ℝ) ^ α := by
        have hδexp : δ ≤ α := by dsimp [α]; linarith [hδ]
        have hpowδ : (n : ℝ) ^ δ ≤ (n : ℝ) ^ α :=
          Real.rpow_le_rpow_of_exponent_le hnreal hδexp
        have h2k : 2 * (kT n δ : ℝ) ≤ 4 * (n : ℝ) ^ (300 * δ) := by
          calc
            2 * (kT n δ : ℝ) ≤ 2 * (2 * (n : ℝ) ^ (300 * δ)) :=
              mul_le_mul_of_nonneg_left hkUpper (by norm_num)
            _ = 4 * (n : ℝ) ^ (300 * δ) := by ring
        have hsumNonneg : 0 ≤ (TT n δ + mS n δ : ℝ) := by positivity
        calc
          2 * (kT n δ : ℝ) * (TT n δ + mS n δ) + (n : ℝ) ^ δ ≤
              4 * (n : ℝ) ^ (300 * δ) * (TT n δ + mS n δ) + (n : ℝ) ^ δ := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right h2k hsumNonneg) (le_refl _)
          _ ≤ 4 * (n : ℝ) ^ (300 * δ) * (3 * (n : ℝ) ^ s) + (n : ℝ) ^ δ := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hTM (by positivity)) (le_refl _)
          _ = 12 * (n : ℝ) ^ α + (n : ℝ) ^ δ := by
            calc
              4 * (n : ℝ) ^ (300 * δ) * (3 * (n : ℝ) ^ s) + (n : ℝ) ^ δ =
                  12 * ((n : ℝ) ^ (300 * δ) * (n : ℝ) ^ s) + (n : ℝ) ^ δ := by ring
              _ = 12 * (n : ℝ) ^ α + (n : ℝ) ^ δ := by rw [hpowerMul]
          _ ≤ 13 * (n : ℝ) ^ α := by
            calc
              12 * (n : ℝ) ^ α + (n : ℝ) ^ δ ≤
                  12 * (n : ℝ) ^ α + (n : ℝ) ^ α :=
                add_le_add_right hpowδ (12 * (n : ℝ) ^ α)
              _ = 13 * (n : ℝ) ^ α := by ring
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpBound) (by norm_num)
    have hoddprod : (n : ℝ) * oddFrac * oddCap ≤ 1 := by
      have hmul : oddFrac * oddCap ≤
          (Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
            (8 * Real.exp (13 * (n : ℝ) ^ α)) :=
        mul_le_mul hoddFrac1 (hoddCap1.trans hOddCapBound) hoddCap0 (by positivity)
      calc
        (n : ℝ) * oddFrac * oddCap ≤
            (n : ℝ) * ((Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
              (8 * Real.exp (13 * (n : ℝ) ^ α))) :=
          by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmul (by positivity)
        _ ≤ 1 := by simpa [mul_assoc] using hOddN
    have hevenprod : (n : ℝ) * evenFrac * rowCap ≤ 1 := by
      have hmul : evenFrac * rowCap ≤
          (Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
            Real.exp ((Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ (-δ)) * n) :=
        mul_le_mul hevenFrac1 hrowCap1 hrowCap0 (by positivity)
      calc
        (n : ℝ) * evenFrac * rowCap ≤
            (n : ℝ) * ((Real.exp ((n : ℝ) ^ γ) / 2 ^ n) *
              Real.exp ((Real.log 2 - (1 / 100 : ℝ) * (n : ℝ) ^ (-δ)) * n)) :=
          by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmul (by positivity)
        _ ≤ 1 := by simpa [mul_assoc] using hEvenN
    have htagBase :
        (4 / κ + (n : ℝ) * tagFrac * meanCap) / typThr ≤ 1 / 8 := by
      calc
        (4 / κ + (n : ℝ) * tagFrac * meanCap) / typThr ≤
            (4 / κ + 1) / typThr :=
          div_le_div_of_nonneg_right (add_le_add_right htagprod (4 / κ)) (by positivity)
        _ = 1 / 8 := by dsimp [typThr]; field_simp
    have htagBase0 : 0 ≤ (4 / κ + (n : ℝ) * tagFrac * meanCap) / typThr := by positivity
    have htagPow := pow_le_pow_left₀ htagBase0 htagBase n
    have htagBudget :
        2 * (N : ℝ) * ((4 / κ + (n : ℝ) * tagFrac * meanCap) / typThr) ^ n ≤ 1 / 8 := by
      calc
        _ ≤ 2 * (N : ℝ) * (1 / 8 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left htagPow (by positivity)
        _ ≤ 1 / 8 := hTagOuter
    have hoddBase :
        ((Fintype.card (OddRole n) : ℝ) *
          (typThr + (n : ℝ) * oddFrac * oddCap) / ((N : ℝ) * oddThr)) ≤ 1 / 8 := by
      have hterm : typThr + (n : ℝ) * oddFrac * oddCap ≤ typThr + 1 :=
        add_le_add_right hoddprod typThr
      have hfactor :
          (Fintype.card (OddRole n) : ℝ) *
            (typThr + (n : ℝ) * oddFrac * oddCap) / ((N : ℝ) * oddThr) =
          ((Fintype.card (OddRole n) : ℝ) / (N : ℝ)) *
            ((typThr + (n : ℝ) * oddFrac * oddCap) / oddThr) := by
        field_simp [ne_of_gt hNpositive, ne_of_gt hoddThr]
        <;> ring
      rw [hfactor]
      have hcoef : 4 * (typThr + 1) ≤ Cconst * oddThr := by
        exact (div_le_iff₀ hoddThr).1 hCodd
      have hratio : (typThr + 1) / (2 * Cconst * oddThr) ≤ 1 / 8 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Cconst * oddThr)).2
        calc
          typThr + 1 = (4 * (typThr + 1)) / 4 := by ring
          _ ≤ (Cconst * oddThr) / 4 :=
            div_le_div_of_nonneg_right hcoef (by norm_num)
          _ = (1 / 8 : ℝ) * (2 * Cconst * oddThr) := by ring
      calc
        ((Fintype.card (OddRole n) : ℝ) / (N : ℝ)) *
            ((typThr + (n : ℝ) * oddFrac * oddCap) / oddThr) ≤
          (1 / (2 * Cconst)) * ((typThr + 1) / oddThr) :=
            mul_le_mul hoddCardN (div_le_div_of_nonneg_right hterm (by positivity))
              (by positivity) (by positivity)
        _ = (typThr + 1) / (2 * Cconst * oddThr) := by field_simp <;> ring
        _ ≤ 1 / 8 := hratio
    have hoddBase0 : 0 ≤
        ((Fintype.card (OddRole n) : ℝ) *
          (typThr + (n : ℝ) * oddFrac * oddCap) / ((N : ℝ) * oddThr)) := by positivity
    have hoddPowQuarter :
        ((Fintype.card (OddRole n) : ℝ) *
          (typThr + (n : ℝ) * oddFrac * oddCap) / ((N : ℝ) * oddThr)) ^ n ≤
          (1 / 4 : ℝ) ^ n := by
      exact pow_le_pow_left₀ hoddBase0 (hoddBase.trans (by norm_num)) n
    have hoddBudget :
        (N : ℝ) *
          ((Fintype.card (OddRole n) : ℝ) * (typThr + (n : ℝ) * oddFrac * oddCap) /
            ((N : ℝ) * oddThr)) ^ n ≤ 1 / 16 := by
      calc
        _ ≤ (N : ℝ) * (1 / 4 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left hoddPowQuarter (by positivity)
        _ ≤ 1 / 16 := hQuarterOuter
    have hevenBase :
        ((Fintype.card (EvenRole n) : ℝ) / (N : ℝ)) * 2 *
          (typThr + (n : ℝ) * evenFrac * rowCap) ≤ 1 / 4 := by
      have hterm : typThr + (n : ℝ) * evenFrac * rowCap ≤ typThr + 1 :=
        add_le_add_right hevenprod typThr
      calc
        ((Fintype.card (EvenRole n) : ℝ) / (N : ℝ)) * 2 *
            (typThr + (n : ℝ) * evenFrac * rowCap) ≤
          (1 / (2 * Cconst)) * 2 * (typThr + 1) := by
            have hfirst :
                ((Fintype.card (EvenRole n) : ℝ) / (N : ℝ)) * 2 ≤
                  (1 / (2 * Cconst)) * 2 :=
              mul_le_mul_of_nonneg_right hevenCardN (by norm_num)
            calc
              _ ≤ (1 / (2 * Cconst)) * 2 *
                  (typThr + (n : ℝ) * evenFrac * rowCap) :=
                mul_le_mul_of_nonneg_right hfirst (by positivity)
              _ ≤ (1 / (2 * Cconst)) * 2 * (typThr + 1) :=
                mul_le_mul_of_nonneg_left hterm (by positivity)
        _ = (typThr + 1) / Cconst := by field_simp
        _ ≤ 1 / 4 := by
          apply (div_le_iff₀ hCpos).2
          calc
            typThr + 1 = (4 * (typThr + 1)) / 4 := by ring
            _ ≤ Cconst / 4 := div_le_div_of_nonneg_right hCeven (by norm_num)
            _ = (1 / 4 : ℝ) * Cconst := by ring
    have hevenBase0 : 0 ≤
        ((Fintype.card (EvenRole n) : ℝ) / (N : ℝ)) * 2 *
          (typThr + (n : ℝ) * evenFrac * rowCap) := by positivity
    have hevenPow := pow_le_pow_left₀ hevenBase0 hevenBase n
    have hevenBudget :
        (N : ℝ) * (((Fintype.card (EvenRole n) : ℝ) / (N : ℝ)) * 2 *
          (typThr + (n : ℝ) * evenFrac * rowCap)) ^ n ≤ 1 / 16 := by
      calc
        _ ≤ (N : ℝ) * (1 / 4 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left hevenPow (by positivity)
        _ ≤ 1 / 16 := hQuarterOuter
    have hclockNumerator :
        ((Real.exp 1 - 1) * (1 / 10 ^ 9 : ℝ) - 1e-8) ≤ -(1 / 10 ^ 9 : ℝ) := by
      nlinarith [Real.exp_one_lt_three]
    have hclockRatio :
        ((Real.exp 1 - 1) * (1 / 10 ^ 9 : ℝ) - 1e-8) / groupCap ≤
          -(1 / 10 ^ 9 : ℝ) * Real.exp ((n : ℝ) ^ ζ / 2) := by
      have hinv : Real.exp ((n : ℝ) ^ ζ / 2) ≤ groupCap⁻¹ := by
        have hrec := one_div_le_one_div_of_le hgroupPos hgroupCap1
        have harg : -((n : ℝ) ^ ζ / 2) = -(n : ℝ) ^ ζ / 2 := by ring
        calc
          Real.exp ((n : ℝ) ^ ζ / 2) =
              1 / Real.exp (-((n : ℝ) ^ ζ / 2)) := by
                rw [Real.exp_neg]
                simp
          _ = 1 / Real.exp (-(n : ℝ) ^ ζ / 2) := by rw [harg]
          _ ≤ 1 / groupCap := hrec
          _ = groupCap⁻¹ := by rw [one_div]
      rw [div_eq_mul_inv]
      calc
        _ ≤ -(1 / 10 ^ 9 : ℝ) * groupCap⁻¹ :=
          mul_le_mul_of_nonneg_right hclockNumerator (by positivity)
        _ ≤ -(1 / 10 ^ 9 : ℝ) * Real.exp ((n : ℝ) ^ ζ / 2) :=
          mul_le_mul_of_nonpos_left hinv (by norm_num)
    have hclockBudget :
        (N : ℝ) * Real.exp (((Real.exp 1 - 1) * (1 / 10 ^ 9 : ℝ) - 1e-8) / groupCap) ≤
          1 / 8 := by
      calc
        _ ≤ (N : ℝ) * Real.exp (-(1 / 10 ^ 9 : ℝ) * Real.exp ((n : ℝ) ^ ζ / 2)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hclockRatio) (by positivity)
        _ ≤ (n : ℝ) * (2 : ℝ) ^ n *
            Real.exp (-(1 / 10 ^ 9 : ℝ) * Real.exp ((n : ℝ) ^ ζ / 2)) :=
          mul_le_mul_of_nonneg_right hNupperR (by positivity)
        _ ≤ 1 / 8 := hClockN
    have hrefExponent :
        (n : ℝ) ^ (-δ) * (kT n δ : ℝ) * n ≥ (n : ℝ) ^ q := by
      have hkLower : (n : ℝ) ^ (300 * δ) ≤ (kT n δ : ℝ) := by
        dsimp [kT, p10_1kTupleListLength]
        exact (Lane_q_s10_d10.ceil_power_bounds hnreal (by positivity)).1
      have hpow : (n : ℝ) ^ (-δ) * (n : ℝ) ^ (300 * δ) * (n : ℝ) =
          (n : ℝ) ^ q := by
        calc
          (n : ℝ) ^ (-δ) * (n : ℝ) ^ (300 * δ) * (n : ℝ) =
              (n : ℝ) ^ (-δ + 300 * δ) * (n : ℝ) := by rw [← Real.rpow_add hnpos]
          _ = (n : ℝ) ^ (-δ + 300 * δ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (n : ℝ) ^ ((-δ + 300 * δ) + 1) := by rw [← Real.rpow_add hnpos]
          _ = (n : ℝ) ^ q := by congr 1; dsimp [q]; ring
      have hmul := mul_le_mul_of_nonneg_left hkLower
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)) (-δ))
      have hmulN := mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤ (n : ℝ))
      calc
        (n : ℝ) ^ q = (n : ℝ) ^ (-δ) * (n : ℝ) ^ (300 * δ) * (n : ℝ) := hpow.symm
        _ ≤ (n : ℝ) ^ (-δ) * (kT n δ : ℝ) * n := hmulN
    have hrefBudget :
        Fintype.card (EvenRole n) * (2 * εref) ≤ 1 / 8 := by
      have hε := mul_le_mul_of_nonneg_left hεref1 (by norm_num : (0 : ℝ) ≤ 2)
      have hcardEq : (Fintype.card (EvenRole n) : ℝ) * 2 = (2 : ℝ) ^ n := by
        rw [hevenCard, hpowN]
        ring
      have hexpLe : Real.exp (-(1 / 200 : ℝ) *
          (aG n δ * (kT n δ : ℝ) * n)) ≤
          Real.exp (-(1 / 200 : ℝ) * (n : ℝ) ^ q) := by
        apply Real.exp_le_exp.mpr
        have hscaled := mul_le_mul_of_nonpos_left hrefExponent
          (by norm_num : (-(1 / 200 : ℝ)) ≤ 0)
        simpa [aG] using hscaled
      calc
        (Fintype.card (EvenRole n) : ℝ) * (2 * εref) ≤
            (Fintype.card (EvenRole n) : ℝ) *
              (2 * Real.exp (-(1 / 200 : ℝ) * (aG n δ * (kT n δ : ℝ) * n))) :=
          by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hε (by positivity)
        _ = ((Fintype.card (EvenRole n) : ℝ) * 2) *
              Real.exp (-(1 / 200 : ℝ) * (aG n δ * (kT n δ : ℝ) * n)) := by ring
        _ = (2 : ℝ) ^ n * Real.exp (-(1 / 200 : ℝ) *
              (aG n δ * (kT n δ : ℝ) * n)) := by rw [hcardEq]
        _ ≤ (2 : ℝ) ^ n * Real.exp (-(1 / 200 : ℝ) * (n : ℝ) ^ q) :=
          mul_le_mul_of_nonneg_left hexpLe (by positivity)
        _ ≤ 1 / 8 := hRefN
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_lt htagBudget (by norm_num)
    · have hsum := hoddBudget
      have hsum2 := hclockBudget
      have hsum3 := hrefBudget
      have hsum4 := hevenBudget
      have htotal : (1 / 100 : ℝ) + 1 / 16 + 1 / 8 + 1 / 8 + 1 / 16 < 1 := by norm_num
      linarith only [hεv1, hsum, hsum2, hsum3, hsum4, htotal]

end SubLemmas

end HypercubeRamsey.Lane_opus_s10_tagged
