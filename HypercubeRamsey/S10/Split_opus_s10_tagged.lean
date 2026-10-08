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

set_option maxHeartbeats 10000000 in
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
  classical
  obtain ⟨n6, h6⟩ := d6_likelihood_comparison η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
  have hδbound : δ < (1 : ℝ) / 2000 := by
    have hmin : min (min η₀ ζ) 1 ≤ 1 := min_le_right _ _
    exact lt_of_lt_of_le hδsmall
      (div_le_div_of_nonneg_right hmin (by norm_num))
  obtain ⟨nS, hS⟩ := Filter.eventually_atTop.1
    (Lane_q_s10_d7.evenRow_scales_eventually δ hδ hδbound)
  obtain ⟨nC, hC⟩ := Filter.eventually_atTop.1
    Lane_q_s10_d7.natCube_le_twoPow_eventually
  refine ⟨max n6 (max nS nC), ?_⟩
  intro n hn N E X Y G M σ hN hNupper t a
  have hN0 : max n6 (max nS nC) ≤ n := hn
  have hinner : max nS nC ≤ n := le_trans (le_max_right _ _) hN0
  have hn6 : n6 ≤ n := le_trans (le_max_left _ _) hN0
  have hnS : nS ≤ n := le_trans (le_max_left _ _) hinner
  have hnC : nC ≤ n := le_trans (le_max_right _ _) hinner
  have hsc := hS n hnS
  have h6spec := h6 n hn6 N E X Y G M t hN
  have hBig : 1000000000000000 ≤ n := hsc.1
  have hn3 : 3 ≤ n := by omega
  have hnCube : n ^ 3 ≤ 2 ^ n := hC n hnC
  have hlevel := Lane_q_s10_d7.heightLevels_le_cube δ hδ hδbound hn3
  have hcardSlice : Fintype.card (Slice n δ) = 2 ^ (mS n δ) := by
    simp [Slice, Fintype.card_fun]
  have hcardLoc : Fintype.card ((hp n δ).Loc) =
      2 ^ (n - mS n δ) * ((hp n δ).H + 1) := by
    have hd : (hp n δ).d = n - mS n δ := rfl
    change Fintype.card (CubeVertex (hp n δ).d × Fin ((hp n δ).H + 1)) = _
    rw [Fintype.card_prod]
    simp [card_cubeVertex, hd]
  have hcardID' : Fintype.card (ID n δ) =
      2 ^ (mS n δ) * (2 ^ (n - mS n δ) * ((hp n δ).H + 1)) := by
    change Fintype.card ((Fin (mS n δ) → Bool) × (hp n δ).Loc) = _
    rw [Fintype.card_prod, hcardSlice, hcardLoc]
  have hsum : mS n δ + (n - mS n δ) = n :=
    Nat.add_sub_of_le (mS_le n δ)
  have hcardID : Fintype.card (ID n δ) = 2 ^ n * ((hp n δ).H + 1) := by
    calc
      Fintype.card (ID n δ) =
          2 ^ (mS n δ) * (2 ^ (n - mS n δ) * ((hp n δ).H + 1)) := hcardID'
      _ = (2 ^ (mS n δ) * 2 ^ (n - mS n δ)) * ((hp n δ).H + 1) := by ring
      _ = 2 ^ (mS n δ + (n - mS n δ)) * ((hp n δ).H + 1) := by rw [← pow_add]
      _ = 2 ^ n * ((hp n δ).H + 1) := by rw [hsum]
  have hIDsmall : Fintype.card (ID n δ) ≤ 2 ^ (2 * n) := by
    rw [hcardID]
    calc
      2 ^ n * ((hp n δ).H + 1) ≤ 2 ^ n * (n ^ 3) :=
        Nat.mul_le_mul_left _ hlevel
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_left _ hnCube
      _ = 2 ^ (2 * n) := by rw [← pow_add]; congr 1 <;> omega
  let k : ℕ := kT n δ
  let a0 : ℝ := aG n δ
  let ε : ℝ := Real.exp (-(1 / 100 : ℝ) * a0 * (k : ℝ) * n)
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hlarge : 200 < a0 * (k : ℝ) := by simpa [a0, k, aG] using hsc.2.2.2.1
    norm_num [k, hk0] at hlarge
  have haPos : 0 < a0 := by
    dsimp [a0, aG]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  have hεpos : 0 < ε := Real.exp_pos _
  have hsubLik_nonneg (h : History n N δ) (c : ID n δ)
      (w : Fin k → Fin N) (ω : OddRole n → Fin N) :
      0 ≤ subLik M t h a c w ω := by
    have hstarNN (h' : History n N δ) : 0 ≤ starLik M t h' a ω := by
      unfold starLik
      apply Finset.prod_nonneg
      intro q hq
      apply Lane_q_s10_d7.finprob_expect_nonneg
      intro j
      apply Finset.prod_nonneg
      intro b hb
      exact (labLaw M t h' b j).nonneg (ω b)
    unfold subLik
    split_ifs with hg
    · exact hstarNN (History.setTuple h c w)
    · exact le_rfl
  have hNpos : 0 < N := by
    have hp : 0 < 2 ^ n := Nat.pow_pos (by omega)
    omega
  let defaultLabel : Fin N := ⟨0, hNpos⟩
  let StarData : Type := {b : OddRole n // b ∈ starOf a} → Fin N
  let GIndex : Type := {q : Site n δ // q ∈ incGroups a}
  let groupRoles : GIndex → Finset (OddRole n) := fun q =>
    (starOf a).filter (fun b => groupOf δ b = q.1)
  let GData : GIndex → Type := fun q => {b : OddRole n // b ∈ groupRoles q} → Fin N
  let defaultGroupProfile : (q : GIndex) → GData q := fun _ _ => defaultLabel
  let liftGroup : (q : GIndex) → GData q → OddRole n → Fin N := fun q u b =>
    if hb : b ∈ groupRoles q then u ⟨b, hb⟩ else defaultLabel
  let liftStar : StarData → OddRole n → Fin N := fun w b =>
    if hb : b ∈ starOf a then w ⟨b, hb⟩ else defaultLabel
  let assemble : (∀ q : GIndex, GData q) → StarData := fun z b =>
    let qsite := groupOf δ b.1
    have hq : qsite ∈ incGroups a := by
      change p10_1kProjectedVertex (mS_le n δ) b.1 ∈
        p10_1kIncidentOddGroups (mS_le n δ) a
      exact (p10_1k_mem_incidentOddGroups (mS_le n δ) a _).2
        ⟨b.1, (Finset.mem_filter.mp b.2).2, rfl⟩
    let q : GIndex := ⟨qsite, hq⟩
    let hb : b.1 ∈ groupRoles q := by
      exact Finset.mem_filter.mpr ⟨b.2, rfl⟩
    z q ⟨b.1, hb⟩
  let encode : StarData → (∀ q : GIndex, GData q) := fun w q b =>
    w ⟨b.1, (Finset.mem_filter.mp b.2).1⟩
  have hassemble_encode (w : StarData) : assemble (encode w) = w := by
    funext b
    simp [assemble, encode, groupRoles]
  let groupDeletionLaw : (h : History n N δ) → (q : GIndex) →
      (c : ID n δ) → Finset (ID n δ) → FinProb (GData q) :=
    fun h q c L =>
      let Fminus : Finset (Fin N) := Finset.univ.filter fun y =>
        ∀ c' ∈ L, c' ≠ c → ∀ i, Hits E G (h.tup c' i) y
      let ρ := maskedPrior M (t q.1.1) (h.mask q.1)
      let D := maskedCluster M (t q.1.1) (h.mask q.1)
      let A : ℝ := ∑ j, ρ.w j * (lawMassOn (D j) Fminus) ^ 2
      if hA : 0 < A then
        let J : FinProb (Fin (M.K (t q.1.1))) :=
          normalizeLaw (fun j => ρ.w j * (lawMassOn (D j) Fminus) ^ 2)
            (by intro j; exact mul_nonneg (ρ.nonneg j) (sq_nonneg _)) hA
        let labels : Fin (M.K (t q.1.1)) → FinProb (GData q) := fun j =>
          FinProb.pi (fun b : {b : OddRole n // b ∈ groupRoles q} =>
            restrictOrSelf (D j) Fminus)
        FinProb.map (FinProb.bind J labels) Prod.snd
      else
        FinProb.uniform {defaultGroupProfile q}
          ⟨defaultGroupProfile q, Finset.mem_singleton_self _⟩
  let groupReferenceLaw : (h : History n N δ) → (c : ID n δ) →
      (q : GIndex) → FinProb (GData q) := fun h c q =>
    let Ls := (lists h q.1).filter (fun L => c ∈ L)
    if hLs : Ls.Nonempty then
      FinProb.map
        (FinProb.bind (FinProb.uniform Ls hLs)
          (fun L => groupDeletionLaw h q c L)) Prod.snd
    else
      FinProb.uniform {defaultGroupProfile q}
        ⟨defaultGroupProfile q, Finset.mem_singleton_self _⟩
  have hdeletionDom (h : History n N δ) (c : ID n δ) (q : GIndex)
      (L : Finset (ID n δ)) (u : GData q) :
      deletionRef M t h a q.1 L c (liftGroup q u) ≤
        (groupDeletionLaw h q c L).w u := by
    classical
    let Fminus : Finset (Fin N) := Finset.univ.filter fun y =>
      ∀ c' ∈ L, c' ≠ c → ∀ i, Hits E G (h.tup c' i) y
    let ρ := maskedPrior M (t q.1.1) (h.mask q.1)
    let D := maskedCluster M (t q.1.1) (h.mask q.1)
    let A : ℝ := ∑ j, ρ.w j * (lawMassOn (D j) Fminus) ^ 2
    have hAnonneg : 0 ≤ A := by
      dsimp [A]
      apply Finset.sum_nonneg
      intro j hj
      apply mul_nonneg
      · exact ρ.nonneg j
      · exact sq_nonneg _
    by_cases hA : 0 < A
    · let J : FinProb (Fin (M.K (t q.1.1))) :=
        normalizeLaw (fun j => ρ.w j * (lawMassOn (D j) Fminus) ^ 2)
          (by intro j; exact mul_nonneg (ρ.nonneg j) (sq_nonneg _)) hA
      let labels : Fin (M.K (t q.1.1)) → FinProb (GData q) := fun j =>
        FinProb.pi (fun _ : {b : OddRole n // b ∈ groupRoles q} =>
          restrictOrSelf (D j) Fminus)
      have hJweight (j : Fin (M.K (t q.1.1))) :
          J.w j = ρ.w j * (lawMassOn (D j) Fminus) ^ 2 / A := by
        simp [J, normalizeLaw, A]
      have hlabelsWeight (j : Fin (M.K (t q.1.1))) :
          (labels j).w u =
            ∏ b ∈ groupRoles q, (restrictOrSelf (D j) Fminus).w (liftGroup q u b) := by
        change (∏ b : {b : OddRole n // b ∈ groupRoles q},
            (restrictOrSelf (D j) Fminus).w (u b)) = _
        have hsubtype :
            (∏ b : {b : OddRole n // b ∈ groupRoles q},
              (restrictOrSelf (D j) Fminus).w (u b)) =
            ∏ b ∈ groupRoles q, (restrictOrSelf (D j) Fminus).w
              (liftGroup q u b) := by
          let f : OddRole n → ℝ := fun b =>
            (restrictOrSelf (D j) Fminus).w (liftGroup q u b)
          have hattach : (∏ b : {b : OddRole n // b ∈ groupRoles q}, f b.1) =
              ∏ b ∈ groupRoles q, f b := by
            rw [Finset.univ_eq_attach]
            simpa [f] using Finset.prod_attach (groupRoles q) f
          calc
            (∏ b : {b : OddRole n // b ∈ groupRoles q},
                (restrictOrSelf (D j) Fminus).w (u b)) =
                ∏ b : {b : OddRole n // b ∈ groupRoles q}, f b.1 := by
              apply Finset.prod_congr rfl
              intro b hb
              simp [f, liftGroup, b.2]
            _ = ∏ b ∈ groupRoles q,
                (restrictOrSelf (D j) Fminus).w (liftGroup q u b) := hattach
        exact hsubtype
      have hmap := Lane_q_s10_d7.bind_map_snd_weight_q_s10_d7 J labels u
      have heq : deletionRef M t h a q.1 L c (liftGroup q u) =
          ∑ j, J.w j * (labels j).w u := by
        unfold deletionRef
        simp only [Fminus, ρ, D, A]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hJweight j, hlabelsWeight j]
      have hQw : (groupDeletionLaw h q c L).w u = ∑ j, J.w j * (labels j).w u := by
        simpa [groupDeletionLaw, Fminus, ρ, D, A, hA] using hmap
      rw [heq, hQw]
    · have hAzero : A = 0 := le_antisymm (le_of_not_gt hA) hAnonneg
      have hzero : deletionRef M t h a q.1 L c (liftGroup q u) = 0 := by
        unfold deletionRef
        change ∑ j, (ρ.w j * (lawMassOn (D j) Fminus) ^ 2 / A) *
          ∏ b ∈ (starOf a).filter (fun b => groupOf δ b = q.1),
            (restrictOrSelf (D j) Fminus).w (liftGroup q u b) = 0
        rw [hAzero]
        simp
      rw [hzero]
      exact (groupDeletionLaw h q c L).nonneg u
  have hgroupRefDom (h : History n N δ) (c : ID n δ) (q : GIndex)
      (u : GData q) :
      groupRef M t h a q.1 c (liftGroup q u) ≤
        (groupReferenceLaw h c q).w u := by
    classical
    let Ls := (lists h q.1).filter (fun L => c ∈ L)
    by_cases hLs : Ls.Nonempty
    · have hsum :
          ∑ L ∈ Ls, deletionRef M t h a q.1 L c (liftGroup q u) ≤
            ∑ L ∈ Ls, (groupDeletionLaw h q c L).w u := by
        apply Finset.sum_le_sum
        intro L hL
        exact hdeletionDom h c q L u
      have hbind := Lane_q_s10_d7.bind_map_snd_weight_q_s10_d7
        (FinProb.uniform Ls hLs) (fun L => groupDeletionLaw h q c L) u
      have huniform := Lane_q_s10_d7.uniform_expect_q_s10_d7 Ls hLs
        (fun L => (groupDeletionLaw h q c L).w u)
      unfold groupRef
      change ((Ls.card : ℝ)⁻¹ *
          ∑ L ∈ Ls, deletionRef M t h a q.1 L c (liftGroup q u)) ≤ _
      calc
        _ ≤ (Ls.card : ℝ)⁻¹ *
            ∑ L ∈ Ls, (groupDeletionLaw h q c L).w u :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = (FinProb.uniform Ls hLs).expect
              (fun L => (groupDeletionLaw h q c L).w u) := by
          rw [huniform, div_eq_mul_inv]
          ring
        _ = (groupReferenceLaw h c q).w u := by
          dsimp [groupReferenceLaw, Ls]
          rw [dif_pos hLs]
          change (∑ L, (FinProb.uniform Ls hLs).w L *
              (groupDeletionLaw h q c L).w u) =
            (FinProb.map
              (FinProb.bind (FinProb.uniform Ls hLs)
                (fun L => groupDeletionLaw h q c L)) Prod.snd).w u
          exact hbind.symm
    · have hLsEmpty : Ls = ∅ := Finset.not_nonempty_iff_eq_empty.mp hLs
      have hRefZero : groupRef M t h a q.1 c (liftGroup q u) = 0 := by
        simp [groupRef, Ls, hLsEmpty]
      rw [hRefZero]
      exact (groupReferenceLaw h c q).nonneg u
  have hdeletionRefNonneg (h : History n N δ) (q : Site n δ)
      (L : Finset (ID n δ)) (c : ID n δ) (ω : OddRole n → Fin N) :
      0 ≤ deletionRef M t h a q L c ω := by
    classical
    unfold deletionRef
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · exact (maskedPrior M (t q.1) (h.mask q)).nonneg j
        · exact sq_nonneg _
      · apply Finset.sum_nonneg
        intro j' hj'
        exact mul_nonneg ((maskedPrior M (t q.1) (h.mask q)).nonneg j') (sq_nonneg _)
    · apply Finset.prod_nonneg
      intro b hb
      exact (restrictOrSelf (maskedCluster M (t q.1) (h.mask q) j)
        (Finset.univ.filter fun y => ∀ c' ∈ L, c' ≠ c →
          ∀ i, Hits E G (h.tup c' i) y)).nonneg (ω b)
  have hgroupRefNonneg (h : History n N δ) (c : ID n δ)
      (q : Site n δ) (ω : OddRole n → Fin N) :
      0 ≤ groupRef M t h a q c ω := by
    unfold groupRef
    apply mul_nonneg
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · apply Finset.sum_nonneg
      intro L hL
      exact hdeletionRefNonneg h q L c ω
  have hgroupRef_eq (h : History n N δ) (c : ID n δ) (q : GIndex)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b, b ∈ groupRoles q → ω b = ω' b) :
      groupRef M t h a q.1 c ω = groupRef M t h a q.1 c ω' := by
    unfold groupRef
    congr 1
    apply Finset.sum_congr rfl
    intro L hL
    unfold deletionRef
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    congr 1
    exact hag b (by simpa [groupRoles] using hb)
  let groupLaws : (h : History n N δ) → (c : ID n δ) →
      ∀ q : GIndex, FinProb (GData q) := fun h c q => groupReferenceLaw h c q
  let Qstar (h : History n N δ) (c : ID n δ) : FinProb StarData :=
    FinProb.map (FinProb.pi (groupLaws h c)) assemble
  have hQdom (h : History n N δ) (c : ID n δ) (w : StarData) :
      refQ M t h a c (liftStar w) ≤ (Qstar h c).w w := by
    let enc := encode w
    have hmap := Lane_q_s10_d7.map_weight_ge_image_q_s10_d7
      (FinProb.pi (groupLaws h c)) assemble enc
    have hmap' :
        (FinProb.pi (groupLaws h c)).w enc ≤ (Qstar h c).w w := by
      simpa [Qstar, enc, hassemble_encode] using hmap
    have hpi : (FinProb.pi (groupLaws h c)).w enc =
        ∏ q : GIndex, (groupReferenceLaw h c q).w (enc q) := rfl
    have hlocal (q : GIndex) :
        groupRef M t h a q.1 c (liftStar w) ≤
          (groupReferenceLaw h c q).w (enc q) := by
      have hag : ∀ b, b ∈ groupRoles q →
          liftGroup q (enc q) b = liftStar w b := by
        intro b hb
        rcases Finset.mem_filter.mp hb with ⟨hbStar, hbGroup⟩
        simp [liftGroup, liftStar, enc, encode, groupRoles, hbStar, hbGroup]
      rw [← hgroupRef_eq h c q _ _ hag]
      exact hgroupRefDom h c q (enc q)
    have hprod :
        (∏ q : GIndex, groupRef M t h a q.1 c (liftStar w)) ≤
          ∏ q : GIndex, (groupReferenceLaw h c q).w (enc q) := by
      apply Finset.prod_le_prod₀
      · intro q hq
        exact hgroupRefNonneg h c q.1 (liftStar w)
      · intro q hq
        exact hlocal q
    have hrefQ : refQ M t h a c (liftStar w) =
        ∏ q : GIndex, groupRef M t h a q.1 c (liftStar w) := by
      unfold refQ
      rw [← Finset.prod_coe_sort]
    calc
      refQ M t h a c (liftStar w) =
          ∏ q : GIndex, groupRef M t h a q.1 c (liftStar w) := hrefQ
      _ ≤ ∏ q : GIndex, (groupReferenceLaw h c q).w (enc q) := hprod
      _ = (FinProb.pi (groupLaws h c)).w enc := hpi.symm
      _ ≤ (Qstar h c).w w := hmap'
  have hlowBound (h : History n N δ) (c : ID n δ) :
      ∑ w : StarData,
        (if predMass M t h a c (liftStar w) = 0 ∨
            predMass M t h a c (liftStar w) < ε * refQ M t h a c (liftStar w)
          then predMass M t h a c (liftStar w) else 0) ≤ ε := by
    classical
    let π : FinProb (Fin k → Fin N) := tuplePrior M t c
    let F : (Fin k → Fin N) → StarData → ℝ := fun w z =>
      subLik M t h a c w (liftStar z)
    let Q : FinProb StarData := Qstar h c
    let s : ℝ := (Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * n
    have hF0 : ∀ w z, 0 ≤ F w z := by
      intro w z
      exact hsubLik_nonneg h c w (liftStar z)
    have hF : ∀ w z, F w z ≤ Real.exp s * Q.w z := by
      intro w z
      have h6 := h6spec h a c w (liftStar z)
      calc
        F w z ≤ Real.exp
            ((Real.log 2 - (6 / 100 : ℝ) * aG n δ) * kT n δ * n) *
              refQ M t h a c (liftStar z) := by
          simpa [F] using h6
        _ ≤ Real.exp s * Q.w z := by
          apply mul_le_mul_of_nonneg_left (hQdom h c z)
          exact Real.exp_nonneg _
    have htest := p10_1i_predictive_test π F hF0 Q ε s hεpos
    let m : StarData → ℝ := fun z => ∑ w, π.w w * F w z
    have hm_eq (z : StarData) : m z = predMass M t h a c (liftStar z) := by
      simp only [m, F, π, predMass, HypercubeRamsey.FinProb.expect]
      rfl
    have hm_nonneg (z : StarData) : 0 ≤ m z := by
      unfold m
      apply Finset.sum_nonneg
      intro w hw
      exact mul_nonneg (π.nonneg w) (hF0 w z)
    have hterm (z : StarData) :
        (if m z = 0 ∨ m z < ε * refQ M t h a c (liftStar z) then m z else 0) ≤
          (if m z < ε * Q.w z ∨ m z = 0 then m z else 0) := by
      by_cases hz : m z = 0
      · simp [hz]
      · by_cases hlow : m z < ε * refQ M t h a c (liftStar z)
        · have hq : m z < ε * Q.w z :=
            lt_of_lt_of_le hlow
              (mul_le_mul_of_nonneg_left (hQdom h c z) (le_of_lt hεpos))
          simp [hz, hlow, hq]
        · by_cases hq : m z < ε * Q.w z
          · simpa [hz, hlow, hq] using hm_nonneg z
          · simp [hz, hlow, hq]
    have hsum := htest.1
    have hbound_m :
      ∑ z : StarData,
          (if m z = 0 ∨ m z < ε * refQ M t h a c (liftStar z) then m z else 0) ≤
        ε := by
      calc
        _ ≤ ∑ z : StarData, (if m z < ε * Q.w z ∨ m z = 0 then m z else 0) :=
          Finset.sum_le_sum (fun z hz => hterm z)
        _ ≤ ε := hsum
    simpa [hm_eq] using hbound_m
  have hlightPos (h : History n N δ) (c : ID n δ) (ω : OddRole n → Fin N)
      (hmass : 0 < predMass M t h a c ω)
      (hpass : ε * refQ M t h a c ω ≤ predMass M t h a c ω) :
      0 < lightMass M t h a c ω := by
    classical
    let π : FinProb (Fin k → Fin N) := tuplePrior M t c
    let P : FinProb (Fin k → Fin N) := {
      w := fun w => posterior M t h a c ω w
      nonneg := by
        intro w
        unfold posterior
        exact div_nonneg
          (mul_nonneg (π.nonneg w) (hsubLik_nonneg h c w ω)) hmass.le
      sum_eq_one := by
        have hsum :
            (∑ w : Fin k → Fin N, π.w w * subLik M t h a c w ω) =
              predMass M t h a c ω := by
          unfold predMass HypercubeRamsey.FinProb.expect
          rfl
        change ∑ w : Fin k → Fin N,
          (π.w w * subLik M t h a c w ω) / predMass M t h a c ω = 1
        rw [← Finset.sum_div, hsum, div_self hmass.ne']
    }
    have havgEq (y : Fin N) :
        avgMarginal M t h a c ω y =
          HypercubeRamsey.averageCoordinateMarginal P y := by
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
        _ = (k : ℝ)⁻¹ * ∑ i : Fin k, P.pr (fun w => w i = y) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          unfold HypercubeRamsey.FinProb.pr
          apply Finset.sum_congr rfl
          intro w hw
          simp [P]
    have havgNonneg (y : Fin N) : 0 ≤ avgMarginal M t h a c ω y := by
      rw [havgEq]
      exact Lane_q_s10_d7.averageCoordinateMarginal_nonneg P y
    have htotal : ∑ y : Fin N, avgMarginal M t h a c ω y = 1 := by
      calc
        ∑ y : Fin N, avgMarginal M t h a c ω y =
            ∑ y : Fin N, HypercubeRamsey.averageCoordinateMarginal P y := by
          apply Finset.sum_congr rfl
          intro y hy
          exact havgEq y
        _ = 1 := Lane_q_s10_d7.averageCoordinateMarginal_sum_one P hkpos
    let B : Finset (Fin N) := heavy M t h a c ω
    let Bexp : ℝ := (Real.log 2 - (2 / 100 : ℝ) * a0) * n
    have hBsum : ∑ y ∈ B, avgMarginal M t h a c ω y ≤ 1 := by
      calc
        ∑ y ∈ B, avgMarginal M t h a c ω y ≤ ∑ y : Fin N, avgMarginal M t h a c ω y := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro y hy hnot
          exact havgNonneg y
        _ = 1 := htotal
    have hBcard : ((B.card : ℝ) / (N : ℝ)) ≤ Real.exp (-Bexp) := by
      have hterm (y : Fin N) (hy : y ∈ B) :
          Real.exp Bexp ≤ (N : ℝ) * avgMarginal M t h a c ω y := by
        have hmem := Finset.mem_filter.mp hy
        simpa [B, Bexp, heavy] using le_of_lt hmem.2
      have hmul : (B.card : ℝ) * Real.exp Bexp ≤ (N : ℝ) := by
        calc
          (B.card : ℝ) * Real.exp Bexp =
              ∑ y ∈ B, Real.exp Bexp := by simp
          _ ≤ ∑ y ∈ B, (N : ℝ) * avgMarginal M t h a c ω y := by
            apply Finset.sum_le_sum
            intro y hy
            exact hterm y hy
          _ = (N : ℝ) * ∑ y ∈ B, avgMarginal M t h a c ω y := by
            rw [← Finset.mul_sum]
          _ ≤ (N : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hBsum (Nat.cast_nonneg N)
          _ = (N : ℝ) := by ring
      have hcardDiv : (B.card : ℝ) ≤ (N : ℝ) / Real.exp Bexp := by
        apply (le_div_iff₀ (Real.exp_pos Bexp)).2
        simpa [mul_comm] using hmul
      apply (div_le_iff₀ (Nat.cast_pos.mpr hNpos)).2
      calc
        (B.card : ℝ) ≤ (N : ℝ) / Real.exp Bexp := hcardDiv
        _ = Real.exp (-Bexp) * (N : ℝ) := by
          rw [div_eq_mul_inv, Real.exp_neg]
          ring
    let S : Finset (Fin k → Fin N) := Finset.univ.filter fun w => ∀ i, w i ∈ B
    have hScard : S.card ≤ B.card ^ k := by
      let f : {w : Fin k → Fin N // w ∈ S} → (Fin k → {y : Fin N // y ∈ B}) :=
        fun w i => ⟨w.1 i, (Finset.mem_filter.mp w.2).2 i⟩
      have hf : Function.Injective f := by
        intro w w' heq
        apply Subtype.ext
        funext i
        exact congrArg Subtype.val (congrFun heq i)
      have hcard : Fintype.card (↥S) ≤ Fintype.card (Fin k → {y : Fin N // y ∈ B}) :=
        Fintype.card_le_of_injective f hf
      calc
        S.card = Fintype.card (↥S) := (Fintype.card_coe S).symm
        _ ≤ Fintype.card (Fin k → {y : Fin N // y ∈ B}) := hcard
        _ = B.card ^ k := by simp
    have hAtom (w : Fin k → Fin N) :
        (N : ℝ) ^ k * P.w w ≤
          Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
            (k : ℝ) * (n : ℝ) ^ δ) := by
      have hlik := h6spec h a c w ω
      let α : ℝ := (1 / 100 : ℝ) * a0 * (k : ℝ) * n
      have hdivRef : refQ M t h a c ω ≤ predMass M t h a c ω / ε := by
        apply (le_div_iff₀ hεpos).2
        simpa [ε, α, mul_comm, mul_left_comm, mul_assoc] using hpass
      have hεeq : ε = Real.exp (-α) := by
        dsimp [ε, α]
        congr 1 <;> ring
      have hinv : ε⁻¹ = Real.exp α := by
        rw [hεeq]
        rw [Real.exp_neg]
        simp
      have hnum : subLik M t h a c w ω ≤
          Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n) *
            predMass M t h a c ω := by
        calc
          subLik M t h a c w ω ≤
              Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * n) *
                refQ M t h a c ω := by simpa [k, a0] using hlik
          _ ≤ Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * n) *
                (predMass M t h a c ω / ε) :=
            mul_le_mul_of_nonneg_left hdivRef (Real.exp_nonneg _)
          _ = Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n) *
                predMass M t h a c ω := by
            calc
              _ = Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * n) *
                    (predMass M t h a c ω * Real.exp α) := by
                rw [show predMass M t h a c ω / ε =
                    predMass M t h a c ω * ε⁻¹ by rw [div_eq_mul_inv], hinv]
              _ = (Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * n) *
                    Real.exp α) * predMass M t h a c ω := by ring
              _ = Real.exp ((Real.log 2 - (6 / 100 : ℝ) * a0) * (k : ℝ) * n + α) *
                    predMass M t h a c ω := by rw [← Real.exp_add]
              _ = Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n) *
                    predMass M t h a c ω := by congr 1 <;> dsimp [α] <;> ring
      have hratio : subLik M t h a c w ω / predMass M t h a c ω ≤
          Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n) := by
        apply (div_le_iff₀ hmass).2
        exact hnum
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
      have hratioNN : 0 ≤ subLik M t h a c w ω / predMass M t h a c ω :=
        div_nonneg (hsubLik_nonneg h c w ω) hmass.le
      calc
        (N : ℝ) ^ k * P.w w =
            ((N : ℝ) ^ k * (tuplePrior M t c).w w) *
              (subLik M t h a c w ω / predMass M t h a c ω) := by
                simp [P, posterior]
                ring
        _ ≤ Real.exp ((k : ℝ) * (n : ℝ) ^ δ) *
              Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n) :=
          mul_le_mul htuple hratio hratioNN (Real.exp_nonneg _)
        _ = Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
              (k : ℝ) * (n : ℝ) ^ δ) := by rw [← Real.exp_add]; congr 1 <;> ring
    have hBmass :
        ∑ w ∈ S, P.w w ≤
          ((B.card : ℝ) / (N : ℝ)) ^ k *
            Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
              (k : ℝ) * (n : ℝ) ^ δ) := by
      have hAtomDiv (w : Fin k → Fin N) : P.w w ≤
          Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
            (k : ℝ) * (n : ℝ) ^ δ) / (N : ℝ) ^ k := by
        apply (le_div_iff₀ (pow_pos (Nat.cast_pos.mpr hNpos) k)).2
        simpa [mul_comm] using hAtom w
      have hSumCap : ∑ w ∈ S, P.w w ≤
          (S.card : ℝ) *
            (Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
              (k : ℝ) * (n : ℝ) ^ δ) / (N : ℝ) ^ k) := by
        calc
          ∑ w ∈ S, P.w w ≤
              ∑ w ∈ S,
                Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
                  (k : ℝ) * (n : ℝ) ^ δ) / (N : ℝ) ^ k := by
            apply Finset.sum_le_sum
            intro w hw
            exact hAtomDiv w
          _ = (S.card : ℝ) *
              (Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
                (k : ℝ) * (n : ℝ) ^ δ) / (N : ℝ) ^ k) := by simp
      have hcardReal : (S.card : ℝ) ≤ (B.card : ℝ) ^ k := by exact_mod_cast hScard
      calc
        ∑ w ∈ S, P.w w ≤ (S.card : ℝ) *
            (Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
              (k : ℝ) * (n : ℝ) ^ δ) / (N : ℝ) ^ k) := hSumCap
        _ ≤ (B.card : ℝ) ^ k *
            (Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
              (k : ℝ) * (n : ℝ) ^ δ) / (N : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_right hcardReal (by positivity)
        _ = ((B.card : ℝ) / (N : ℝ)) ^ k *
            Real.exp ((Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
              (k : ℝ) * (n : ℝ) ^ δ) := by
          rw [div_pow]
          field_simp [ne_of_gt (Nat.cast_pos.mpr hNpos)]
          <;> ring
    let Sexp : ℝ := (Real.log 2 - (5 / 100 : ℝ) * a0) * (k : ℝ) * n +
      (k : ℝ) * (n : ℝ) ^ δ
    have hratioB : 0 ≤ (B.card : ℝ) / (N : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hexpAll : Sexp - Bexp * (k : ℝ) < 0 := by
      have hwidth := hsc.2.1
      dsimp [a0, aG] at ⊢
      dsimp [Sexp, Bexp]
      nlinarith [mul_lt_mul_of_pos_right hwidth (Nat.cast_pos.mpr hkpos), haPos,
        (show 0 < (n : ℝ) by exact_mod_cast (show 0 < n by omega))]
    have hAllUpper : ∑ w ∈ S, P.w w < 1 := by
      calc
        ∑ w ∈ S, P.w w ≤ ((B.card : ℝ) / (N : ℝ)) ^ k * Real.exp Sexp := by
          simpa [Sexp] using hBmass
        _ ≤ Real.exp (-Bexp) ^ k * Real.exp Sexp := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ hratioB hBcard k) (Real.exp_nonneg _)
        _ = Real.exp ((k : ℝ) * (-Bexp) + Sexp) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
        _ = Real.exp (Sexp - Bexp * (k : ℝ)) := by congr 1 <;> ring
        _ < 1 := (Real.exp_lt_one_iff).2 hexpAll
    by_contra hnot
    have hzero : lightMass M t h a c ω = 0 := le_antisymm (le_of_not_gt hnot)
      (by unfold lightMass; apply Finset.sum_nonneg; intro y hy; exact havgNonneg y)
    have hlightMarginalZero (y : Fin N) (hy : y ∉ B) :
        avgMarginal M t h a c ω y = 0 := by
      have hyS : y ∈ Finset.univ \ B := by simp [hy]
      have hterm := Finset.single_le_sum
        (s := Finset.univ \ B)
        (f := fun z => avgMarginal M t h a c ω z)
        (by intro z hz; exact havgNonneg z) hyS
      have hnonneg := havgNonneg y
      unfold lightMass at hzero
      rw [hzero] at hterm
      exact le_antisymm hterm hnonneg
    have houtsideZero (w : Fin k → Fin N) (hw : w ∉ S) : P.w w = 0 := by
      have hnotAll : ¬ ∀ i, w i ∈ B := by
        intro hall
        apply hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩
      obtain ⟨i, hi⟩ := not_forall.mp hnotAll
      have hfreqpos : 0 <
          (((Finset.univ.filter fun j : Fin k => w j = w i).card : ℝ) / (k : ℝ)) := by
        have hcard : 0 < (Finset.univ.filter fun j : Fin k => w j = w i).card :=
          Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        exact div_pos (by exact_mod_cast hcard) (Nat.cast_pos.mpr hkpos)
      have hsumTerm : posterior M t h a c ω w *
          (((Finset.univ.filter fun j : Fin k => w j = w i).card : ℝ) / (k : ℝ)) ≤
            avgMarginal M t h a c ω (w i) := by
        unfold avgMarginal
        let f : (Fin k → Fin N) → ℝ := fun z => posterior M t h a c ω z *
          (((Finset.univ.filter fun j : Fin k => z j = w i).card : ℝ) / (k : ℝ))
        change f w ≤ ∑ z ∈ Finset.univ, f z
        exact Finset.single_le_sum (f := f)
          (fun z hz => by
            dsimp [f]
            apply mul_nonneg
            · unfold posterior
              exact div_nonneg (mul_nonneg (π.nonneg z) (hsubLik_nonneg h c z ω)) hmass.le
            · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (Finset.mem_univ w)
      have hzeroAvg := hlightMarginalZero (w i) hi
      have hpostZero : posterior M t h a c ω w = 0 := by
        by_contra hnpost
        have hpostNN : 0 ≤ posterior M t h a c ω w := by
          unfold posterior
          exact div_nonneg (mul_nonneg (π.nonneg w) (hsubLik_nonneg h c w ω)) hmass.le
        have hpostPos : 0 < posterior M t h a c ω w := by
          by_contra hn
          have hz : posterior M t h a c ω w = 0 :=
            le_antisymm (le_of_not_gt hn) hpostNN
          exact hnpost hz
        have hprodPos := mul_pos hpostPos hfreqpos
        rw [hzeroAvg] at hsumTerm
        linarith
      simpa [P] using hpostZero
    have hAllEq : ∑ w ∈ S, P.w w = 1 := by
      have hcomplement : ∑ w ∈ Finset.univ \ S, P.w w = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        exact houtsideZero w (Finset.mem_sdiff.mp hw).2
      have hsplit := Finset.sum_add_sum_compl S (fun w => P.w w)
      rw [P.sum_eq_one] at hsplit
      have hsplit' :
          (∑ w ∈ S, P.w w) + ∑ w ∈ Finset.univ \ S, P.w w = 1 := by
        simpa [Finset.compl_eq_univ_sdiff] using hsplit
      rw [hcomplement] at hsplit'
      linarith
    linarith [hAllUpper, hAllEq]
  have hstarLikEq (h : History n N δ) (ω ω' : OddRole n → Fin N)
      (hag : ∀ b, b ∈ starOf a → ω b = ω' b) :
      starLik M t h a ω = starLik M t h a ω' := by
    unfold starLik
    apply Finset.prod_congr rfl
    intro q hq
    unfold HypercubeRamsey.FinProb.expect
    apply Finset.sum_congr rfl
    intro z hz
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    exact congrArg (fun y => (labLaw M t h b z).w y)
      (hag b (Finset.mem_filter.mp hb).1)
  have hsubLikEq (h : History n N δ) (c : ID n δ) (w : Fin k → Fin N)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b, b ∈ starOf a → ω b = ω' b) :
      subLik M t h a c w ω = subLik M t h a c w ω' := by
    unfold subLik
    rw [hstarLikEq (History.setTuple h c w) ω ω' hag]
  have hpredMassEq (h : History n N δ) (c : ID n δ)
      (ω ω' : OddRole n → Fin N)
      (hag : ∀ b, b ∈ starOf a → ω b = ω' b) :
      predMass M t h a c ω = predMass M t h a c ω' := by
    unfold predMass HypercubeRamsey.FinProb.expect
    apply Finset.sum_congr rfl
    intro w hw
    exact congrArg (fun x => (tuplePrior M t c).w w * x)
      (hsubLikEq h c w ω ω' hag)
  have hdeletionRefEq (h : History n N δ) (q : Site n δ)
      (L : Finset (ID n δ)) (c : ID n δ) (ω ω' : OddRole n → Fin N)
      (hag : ∀ b, b ∈ starOf a → ω b = ω' b) :
      deletionRef M t h a q L c ω = deletionRef M t h a q L c ω' := by
    unfold deletionRef
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    exact congrArg (fun y =>
      (restrictOrSelf (maskedCluster M (t q.1) (h.mask q) j)
        (Finset.univ.filter fun y => ∀ c' ∈ L, c' ≠ c →
          ∀ i, Hits E G (h.tup c' i) y)).w y) (hag b (Finset.mem_filter.mp hb).1)
  have hrefQEq (h : History n N δ) (c : ID n δ) (ω ω' : OddRole n → Fin N)
      (hag : ∀ b, b ∈ starOf a → ω b = ω' b) :
      refQ M t h a c ω = refQ M t h a c ω' := by
    unfold refQ
    apply Finset.prod_congr rfl
    intro q hq
    unfold groupRef
    congr 1
    apply Finset.sum_congr rfl
    intro L hL
    exact hdeletionRefEq h q L c ω ω' hag
  let restrictStar : (OddRole n → Fin N) → StarData := fun ω b => ω b.1
  have hLiftRestrict (ω : OddRole n → Fin N) (b : OddRole n)
      (hb : b ∈ starOf a) : liftStar (restrictStar ω) b = ω b := by
    simp [liftStar, restrictStar, hb]
  have hgroupOf_mem (b : OddRole n) (hb : b ∈ starOf a) :
      groupOf δ b ∈ incGroups a := by
    change p10_1kProjectedVertex (mS_le n δ) b.1 ∈
      p10_1kIncidentOddGroups (mS_le n δ) a
    exact (p10_1k_mem_incidentOddGroups (mS_le n δ) a _).2
      ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩
  have hpredMassLift (h : History n N δ) (c : ID n δ) (ω : OddRole n → Fin N) :
      predMass M t h a c ω = predMass M t h a c (liftStar (restrictStar ω)) := by
    apply hpredMassEq
    intro b hb
    exact (hLiftRestrict ω b hb).symm
  have hrefQLift (h : History n N δ) (c : ID n δ) (ω : OddRole n → Fin N) :
      refQ M t h a c ω = refQ M t h a c (liftStar (restrictStar ω)) := by
    apply hrefQEq
    intro b hb
    exact (hLiftRestrict ω b hb).symm
  let lowStar (h : History n N δ) (c : ID n δ) (z : StarData) : Prop :=
    predMass M t h a c (liftStar z) = 0 ∨
      predMass M t h a c (liftStar z) < ε * refQ M t h a c (liftStar z)
  have hsetTupleOverwrite (h : History n N δ) (c : ID n δ)
      (w₀ w : Fin k → Fin N) :
      History.setTuple (History.setTuple h c w₀) c w = History.setTuple h c w := by
    simp [History.setTuple, History.pos, History.tup, History.mask,
      History.act, History.tie, Function.update_idem]
  have hsubLikTupleInvariant (h : History n N δ) (c : ID n δ)
      (w₀ w : Fin k → Fin N) (ω : OddRole n → Fin N) :
      subLik M t (History.setTuple h c w₀) a c w ω = subLik M t h a c w ω := by
    unfold subLik
    rw [hsetTupleOverwrite]
  have hpredMassTupleInvariant (h : History n N δ) (c : ID n δ)
      (w₀ : Fin k → Fin N) (ω : OddRole n → Fin N) :
      predMass M t (History.setTuple h c w₀) a c ω = predMass M t h a c ω := by
    unfold predMass HypercubeRamsey.FinProb.expect
    apply Finset.sum_congr rfl
    intro w hw
    exact congrArg (fun x => (tuplePrior M t c).w w * x)
      (hsubLikTupleInvariant h c w₀ w ω)
  have hdeletionTupleInvariant (h : History n N δ) (q : Site n δ)
      (L : Finset (ID n δ)) (c : ID n δ) (w₀ : Fin k → Fin N)
      (ω : OddRole n → Fin N) :
      deletionRef M t (History.setTuple h c w₀) a q L c ω =
        deletionRef M t h a q L c ω := by
    unfold deletionRef
    simp [History.setTuple, History.tup, Function.update_apply]
  have hrefQTupleInvariant (h : History n N δ) (c : ID n δ)
      (w₀ : Fin k → Fin N) (ω : OddRole n → Fin N) :
      refQ M t (History.setTuple h c w₀) a c ω = refQ M t h a c ω := by
    unfold refQ
    apply Finset.prod_congr rfl
    intro q hq
    unfold groupRef
    congr 1
    have hlists : lists (History.setTuple h c w₀) q = lists h q := by
      simp [lists, candidates, History.setTuple, History.pos]
    rw [hlists]
    apply Finset.sum_congr rfl
    intro L hL
    exact hdeletionTupleInvariant h q L c w₀ ω
  have hlowTupleInvariant (h : History n N δ) (c : ID n δ)
      (w₀ : Fin k → Fin N) (z : StarData) :
      lowStar (History.setTuple h c w₀) c z = lowStar h c z := by
    simp [lowStar, hpredMassTupleInvariant, hrefQTupleInvariant]
  let groupRoleSet : Site n δ → Finset (OddRole n) := fun q =>
    (starOf a).filter (fun b => groupOf δ b = q)
  let starLabelLaw (h : History n N δ) (C : Site n δ → ClIdx M) : FinProb StarData :=
    FinProb.pi (fun b : {b : OddRole n // b ∈ starOf a} =>
      labLaw M t h b.1 (C (groupOf δ b.1)))
  let groupFactor (h : History n N δ) (z : StarData) (q : Site n δ)
      (j : ClIdx M) : ℝ :=
    ∏ b ∈ groupRoleSet q, (labLaw M t h b j).w (liftStar z b)
  let clusterFactor (h : History n N δ) (z : StarData)
      (q : Site n δ) (j : ClIdx M) : ℝ :=
    if q ∈ incGroups a then groupFactor h z q j else 1
  letI : DecidableEq (Site n δ) := instDecidableEqProd
  have hgroupRole_product (h : History n N δ) (z : StarData)
      (C : Site n δ → ClIdx M) :
      ∏ b : {b : OddRole n // b ∈ starOf a},
          (labLaw M t h b.1 (C (groupOf δ b.1))).w (liftStar z b.1) =
        ∏ q ∈ incGroups a, groupFactor h z q (C q) := by
    let f : OddRole n → ℝ := fun b =>
      (labLaw M t h b (C (groupOf δ b))).w (liftStar z b)
    have hset : (starOf a).filter (fun b => groupOf δ b ∈ incGroups a) = starOf a := by
      ext b
      simp only [Finset.mem_filter]
      constructor
      · exact And.left
      · intro hb
        exact ⟨hb, hgroupOf_mem b hb⟩
    have hattach :
        (∏ b : {b : OddRole n // b ∈ starOf a}, f b.1) =
          ∏ b ∈ starOf a, f b := by
      rw [Finset.univ_eq_attach]
      simpa [f] using Finset.prod_attach (starOf a) f
    calc
      ∏ b : {b : OddRole n // b ∈ starOf a},
          (labLaw M t h b.1 (C (groupOf δ b.1))).w (liftStar z b.1) =
        ∏ b ∈ starOf a, f b := by simpa [f] using hattach
      _ = ∏ b ∈ (starOf a).filter (fun b => groupOf δ b ∈ incGroups a), f b := by
        rw [hset]
      _ = ∏ q ∈ incGroups a,
          ∏ b ∈ (starOf a).filter (fun b => groupOf δ b = q), f b :=
        (Finset.prod_fiberwise_eq_prod_filter (starOf a) (incGroups a)
          (groupOf δ) f).symm
      _ = ∏ q ∈ incGroups a, groupFactor h z q (C q) := by
        apply Finset.prod_congr rfl
        intro q hq
        unfold groupFactor groupRoleSet
        apply Finset.prod_congr rfl
        intro b hb
        have hbq : groupOf δ b = q := (Finset.mem_filter.mp hb).2
        simp [f, hbq]
  have hstarLikCluster (h : History n N δ) (z : StarData) :
      starLik M t h a (liftStar z) =
        (FinProb.pi (fun q : Site n δ => clusterLaw M t h q)).expect
          (fun C => ∏ b : {b : OddRole n // b ∈ starOf a},
            (labLaw M t h b.1 (C (groupOf δ b.1))).w (liftStar z b.1)) := by
    let f : Site n δ → ClIdx M → ℝ := fun q j => clusterFactor h z q j
    have hIncFilter :
        (Finset.univ : Finset (Site n δ)).filter (fun q => q ∈ incGroups a) =
          incGroups a := by
      ext q
      simp
    have hfactor (C : Site n δ → ClIdx M) :
      (∏ b : {b : OddRole n // b ∈ starOf a},
          (labLaw M t h b.1 (C (groupOf δ b.1))).w (liftStar z b.1)) =
            ∏ q : Site n δ, f q (C q) := by
      rw [hgroupRole_product]
      calc
        ∏ q ∈ incGroups a, groupFactor h z q (C q) =
            ∏ q : Site n δ,
              if q ∈ incGroups a then groupFactor h z q (C q) else 1 := by
          rw [← hIncFilter, Finset.prod_filter]
        _ = ∏ q : Site n δ, f q (C q) := by simp [f, clusterFactor]
    have hexpect := Lane_q_s10_d7.pi_expect_prod_q_s10_d7
      (fun q : Site n δ => clusterLaw M t h q) f
    unfold starLik
    calc
      (∏ q ∈ incGroups a,
          (clusterLaw M t h q).expect (fun j => groupFactor h z q j)) =
        ∏ q : Site n δ, (clusterLaw M t h q).expect (f q) := by
          calc
            ∏ q ∈ incGroups a,
                (clusterLaw M t h q).expect (fun j => groupFactor h z q j) =
              ∏ q : Site n δ, if q ∈ incGroups a then
                (clusterLaw M t h q).expect (fun j => groupFactor h z q j) else 1 := by
                  rw [← hIncFilter, Finset.prod_filter]
            _ = ∏ q : Site n δ, (clusterLaw M t h q).expect (f q) := by
              apply Finset.prod_congr rfl
              intro q hq
              by_cases hqi : q ∈ incGroups a
              · simp [f, clusterFactor, hqi]
              · simp [f, clusterFactor, hqi, FinProb.expect_const]
      _ = (FinProb.pi (fun q : Site n δ => clusterLaw M t h q)).expect
          (fun C => ∏ q : Site n δ, f q (C q)) := hexpect.symm
      _ = (FinProb.pi (fun q : Site n δ => clusterLaw M t h q)).expect
          (fun C => ∏ b : {b : OddRole n // b ∈ starOf a},
            (labLaw M t h b.1 (C (groupOf δ b.1))).w (liftStar z b.1)) := by
          apply Finset.sum_congr rfl
          intro C hC
          rw [hfactor C]
  have hprEq {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
      P.pr A = P.expect (fun x => if A x then (1 : ℝ) else 0) := by
    simp [FinProb.pr, FinProb.expect]
  have hstarLabelPr (h : History n N δ) (C : Site n δ → ClIdx M)
      (A : StarData → Prop) :
      (starLabelLaw h C).pr (fun z => A z) =
        (FinProb.pi (fun b : OddRole n => labLaw M t h b (C (groupOf δ b)))).pr
          (fun ω => A (restrictStar ω)) := by
    classical
    let Pfull := fun b : OddRole n => labLaw M t h b (C (groupOf δ b))
    let Pstar := fun b : {b : OddRole n // b ∈ starOf a} => Pfull b.1
    let e := Equiv.piEquivPiSubtypeProd (fun b : OddRole n => b ∈ starOf a)
      (fun _ : OddRole n => Fin N)
    let outside : ∀ b : {b : OddRole n // b ∉ starOf a}, Fin N := fun _ => defaultLabel
    let F : (OddRole n → Fin N) → ℝ := fun ω =>
      if A (restrictStar ω) then 1 else 0
    have hdep : FinProb.DependsOn F (starOf a) := by
      intro ω ω' hag
      have hrestrict : restrictStar ω = restrictStar ω' := by
        funext b
        exact hag b.1 b.2
      simp [F, hrestrict]
    have hExt (z : StarData) : restrictStar (e.symm (z, outside)) = z := by
      funext b
      simp [restrictStar, e, outside, Equiv.piEquivPiSubtypeProd]
    have hexpect := FinProb.pi_expect_depends Pfull (starOf a) F
      (fun _ : OddRole n => defaultLabel) hdep
    have hfullToStar :
        (FinProb.pi Pfull).pr (fun ω => A (restrictStar ω)) =
          (FinProb.pi Pstar).pr A := by
      calc
        (FinProb.pi Pfull).pr (fun ω => A (restrictStar ω)) =
            (FinProb.pi Pfull).expect F := hprEq _ _
        _ = (FinProb.pi Pstar).expect
            (fun z => F (e.symm (z, outside))) := by
          exact hexpect
        _ = (FinProb.pi Pstar).expect (fun z => if A z then (1 : ℝ) else 0) := by
          unfold HypercubeRamsey.FinProb.expect
          apply Finset.sum_congr rfl
          intro z hz
          simp [F, hExt]
        _ = (FinProb.pi Pstar).pr A := (hprEq _ _).symm
    simpa [starLabelLaw, Pfull, Pstar] using hfullToStar.symm
  have hstarMarginal (h : History n N δ) (A : StarData → Prop) :
      ∑ C : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w C *
        (FinProb.pi (fun b : OddRole n => labLaw M t h b (C (groupOf δ b))).pr
          (fun ω => A (restrictStar ω))) =
        ∑ z : StarData, starLik M t h a (liftStar z) * (if A z then 1 else 0) := by
    classical
    have hstarSum (z : StarData) :
        ∑ C : Site n δ → ClIdx M,
            (FinProb.pi (clusterLaw M t h)).w C * (starLabelLaw h C).w z =
          starLik M t h a (liftStar z) := by
      have hh := hstarLikCluster h z
      simpa [starLabelLaw, HypercubeRamsey.FinProb.expect,
        HypercubeRamsey.FinProb.pi] using hh
    calc
      ∑ C : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w C *
            (FinProb.pi (fun b : OddRole n => labLaw M t h b (C (groupOf δ b))).pr
              (fun ω => A (restrictStar ω))) =
            ∑ C : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w C *
          (starLabelLaw h C).pr A := by
            apply Finset.sum_congr rfl
            intro C hC
            rw [← hstarLabelPr h C A]
      _ = ∑ C : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w C *
          ∑ z : StarData, if A z then (starLabelLaw h C).w z else 0 := by
            apply Finset.sum_congr rfl
            intro C hC
            simp [HypercubeRamsey.FinProb.pr]
      _ = ∑ z : StarData, ∑ C : Site n δ → ClIdx M,
          (FinProb.pi (clusterLaw M t h)).w C *
            (if A z then (starLabelLaw h C).w z else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ z : StarData, starLik M t h a (liftStar z) * (if A z then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro z hz
            by_cases hA : A z
            · simp [hA, ← Finset.mul_sum, hstarSum z]
            · simp [hA]
  have hIsGroup_of_inc (q : Site n δ) (hq : q ∈ incGroups a) : IsGroup δ q := by
    change (p10_1kOddGroupRoles (mS_le n δ) q).Nonempty
    obtain ⟨b, hadj, hbq⟩ := (p10_1k_mem_incidentOddGroups (mS_le n δ) a q).mp hq
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbq⟩⟩
  have hvalidCenter (h : History n N δ) (hv : valid M t h) :
      ∃ c, centerOf M t h a = some c ∧ gate M t h a c := by
    have hnpos : 0 < n := by omega
    let j : Fin n := ⟨0, by omega⟩
    let b : OddRole n := p10_1kFlipOddRole a j
    have hadj : (cube n).Adj a.1 b.1 := p10_1kFlipOddRole_adjacent a j
    let q : Site n δ := groupOf δ b
    have hqmem : q ∈ incGroups a := by
      change p10_1kProjectedVertex (mS_le n δ) b.1 ∈
        p10_1kIncidentOddGroups (mS_le n δ) a
      exact (p10_1k_mem_incidentOddGroups (mS_le n δ) a _).2 ⟨b, hadj, rfl⟩
    have hqgroup : IsGroup δ q := by
      change (p10_1kOddGroupRoles (mS_le n δ) q).Nonempty
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    have hgv := hv q hqgroup
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
    rcases hgv with ⟨hpos, hlegal, hselected, hlist, hpass, htilt⟩
    have hsome : (selected M t h s).isSome := hselected s hsInc
    obtain ⟨loc, hsel⟩ := Option.isSome_iff_exists.mp hsome
    let c : ID n δ := (s.1, loc)
    have hcenter : centerOf M t h a = some c := by
      simp [centerOf, c, s, hsel]
    have hgate : gate M t h a c := by
      refine ⟨hcenter, ?_, ?_⟩
      · intro j
        exact hpos s hsInc j
      · intro q' hq'
        exact hv q' (hIsGroup_of_inc q' hq')
    exact ⟨c, hcenter, hgate⟩
  have hfailureLow (h : History n N δ) (c : ID n δ) (ω : OddRole n → Fin N)
      (hg : gate M t h a c) (hnpred : ¬ predictive M t a h ω) :
      predMass M t h a c ω = 0 ∨
        predMass M t h a c ω < ε * refQ M t h a c ω := by
    by_cases hz : predMass M t h a c ω = 0
    · exact Or.inl hz
    · have hmassNN : 0 ≤ predMass M t h a c ω := by
        unfold predMass HypercubeRamsey.FinProb.expect
        apply Finset.sum_nonneg
        intro w hw
        exact mul_nonneg (tuplePrior M t c).nonneg w (hsubLik_nonneg h c w ω)
      have hmass : 0 < predMass M t h a c ω := lt_of_le_of_ne hmassNN (Ne.symm hz)
      by_cases hpass : ε * refQ M t h a c ω ≤ predMass M t h a c ω
      · have hlight := hlightPos h c ω hmass hpass
        have hpred : predOK M t h a c ω := by
          refine ⟨hg, hmass, ?_, hlight⟩
          simpa [ε, a0, k, aG] using hpass
        exact (hnpred ⟨c, hg.1, hpred⟩).elim
      · exact Or.inr (lt_of_not_ge hpass)
  let perCandidate (h : History n N δ) (c : ID n δ) : ℝ :=
    ∑ C : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w C *
      (FinProb.pi (fun b : OddRole n => labLaw M t h b (C (groupOf δ b))).pr
        (fun ω => gate M t h a c ∧ lowStar h c (restrictStar ω)))
  have hsetTupleSelf (h : History n N δ) (c : ID n δ) :
      History.setTuple h c (History.tup h c) = h := by
    simp [History.setTuple, History.pos, History.tup, History.mask, History.act,
      History.tie, Function.update_eq_self]
  have hperCandidateEq (h : History n N δ) (c : ID n δ) :
      perCandidate h c =
        ∑ z : StarData, subLik M t h a c (History.tup h c) (liftStar z) *
          (if lowStar h c z then 1 else 0) := by
    classical
    by_cases hg : gate M t h a c
    · have hstar := hstarMarginal h (lowStar h c)
      have hsub (z : StarData) :
          subLik M t h a c (History.tup h c) (liftStar z) =
            starLik M t h a (liftStar z) := by
        simp [subLik, hsetTupleSelf h c, hg]
      calc
        perCandidate h c =
            ∑ C : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w C *
              (FinProb.pi (fun b : OddRole n => labLaw M t h b (C (groupOf δ b))).pr
                (fun ω => lowStar h c (restrictStar ω))) := by
          simp [perCandidate, hg]
        _ = ∑ z : StarData, starLik M t h a (liftStar z) *
              (if lowStar h c z then 1 else 0) := hstar
        _ = ∑ z : StarData, subLik M t h a c (History.tup h c) (liftStar z) *
              (if lowStar h c z then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [hsub z]
    · unfold perCandidate
      simp [hg, subLik, hsetTupleSelf h c]
  let PositionLaw : FinProb (ID n δ → Bool) :=
    p10_1kGlobalPositionLaw n (mS n δ) δ
  let TupleKernel : ID n δ → FinProb (Fin k → Fin N) := fun c => tuplePrior M t c
  let TupleLaw : FinProb (ID n δ → Fin k → Fin N) := FinProb.pi TupleKernel
  let MaskLaw : FinProb (Site n δ → Finset (Fin N)) := FinProb.pi (fun q => σ t q)
  let ActivationLaw : FinProb (ID n δ → Bool) :=
    p10_1kGlobalActivationLaw n (mS n δ) δ
  let TieLaw : FinProb (ID n δ → (hp n δ).TiePerm) :=
    p10_1kGlobalTieLaw n (mS n δ) δ
  let RestIndex (c : ID n δ) := {id : ID n δ // id ≠ c}
  let RestTuple (c : ID n δ) := RestIndex c → (Fin k → Fin N)
  let RestLaw (c : ID n δ) : FinProb (RestTuple c) :=
    FinProb.pi (fun id : RestIndex c => TupleKernel id.1)
  let restoreTuple (c : ID n δ) (r : RestTuple c) (w : Fin k → Fin N) :
      ID n δ → Fin k → Fin N := fun id => if hi : id = c then w else r ⟨id, hi⟩
  let composeHistory (c : ID n δ) (pos : ID n δ → Bool) (r : RestTuple c)
      (mask : Site n δ → Finset (Fin N)) (act : ID n δ → Bool)
      (tie : ID n δ → (hp n δ).TiePerm) (w : Fin k → Fin N) : History n N δ :=
    ((((pos, restoreTuple c r w), mask), act), tie)
  have hTupleLaw : p10_1kGlobalTupleArrayLaw n (mS n δ) δ
      (fun z => M.μ (t z)) = TupleLaw := by rfl
  have hTupleSplit (c : ID n δ) (g : (ID n δ → Fin k → Fin N) → ℝ) :
      TupleLaw.expect g =
        (RestLaw c).expect (fun r =>
          (tuplePrior M t c).expect (fun w => g (restoreTuple c r w))) := by
    simpa [TupleLaw, RestLaw, TupleKernel, restoreTuple] using
      Lane_q_s10_d7.pi_expect_split_at_q_s10_d7 TupleKernel c g
  have hHistoryExpect (F : History n N δ → ℝ) :
      (historyLaw M σ t).expect F =
        PositionLaw.expect (fun pos => TupleLaw.expect (fun W =>
          MaskLaw.expect (fun mask => ActivationLaw.expect (fun act =>
            TieLaw.expect (fun tie => F ((((pos, W), mask), act), tie)))))) := by
    unfold historyLaw
    rw [hTupleLaw]
    simp only [Lane_q_s10_d7.finprob_prod_expect_q_s10_d7]
  have hMoveTuple (c : ID n δ)
      (g : (Fin k → Fin N) → (Site n δ → Finset (Fin N)) →
        (ID n δ → Bool) → (ID n δ → (hp n δ).TiePerm) → ℝ) :
      (tuplePrior M t c).expect (fun w => MaskLaw.expect (fun mask =>
        ActivationLaw.expect (fun act => TieLaw.expect (fun tie => g w mask act tie)))) =
        MaskLaw.expect (fun mask => ActivationLaw.expect (fun act => TieLaw.expect
          (fun tie => (tuplePrior M t c).expect (fun w => g w mask act tie)))) := by
    calc
      _ = MaskLaw.expect (fun mask => (tuplePrior M t c).expect (fun w =>
            ActivationLaw.expect (fun act => TieLaw.expect (fun tie => g w mask act tie)))) := by
          exact Lane_q_s10_d7.finprob_expect_swap_q_s10_d7 (tuplePrior M t c) MaskLaw
            (fun w mask => ActivationLaw.expect (fun act => TieLaw.expect (fun tie => g w mask act tie)))
      _ = MaskLaw.expect (fun mask => ActivationLaw.expect (fun act =>
            (tuplePrior M t c).expect (fun w => TieLaw.expect (fun tie => g w mask act tie)))) := by
          apply Lane_q_s10_d7.finprob_expect_congr_q_s10_d7 MaskLaw
          intro mask
          exact Lane_q_s10_d7.finprob_expect_swap_q_s10_d7 (tuplePrior M t c) ActivationLaw
            (fun w act => TieLaw.expect (fun tie => g w mask act tie))
      _ = MaskLaw.expect (fun mask => ActivationLaw.expect (fun act => TieLaw.expect
            (fun tie => (tuplePrior M t c).expect (fun w => g w mask act tie)))) := by
          apply Lane_q_s10_d7.finprob_expect_congr_q_s10_d7 MaskLaw
          intro mask
          apply Lane_q_s10_d7.finprob_expect_congr_q_s10_d7 ActivationLaw
          intro act
          exact Lane_q_s10_d7.finprob_expect_swap_q_s10_d7 (tuplePrior M t c) TieLaw
            (fun w tie => g w mask act tie)
  have hHistorySplit (c : ID n δ) (F : History n N δ → ℝ) :
      (historyLaw M σ t).expect F =
        PositionLaw.expect (fun pos => (RestLaw c).expect (fun r =>
          MaskLaw.expect (fun mask => ActivationLaw.expect (fun act => TieLaw.expect
            (fun tie => (tuplePrior M t c).expect (fun w =>
              F (composeHistory c pos r mask act tie w))))))) := by
    rw [hHistoryExpect]
    apply Lane_q_s10_d7.finprob_expect_congr_q_s10_d7 PositionLaw
    intro pos
    calc
      TupleLaw.expect (fun W => MaskLaw.expect (fun mask => ActivationLaw.expect
          (fun act => TieLaw.expect (fun tie => F ((((pos, W), mask), act), tie))))) =
        (RestLaw c).expect (fun r => (tuplePrior M t c).expect (fun w =>
          MaskLaw.expect (fun mask => ActivationLaw.expect (fun act => TieLaw.expect
            (fun tie => F (composeHistory c pos r mask act tie w)))))) := by
          exact hTupleSplit c (fun W => MaskLaw.expect (fun mask => ActivationLaw.expect
            (fun act => TieLaw.expect (fun tie => F ((((pos, W), mask), act), tie)))))
      _ = (RestLaw c).expect (fun r => MaskLaw.expect (fun mask => ActivationLaw.expect
          (fun act => TieLaw.expect (fun tie => (tuplePrior M t c).expect (fun w =>
            F (composeHistory c pos r mask act tie w)))))) := by
          apply Lane_q_s10_d7.finprob_expect_congr_q_s10_d7 (RestLaw c)
          intro r
          exact hMoveTuple c (fun w mask act tie => F (composeHistory c pos r mask act tie w))
  let defaultTuple : Fin k → Fin N := fun _ => defaultLabel
  have hrestoreUpdate (c : ID n δ) (r : RestTuple c) (w : Fin k → Fin N) :
      restoreTuple c r w = Function.update (restoreTuple c r defaultTuple) c w := by
    funext id
    by_cases hid : id = c <;> simp [restoreTuple, hid, defaultTuple]
  have hcomposeSet (c : ID n δ) (pos : ID n δ → Bool) (r : RestTuple c)
      (mask : Site n δ → Finset (Fin N)) (act : ID n δ → Bool)
      (tie : ID n δ → (hp n δ).TiePerm) (w : Fin k → Fin N) :
      composeHistory c pos r mask act tie w =
        History.setTuple (composeHistory c pos r mask act tie defaultTuple) c w := by
    simp [composeHistory, History.setTuple, History.tup, hrestoreUpdate]
  have hperCandidateBase (c : ID n δ) (pos : ID n δ → Bool) (r : RestTuple c)
      (mask : Site n δ → Finset (Fin N)) (act : ID n δ → Bool)
      (tie : ID n δ → (hp n δ).TiePerm) (w : Fin k → Fin N) :
      perCandidate (composeHistory c pos r mask act tie w) c =
        ∑ z : StarData,
          subLik M t (composeHistory c pos r mask act tie defaultTuple)
            a c w (liftStar z) *
              (if lowStar (composeHistory c pos r mask act tie defaultTuple) c z
                then 1 else 0) := by
    let hcur := composeHistory c pos r mask act tie w
    let hbase := composeHistory c pos r mask act tie defaultTuple
    have htup : History.tup hcur c = w := by
      simp [hcur, composeHistory, History.tup, restoreTuple]
    have hcurEq : hcur = History.setTuple hbase c w := by
      simpa [hcur, hbase] using hcomposeSet c pos r mask act tie w
    rw [hperCandidateEq hcur c]
    rw [htup, hcurEq]
    have htupSet : History.tup (History.setTuple hbase c w) c = w := by
      simp [History.tup, History.setTuple]
    rw [htupSet]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hsubLikTupleInvariant hbase c w w (liftStar z),
      hlowTupleInvariant hbase c w z]
  have htupleCandidateBound (c : ID n δ) (pos : ID n δ → Bool)
      (r : RestTuple c) (mask : Site n δ → Finset (Fin N))
      (act : ID n δ → Bool) (tie : ID n δ → (hp n δ).TiePerm) :
      (tuplePrior M t c).expect (fun w =>
        perCandidate (composeHistory c pos r mask act tie w) c) ≤ ε := by
    let hbase := composeHistory c pos r mask act tie defaultTuple
    have hsumEq : (tuplePrior M t c).expect (fun w =>
        perCandidate (composeHistory c pos r mask act tie w) c) =
        ∑ z : StarData,
          (if lowStar hbase c z then 1 else 0) *
            predMass M t hbase a c (liftStar z) := by
      unfold HypercubeRamsey.FinProb.expect
      simp_rw [hperCandidateBase]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hlow : lowStar hbase c z
      · simp [hbase, hlow, predMass, HypercubeRamsey.FinProb.expect]
      · simp [hbase, hlow, predMass, HypercubeRamsey.FinProb.expect]
    calc
      (tuplePrior M t c).expect (fun w =>
          perCandidate (composeHistory c pos r mask act tie w) c) =
        ∑ z : StarData,
          (if lowStar hbase c z then 1 else 0) *
            predMass M t hbase a c (liftStar z) := hsumEq
      _ = ∑ z : StarData,
          (if lowStar hbase c z then
            predMass M t hbase a c (liftStar z) else 0) := by
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hlow : lowStar hbase c z <;> simp [hlow, mul_comm]
      _ ≤ ε := by simpa [lowStar] using hlowBound hbase c
  have expectBound {β : Type*} [Fintype β] (P : FinProb β) (f : β → ℝ)
      (hf : ∀ x, f x ≤ ε) : P.expect f ≤ ε := by
    calc
      P.expect f ≤ P.expect (fun _ => ε) :=
        FinProb.expect_mono P (fun x => hf x)
      _ = ε := FinProb.expect_const P ε
  have hperCandidateBound (c : ID n δ) :
      (historyLaw M σ t).expect (fun h => perCandidate h c) ≤ ε := by
    rw [hHistorySplit c (fun h => perCandidate h c)]
    apply expectBound PositionLaw
    intro pos
    apply expectBound (RestLaw c)
    intro r
    apply expectBound MaskLaw
    intro mask
    apply expectBound ActivationLaw
    intro act
    apply expectBound TieLaw
    intro tie
    exact htupleCandidateBound c pos r mask act tie
  have hfailCandidates (h : History n N δ) (hv : valid M t h)
      (ω : OddRole n → Fin N) (hnpred : ¬ predictive M t a h ω) :
      ∃ c : ID n δ, gate M t h a c ∧ lowStar h c (restrictStar ω) := by
    obtain ⟨c, hcenter, hgate⟩ := hvalidCenter h hv
    have hlow := hfailureLow h c ω hgate hnpred
    have hlowStar : lowStar h c (restrictStar ω) := by
      simpa [lowStar, hpredMassLift h c ω, hrefQLift h c ω] using hlow
    exact ⟨c, hgate, hlowStar⟩
  have hprobUnion (P : FinProb (OddRole n → Fin N)) (h : History n N δ)
      (hv : valid M t h) :
      P.pr (fun ω => ¬ predictive M t a h ω) ≤
        ∑ c : ID n δ, P.pr (fun ω => gate M t h a c ∧ lowStar h c (restrictStar ω)) := by
    classical
    have hcount (ω : OddRole n → Fin N) :
        (if ¬ predictive M t a h ω then (1 : ℝ) else 0) ≤
          ∑ c : ID n δ, if gate M t h a c ∧ lowStar h c (restrictStar ω) then 1 else 0 := by
      by_cases hbad : ¬ predictive M t a h ω
      · obtain ⟨c, hc⟩ := hfailCandidates h hv ω hbad
        have hsingle :
            (if gate M t h a c ∧ lowStar h c (restrictStar ω) then (1 : ℝ) else 0) ≤
              ∑ c : ID n δ,
                if gate M t h a c ∧ lowStar h c (restrictStar ω) then 1 else 0 :=
          Finset.single_le_sum
            (fun c' hc' => by split_ifs <;> norm_num)
            (Finset.mem_univ c)
        simp [hbad, hc] at hsingle ⊢
        exact hsingle
      · simp [hbad]
        apply Finset.sum_nonneg
        intro c hc
        split_ifs <;> norm_num
    unfold HypercubeRamsey.FinProb.pr
    calc
      (∑ ω, if ¬ predictive M t a h ω then P.w ω else 0) ≤
          ∑ ω, P.w ω *
            ∑ c : ID n δ,
              if gate M t h a c ∧ lowStar h c (restrictStar ω) then 1 else 0 := by
        apply Finset.sum_le_sum
        intro ω hω
        by_cases hbad : ¬ predictive M t a h ω
        · simp [hbad]
          exact mul_le_mul_of_nonneg_left (hcount ω) (P.nonneg ω)
        · simp [hbad]
          apply mul_nonneg (P.nonneg ω)
          apply Finset.sum_nonneg
          intro c hc
          split_ifs <;> norm_num
      _ = ∑ c : ID n δ, P.pr (fun ω =>
            gate M t h a c ∧ lowStar h c (restrictStar ω)) := by
        rw [Finset.mul_sum, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c hc
        simp [HypercubeRamsey.FinProb.pr, mul_comm]
  have hperNonneg (h : History n N δ) (c : ID n δ) : 0 ≤ perCandidate h c := by
    unfold perCandidate
    apply Finset.sum_nonneg
    intro C hC
    exact mul_nonneg ((FinProb.pi (clusterLaw M t h)).nonneg C)
      (pr_nonneg' _ _)
  have hperHistory (h : History n N δ) :
      (if valid M t h then
          ∑ C : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w C *
            (FinProb.pi (fun b => labLaw M t h b (C (groupOf δ b))).pr
              (fun ω => ¬ predictive M t a h ω))
        else 0) ≤ ∑ c : ID n δ, perCandidate h c := by
    by_cases hv : valid M t h
    · simp [hv]
      have hP (C : Site n δ → ClIdx M) :=
        hprobUnion (FinProb.pi (fun b => labLaw M t h b (C (groupOf δ b)))) h hv
      calc
        ∑ C : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w C *
            (FinProb.pi (fun b => labLaw M t h b (C (groupOf δ b))).pr
              (fun ω => ¬ predictive M t a h ω)) ≤
          ∑ C : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w C *
            ∑ c : ID n δ,
              (FinProb.pi (fun b => labLaw M t h b (C (groupOf δ b))).pr
                (fun ω => gate M t h a c ∧ lowStar h c (restrictStar ω))) := by
          apply Finset.sum_le_sum
          intro C hC
          exact mul_le_mul_of_nonneg_left (hP C)
            ((FinProb.pi (clusterLaw M t h)).nonneg C)
        _ = ∑ c : ID n δ,
            ∑ C : Site n δ → ClIdx M, (FinProb.pi (clusterLaw M t h)).w C *
              (FinProb.pi (fun b => labLaw M t h b (C (groupOf δ b))).pr
                (fun ω => gate M t h a c ∧ lowStar h c (restrictStar ω)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro C hC
          ring
        _ = ∑ c : ID n δ, perCandidate h c := by
          apply Finset.sum_congr rfl
          intro c hc
          rfl
    · simp [hv]
      apply Finset.sum_nonneg
      intro c hc
      exact hperNonneg h c
  have hrefFailCandidates :
      refFail M t σ a ≤ ∑ c : ID n δ,
        (historyLaw M σ t).expect (fun h => perCandidate h c) := by
    unfold refFail
    calc
      ∑ h, (historyLaw M σ t).w h *
          (if valid M t h then ∑ C : Site n δ → ClIdx M,
            (FinProb.pi (clusterLaw M t h)).w C *
              (FinProb.pi (fun b => labLaw M t h b (C (groupOf δ b))).pr
                (fun ω => ¬ predictive M t a h ω))
          else 0) ≤
        ∑ h, (historyLaw M σ t).w h * ∑ c : ID n δ, perCandidate h c := by
          apply Finset.sum_le_sum
          intro h hh
          exact mul_le_mul_of_nonneg_left (hperHistory h)
            ((historyLaw M σ t).nonneg h)
      _ = ∑ c : ID n δ,
          ∑ h, (historyLaw M σ t).w h * perCandidate h c := by
          rw [Finset.mul_sum, Finset.sum_comm]
      _ = ∑ c : ID n δ,
          (historyLaw M σ t).expect (fun h => perCandidate h c) := by
          apply Finset.sum_congr rfl
          intro c hc
          rfl
  have htotalFail : refFail M t σ a ≤ (Fintype.card (ID n δ) : ℝ) * ε := by
    calc
      refFail M t σ a ≤ ∑ c : ID n δ,
          (historyLaw M σ t).expect (fun h => perCandidate h c) := hRefFailCandidates
      _ ≤ ∑ _c : ID n δ, ε := by
          apply Finset.sum_le_sum
          intro c hc
          exact hperCandidateBound c
      _ = (Fintype.card (ID n δ) : ℝ) * ε := by simp
  have hcardReal : (Fintype.card (ID n δ) : ℝ) ≤ (2 : ℝ) ^ (2 * n) := by
    exact_mod_cast hIDsmall
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_two_lt_d9
    linarith
  have hpow2exp : (2 : ℝ) ^ (2 * n) ≤ Real.exp (2 * (n : ℝ)) := by
    have hpow : (2 : ℝ) ^ (2 * n) =
        Real.exp ((2 * (n : ℝ)) * Real.log 2) := by
      calc
        (2 : ℝ) ^ (2 * n) = Real.exp (Real.log ((2 : ℝ) ^ (2 * n))) := by
          rw [Real.exp_log (by positivity)]
        _ = Real.exp ((2 * (n : ℝ)) * Real.log 2) := by rw [Real.log_pow]; ring_nf
    rw [hpow]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hlog2le (by positivity))
  have hakBig : 10000 < a0 * (k : ℝ) := by
    simpa [a0, k, aG] using hsc.2.2.2.2
  have hfinal : (Fintype.card (ID n δ) : ℝ) * ε ≤
      Real.exp (-(1 / 200 : ℝ) * a0 * (k : ℝ) * n) := by
    calc
      (Fintype.card (ID n δ) : ℝ) * ε ≤
          Real.exp (2 * (n : ℝ)) * ε :=
        mul_le_mul_of_nonneg_right (le_trans hcardReal hpow2exp) (Real.exp_nonneg _)
      _ = Real.exp (2 * (n : ℝ) -
          (1 / 100 : ℝ) * a0 * (k : ℝ) * n) := by
        rw [show ε = Real.exp (-(1 / 100 : ℝ) * a0 * (k : ℝ) * n) by rfl,
          ← Real.exp_add]
        congr 1 <;> ring
      _ ≤ Real.exp (-(1 / 200 : ℝ) * a0 * (k : ℝ) * n) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hakBig, show 0 ≤ (n : ℝ) by positivity]
  exact htotalFail.trans hfinal

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
    have hcontr : 200 < a0 * (k : ℝ) := by simpa [k, a0, aG] using hsc.2.2.2.1
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
    simpa [a0, k, aG] using hsc.2.2.2.1
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
