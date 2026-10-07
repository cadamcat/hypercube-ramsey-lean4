import HypercubeRamsey.S03.Height.Selection_p_height_main

set_option maxHeartbeats 400000

namespace HypercubeRamsey.Lane_sol_hs_paths

open OAI.HypercubeRamsey Lane_p_height_main

/-- A finite path before imposing a stopping radius. -/
inductive Path {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) : HDState p → HDState p → Type
  | nil {s} : Path Sites P A E s s
  | cons {s t f} (step : HDScaleStep Sites P A E s t)
      (tail : Path Sites P A E t f) : Path Sites P A E s f

namespace Path

noncomputable def append {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool} {E : p.EligMap}
    {s t f : HDState p} (a : Path Sites P A E s t) (b : Path Sites P A E t f) :
    Path Sites P A E s f := by
  induction a with
  | nil => exact b
  | cons step tail ih => exact .cons step (ih b)

end Path

theorem reach_mem {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool}
    {E : p.EligMap} {vq v : CubeVertex p.d} {R j : ℕ}
    (h : p.Reach Sites P A E vq R v j) :
    v ∈ Sites ∧ _root_.hammingDist v vq ≤ R := by
  induction h with
  | start v hv hq => exact ⟨hv, hq⟩
  | up v j hj h hbad ih => exact ih
  | down v v' j h hv' hq hstep ih => exact ⟨hv', hq⟩

/-- Reachability has a finite path with all its sites in any domain containing
its consultation ball. -/
theorem reach_path {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool}
    {E : p.EligMap} {vq v : CubeVertex p.d} {R j : ℕ}
    (Dom : p.Sites) (hDom : ∀ w ∈ Sites, _root_.hammingDist w vq ≤ R → w ∈ Dom)
    (h : p.Reach Sites P A E vq R v j) :
    ∃ u ∈ Dom, Nonempty (Path Dom P A E (u, 0) (v, j)) := by
  induction h with
  | start v hv hq => exact ⟨v, hDom v hv hq, ⟨.nil⟩⟩
  | up v j hj h hbad ih =>
      obtain ⟨u, hu, ⟨path⟩⟩ := ih
      have hv := reach_mem h
      exact ⟨u, hu, ⟨path.append (.cons (.up (hDom v hv.1 hv.2) hj hbad) .nil)⟩⟩
  | down v v' j h hv' hq hstep ih =>
      obtain ⟨u, hu, ⟨path⟩⟩ := ih
      have hj : j < p.H := by
        have := reach_level_le Sites P A E vq R h
        omega
      exact ⟨u, hu, ⟨path.append (.cons (.down hj (hDom v' hv' hq) hstep) .nil)⟩⟩

/-- Cut a finite path at its first exit from a metric ball. -/
theorem path_cut {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool}
    {E : p.EligMap} (origin : HDState p) (R : ℕ) {s f : HDState p}
    (path : Path Sites P A E s f) (hout : R ≤ hdScaleDistance p.D origin f) :
    ∃ m, Nonempty (HDScaleWalk Sites P A E origin R s m) := by
  induction path with
  | nil => exact ⟨_, ⟨.stop hout⟩⟩
  | @cons s t f step tail ih =>
      by_cases hs : R ≤ hdScaleDistance p.D origin s
      · exact ⟨s, ⟨.stop hs⟩⟩
      · have hins : hdScaleDistance p.D origin s < R := by omega
        obtain ⟨m, ⟨walk⟩⟩ := ih hout
        cases step with
        | up hv hj hbad => exact ⟨m, ⟨.up hins hv hj hbad walk⟩⟩
        | down hj hv' hstep => exact ⟨m, ⟨.down hins hv' hj hstep walk⟩⟩

/-- Any exit by a path starting at level zero has nonnegative net rise. -/
theorem failure_of_path {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool}
    {E : p.EligMap} {u : CubeVertex p.d} {f : HDState p} {R : ℕ} {η : ℝ}
    (path : Path Sites P A E (u, 0) f) (hη : 0 ≤ η)
    (hout : R ≤ hdScaleDistance p.D (u, 0) f) :
    hdScaleFailure Sites P A E (u, 0) R η := by
  obtain ⟨m, hm⟩ := path_cut (u, 0) R path hout
  refine ⟨m, hm, ?_⟩
  simp only [Nat.cast_zero, sub_zero]
  have : 0 ≤ η * (R : ℝ) := mul_nonneg hη (Nat.cast_nonneg _)
  linarith [Nat.cast_nonneg (α := ℝ) m.2]

theorem path_first_bad {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool}
    {E : p.EligMap} {u v : CubeVertex p.d} {j : ℕ}
    (path : Path Sites P A E (u, 0) (v, j)) (hj : 0 < j) :
    0 < p.H ∧ p.BadN P A E u 0 := by
  cases path with
  | nil => omega
  | cons step tail =>
      cases step with
      | up hv hH hbad => exact ⟨hH, hbad⟩

/-- A bad site at level zero immediately gives a radius-one failure. -/
theorem failure_one_of_bad {p : HDParams} (hD : 0 < p.D) {Sites : p.Sites}
    {P A : p.Loc → Bool} {E : p.EligMap} {u : CubeVertex p.d}
    (hu : u ∈ Sites) (hH : 0 < p.H) (hbad : p.BadN P A E u 0) :
    hdScaleFailure Sites P A E (u, 0) 1 (1 / 2) := by
  refine ⟨(u, 1), ⟨.up ?_ hu hH hbad (.stop ?_)⟩, ?_⟩
  · rw [hdScaleDistance_self _ hD]
    omega
  · unfold hdScaleDistance
    norm_num [Nat.dist]
  · norm_num

theorem zero_distance_le_finish {p : HDParams} (u v : CubeVertex p.d) (j : ℕ) :
    hdScaleDistance p.D (v, 0) (u, 0) ≤ hdScaleDistance p.D (u, 0) (v, j) := by
  simp only [hdScaleDistance, Nat.dist_self, zero_max, _root_.hammingDist_comm]
  exact Nat.le_max_right _ _

theorem scale_bracket (n : ℕ) (σ : ℝ) (h L : ℕ)
    (hbase : heightBaseRadius n ≤ L) (htop : L < hdScaleRadius n σ h) :
    ∃ i < h, hdScaleRadius n σ i ≤ L ∧ L < hdScaleRadius n σ (i + 1) := by
  induction h with
  | zero =>
      have htop' : L < heightBaseRadius n := by simpa [hdScaleRadius] using htop
      omega
  | succ h ih =>
      by_cases hprev : L < hdScaleRadius n σ h
      · obtain ⟨i, hi, hlo, hhi⟩ := ih hprev
        exact ⟨i, by omega, hlo, hhi⟩
      · exact ⟨h, by omega, by omega, htop⟩

/-- Without a level-zero failure, every finite path stays below the stopping radius. -/
theorem path_bound {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool}
    {E : p.EligMap} {η : ℝ} (hη : 0 ≤ η)
    (hno : ∀ u ∈ Sites, ¬ hdScaleFailure Sites P A E (u, 0) p.H η)
    {u : CubeVertex p.d} (hu : u ∈ Sites) {f : HDState p}
    (path : Path Sites P A E (u, 0) f) : hdScaleDistance p.D (u, 0) f < p.H := by
  by_contra hout
  exact hno u hu (failure_of_path path hη (by omega))

/-- Convert a finite path into reachability when every possible prefix endpoint
is in the consultation ball. -/
theorem path_reach {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool}
    {E : p.EligMap} (vq : CubeVertex p.d) (R : ℕ) {s f : HDState p}
    (path : Path Sites P A E s f)
    (hstart : p.Reach Sites P A E vq R s.1 s.2)
    (hnear : ∀ t, Nonempty (Path Sites P A E s t) → _root_.hammingDist t.1 vq ≤ R) :
    p.Reach Sites P A E vq R f.1 f.2 := by
  revert hstart hnear
  induction path with
  | nil => intro hstart hnear; exact hstart
  | @cons s t f step tail ih =>
      intro hstart hnear
      have hnext : p.Reach Sites P A E vq R t.1 t.2 := by
        cases step with
        | up hv hj hbad => exact HDParams.Reach.up _ _ hj hstart hbad
        | down hj hv' hstep =>
            exact HDParams.Reach.down _ _ _ hstart hv'
              (hnear _ ⟨.cons (.down hj hv' hstep) .nil⟩) hstep
      apply ih hnext
      intro g hg
      obtain ⟨pg⟩ := hg
      exact hnear g ⟨.cons step pg⟩

/-- Top-scale success lets any path be viewed from its endpoint's long ball. -/
theorem path_query_reach {p : HDParams} (hD : 0 < p.D) {Sites : p.Sites}
    {P A : p.Loc → Bool} {E : p.EligMap} {η : ℝ} (hη : 0 ≤ η)
    (hno : ∀ u ∈ Sites, ¬ hdScaleFailure Sites P A E (u, 0) p.H η)
    {u v : CubeVertex p.d} (hu : u ∈ Sites) {j : ℕ}
    (path : Path Sites P A E (u, 0) (v, j)) :
    p.Reach Sites P A E v p.Rlong v j := by
  have hvdist := hdScaleDistance_hamming_bound hD (path_bound hη hno hu path)
  have hnear : ∀ t, Nonempty (Path Sites P A E (u, 0) t) →
      _root_.hammingDist t.1 v ≤ p.Rlong := by
    intro t ht
    obtain ⟨pt⟩ := ht
    have htdist := hdScaleDistance_hamming_bound hD (path_bound hη hno hu pt)
    calc
      _root_.hammingDist t.1 v ≤ _root_.hammingDist t.1 u +
          _root_.hammingDist u v := _root_.hammingDist_triangle _ _ _
      _ = _root_.hammingDist u t.1 + _root_.hammingDist u v := by
          rw [_root_.hammingDist_comm t.1 u]
      _ ≤ p.D * p.H + p.D * p.H := Nat.add_le_add htdist hvdist
      _ = p.Rlong := by unfold HDParams.Rlong; ring
  exact path_reach v p.Rlong path (HDParams.Reach.start u hu (hnear _ ⟨.nil⟩)) hnear

theorem height_lt_of_no_failure {p : HDParams} {Sites : p.Sites}
    {P A : p.Loc → Bool} {E : p.EligMap} {η : ℝ} (hη : 0 ≤ η)
    (hno : ∀ u ∈ Sites, ¬ hdScaleFailure Sites P A E (u, 0) p.H η)
    (v : CubeVertex p.d) (hv : v ∈ Sites) : p.height Sites P A E p.Rlong v < p.H := by
  have hr := height_reach_at_height Sites P A E v p.Rlong hv
  obtain ⟨u, hu, ⟨path⟩⟩ := reach_path Sites (fun _ hw _ => hw) hr
  have hb := path_bound hη hno hu path
  have hlevel : p.height Sites P A E p.Rlong v ≤
      hdScaleDistance p.D (u, 0) (v, p.height Sites P A E p.Rlong v) := by
    unfold hdScaleDistance
    rw [show Nat.dist 0 (p.height Sites P A E p.Rlong v) =
      p.height Sites P A E p.Rlong v by unfold Nat.dist; omega]
    exact Nat.le_max_left _ _
  exact hlevel.trans_lt hb

theorem height_le_neighbor_add_one {p : HDParams} (hD : 0 < p.D) {Sites : p.Sites}
    {P A : p.Loc → Bool} {E : p.EligMap} {η : ℝ} (hη : 0 ≤ η)
    (hno : ∀ u ∈ Sites, ¬ hdScaleFailure Sites P A E (u, 0) p.H η)
    (v v' : CubeVertex p.d) (hv : v ∈ Sites) (hv' : v' ∈ Sites)
    (hdist : _root_.hammingDist v v' ≤ p.D) :
    p.height Sites P A E p.Rlong v ≤ p.height Sites P A E p.Rlong v' + 1 := by
  let j := p.height Sites P A E p.Rlong v
  by_cases hj : j = 0
  · simp [j] at hj
    omega
  · have hlow : j < p.H := height_lt_of_no_failure hη hno v hv
    have hr := height_reach_at_height Sites P A E v p.Rlong hv
    obtain ⟨u, hu, ⟨path⟩⟩ := reach_path Sites (fun _ hw _ => hw) hr
    have hj' : (j - 1) + 1 = j := by omega
    have prior : Path Sites P A E (u, 0) (v, (j - 1) + 1) := by
      simpa only [hj'] using path
    have full : Path Sites P A E (u, 0) (v', j - 1) :=
      prior.append (.cons (.down (by omega) hv' hdist) .nil)
    have hr' := path_query_reach hD hη hno hu full
    have hle := height_reach_le Sites P A E v' p.Rlong hr'
    change j ≤ _
    omega

/-- All clauses of the global height property follow from top-scale success. -/
theorem goodHeights_of_no_failure {p : HDParams} (hD : 0 < p.D) {Sites : p.Sites}
    {P A : p.Loc → Bool} {E : p.EligMap} {η : ℝ} (hη : 0 ≤ η)
    (hno : ∀ u ∈ Sites, ¬ hdScaleFailure Sites P A E (u, 0) p.H η) :
    p.GoodHeights Sites P A E := by
  apply goodHeights_of_height_lt Sites P A E
    (height_lt_of_no_failure hη hno)
  intro v hv v' hv' hdist
  have hab := height_le_neighbor_add_one hD hη hno v v' hv hv' hdist
  have hba := height_le_neighbor_add_one hD hη hno v' v hv' hv
    (by simpa only [_root_.hammingDist_comm] using hdist)
  apply abs_le.mpr
  constructor <;> omega

end HypercubeRamsey.Lane_sol_hs_paths
