import HypercubeRamsey.S03.Height.Split_opus_height

set_option maxHeartbeats 400000

namespace HypercubeRamsey.Lane_sol_height_short

open OAI.HypercubeRamsey Lane_p_height_main Lane_opus_height Lane_sol_hs_paths

namespace Path

/-- The states visited by this particular finite path. -/
def states {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool} {E : p.EligMap}
    {s f : HDState p} : Lane_sol_hs_paths.Path Sites P A E s f → Finset (HDState p)
  | .nil => {s}
  | .cons _ tail => insert s (states tail)

theorem start_mem {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool} {E : p.EligMap}
    {s f : HDState p} (path : Lane_sol_hs_paths.Path Sites P A E s f) : s ∈ states path := by
  cases path <;> simp [states]

theorem finish_mem {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool} {E : p.EligMap}
    {s f : HDState p} (path : Lane_sol_hs_paths.Path Sites P A E s f) : f ∈ states path := by
  induction path with
  | nil => simp [states]
  | cons step tail ih => exact Finset.mem_insert_of_mem ih

/-- Every visited state has a prefix of the same path. -/
theorem to_prefix {p : HDParams} {Sites : p.Sites} {P A : p.Loc → Bool} {E : p.EligMap}
    {s f : HDState p} (path : Lane_sol_hs_paths.Path Sites P A E s f) {t : HDState p}
    (ht : t ∈ states path) : Nonempty (Lane_sol_hs_paths.Path Sites P A E s t) := by
  induction path with
  | nil =>
      have : t = _ := Finset.mem_singleton.mp ht
      subst t
      exact ⟨.nil⟩
  | cons step tail ih =>
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨.nil⟩
      · obtain ⟨pt⟩ := ih ht
        exact ⟨.cons step pt⟩

/-- A path whose visited sites fit the query ball gives reachability in that ball. -/
theorem reach_of_states {p : HDParams} {Dom Sites : p.Sites}
    {P A : p.Loc → Bool} {E : p.EligMap} {s f : HDState p}
    (path : Lane_sol_hs_paths.Path Dom P A E s f) (hsub : Dom ⊆ Sites) (v : CubeVertex p.d) (R : ℕ)
    (hstart : p.Reach Sites P A E v R s.1 s.2)
    (hnear : ∀ t ∈ states path, _root_.hammingDist t.1 v ≤ R) :
    p.Reach Sites P A E v R f.1 f.2 := by
  revert hstart hnear
  induction path with
  | nil => intro hstart hnear; exact hstart
  | @cons s t f step tail ih =>
      intro hstart hnear
      have ht : t ∈ states (.cons step tail) :=
        Finset.mem_insert_of_mem (start_mem tail)
      have hnext : p.Reach Sites P A E v R t.1 t.2 := by
        cases step with
        | up hv hj hbad => exact HDParams.Reach.up _ _ hj hstart hbad
        | down hj hv hdist =>
            exact HDParams.Reach.down _ _ _ hstart (hsub hv) (hnear _ ht) hdist
      exact ih hnext (fun t ht => hnear t (Finset.mem_insert_of_mem ht))

end Path

theorem reach_mono_radius {p : HDParams} {Sites : p.Sites}
    {P A : p.Loc → Bool} {E : p.EligMap} {v w : CubeVertex p.d} {R S j : ℕ}
    (hRS : R ≤ S) (hr : p.Reach Sites P A E v R w j) :
    p.Reach Sites P A E v S w j := by
  induction hr with
  | start w hw hnear => exact .start w hw (hnear.trans hRS)
  | up w j hj hr hbad ih => exact .up w j hj ih hbad
  | down w w' j hr hw' hnear hdist ih =>
      exact .down w w' j ih hw' (hnear.trans hRS) hdist

theorem height_mono_radius {p : HDParams} {Sites : p.Sites}
    {P A : p.Loc → Bool} {E : p.EligMap} {v : CubeVertex p.d} (hv : v ∈ Sites)
    {R S : ℕ} (hRS : R ≤ S) :
    p.height Sites P A E R v ≤ p.height Sites P A E S v :=
  height_reach_le Sites P A E v S
    (reach_mono_radius hRS (height_reach_at_height Sites P A E v R hv))

/-- Displacement below `R` puts every visited site within a `2DR` query tube. -/
theorem path_short_reach {p : HDParams} (hD : 0 < p.D) {Sites Dom : p.Sites}
    {P A : p.Loc → Bool} {E : p.EligMap} {u v : CubeVertex p.d} {j R q : ℕ}
    (path : Lane_sol_hs_paths.Path Dom P A E (u, 0) (v, j)) (hu : u ∈ Dom) (hsub : Dom ⊆ Sites)
    (hbound : ∀ t ∈ Path.states path, hdScaleDistance p.D (u, 0) t < R)
    (hRq : 2 * R ≤ q) : p.Reach Sites P A E v (p.D * q) v j := by
  have hvdist := hdScaleDistance_hamming_bound hD
    (hbound _ (Path.finish_mem path))
  have hnear : ∀ t ∈ Path.states path, _root_.hammingDist t.1 v ≤ p.D * q := by
    intro t ht
    have htdist := hdScaleDistance_hamming_bound hD (hbound t ht)
    calc
      _root_.hammingDist t.1 v ≤ _root_.hammingDist t.1 u +
          _root_.hammingDist u v := _root_.hammingDist_triangle _ _ _
      _ = _root_.hammingDist u t.1 + _root_.hammingDist u v := by
        rw [_root_.hammingDist_comm t.1 u]
      _ ≤ p.D * R + p.D * R := Nat.add_le_add htdist hvdist
      _ = p.D * (2 * R) := by ring
      _ ≤ p.D * q := Nat.mul_le_mul_left _ hRq
  exact Path.reach_of_states path hsub v (p.D * q)
    (.start u (hsub hu) (hnear _ (Path.start_mem path))) hnear

/-- A mismatch has a failure at a scale large enough to leave the short tube,
or at the top scale. The failure stays in the long consultation domain. -/
theorem short_height_witness (p : HDParams) (hD : 0 < p.D) (σ ζ : ℝ)
    (_hH : p.H = hdScaleRadius p.n σ (hdScaleIndex p.n σ ζ))
    (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap)
    (v : CubeVertex p.d) (hv : v ∈ Sites) (m : ℕ)
    (hshort : p.Rshort m ≤ p.Rlong)
    (hbase : 2 * heightBaseRadius p.n ≤ Nat.sqrt m)
    (hne : p.height Sites P A E p.Rlong v ≠ p.height Sites P A E (p.Rshort m) v) :
    (∃ i ∈ (Finset.range (hdScaleIndex p.n σ ζ)).filter
        (fun i => Nat.sqrt m < 2 * hdScaleRadius p.n σ (i + 1)),
      ∃ u ∈ midStarts p (p.domBall Sites v p.Rlong) v (hdScaleRadius p.n σ (i + 1)),
        hdScaleFailure (p.domBall Sites v p.Rlong) P A E (u, 0)
          (hdScaleRadius p.n σ i) (hdScaleSlope (hdScaleIndex p.n σ ζ) i)) ∨
    (∃ u ∈ p.domBall Sites v p.Rlong,
      hdScaleFailure (p.domBall Sites v p.Rlong) P A E (u, 0)
        (hdScaleRadius p.n σ (hdScaleIndex p.n σ ζ))
        (hdScaleSlope (hdScaleIndex p.n σ ζ) (hdScaleIndex p.n σ ζ))) := by
  classical
  let Dom := p.domBall Sites v p.Rlong
  have hsub : Dom ⊆ Sites := Finset.filter_subset _ _
  have hr := height_reach_at_height Sites P A E v p.Rlong hv
  obtain ⟨u, hu, ⟨path⟩⟩ := reach_path Dom
    (fun w hw hq => Finset.mem_filter.mpr ⟨hw, hq⟩) hr
  let L := (Path.states path).sup (hdScaleDistance p.D (u, 0))
  have hbound : ∀ t ∈ Path.states path, hdScaleDistance p.D (u, 0) t ≤ L := by
    intro t ht
    exact Finset.le_sup ht
  have hnot : ∀ R, L < R → Nat.sqrt m < 2 * R := by
    intro R hLR
    by_contra hq
    have hrshort := path_short_reach hD path hu hsub
      (fun t ht => (hbound t ht).trans_lt hLR) (by omega : 2 * R ≤ Nat.sqrt m)
    have hle := height_reach_le Sites P A E v (p.Rshort m) hrshort
    have hge := height_mono_radius hv hshort (P := P) (A := A) (E := E)
    exact hne (Nat.le_antisymm hle hge)
  have hLbase : heightBaseRadius p.n ≤ L := by
    by_contra h
    have := hnot (heightBaseRadius p.n) (by omega)
    omega
  obtain ⟨t, ht, hLt⟩ := Finset.exists_mem_eq_sup (Path.states path)
    ⟨(u, 0), Path.start_mem path⟩ (hdScaleDistance p.D (u, 0))
  obtain ⟨initial⟩ := Path.to_prefix path ht
  let h := hdScaleIndex p.n σ ζ
  by_cases htop : hdScaleRadius p.n σ h ≤ L
  · right
    refine ⟨u, hu, failure_of_path initial ?_ ?_⟩
    · have hs := hdScaleThreshold_fractions_bounds (Nat.le_refl h)
      linarith [hs.2.2.2.2.1]
    · exact htop.trans_eq hLt
  · obtain ⟨i, hi, hlo, hhi⟩ := scale_bracket p.n σ h L hLbase (by omega)
    left
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hnot _ hhi⟩,
      u, Finset.mem_filter.mpr ⟨hu, ?_⟩, failure_of_path initial ?_ (hlo.trans_eq hLt)⟩
    · exact (zero_distance_le_finish u v _).trans_lt
        ((hbound _ (Path.finish_mem path)).trans_lt hhi)
    · have hs := hdScaleThreshold_fractions_bounds (Nat.le_of_lt hi)
      linarith [hs.2.2.2.2.1]

end HypercubeRamsey.Lane_sol_height_short
