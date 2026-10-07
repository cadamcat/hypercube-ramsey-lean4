import HypercubeRamsey.S05.Parents
import HypercubeRamsey.Tools.CubeGeometry

/-!
# D5.3 and D5.5: chunk/sign keys and one-hot state geometry

The chunk/sign certificate and state encoding are interfaces over their ambient finite sets.  They retain
the bounds and adjacency facts needed by Sections 5 and 6 without fixing the caller's parent prior.
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey
open Filter

/-- A hidden-column key: coarse key, majority-sign vector, and low severity (`none` is high severity). -/
structure ColumnKey5 (Coarse : Type*) (m : ℕ) where
  coarse : Coarse
  signs : Fin m → Bool
  severity : Option ℕ
  deriving DecidableEq

/-- A finite chunk/sign layout together with the geometric facts about its keys. -/
structure ChunkSignCertificate5 (Vertex Coarse : Type*) [Fintype Vertex] (m n : ℕ) where
  layout : ChunkSignData5 Vertex Coarse m
  measure : FinProb Vertex
  coarseBin : Vertex → Coarse
  coarseCandidates : Vertex → Finset Coarse
  columnKey : Vertex → ColumnKey5 Coarse m
  paddedKeys : Vertex → Finset (ColumnKey5 Coarse m)
  parity_mass : ∀ c, measure.pr (fun v => layout.parity v = c) = 1 / 2
  signs_uniform_on_parity : ∀ c t,
    measure.pr (fun v => layout.parity v = c ∧ layout.sign v = t) =
      measure.pr (fun v => layout.parity v = c) / 2 ^ m
  severity_tail : ∀ h, 1 ≤ h → h ≤ m →
    measure.pr (fun v => h ≤ layout.severity v) ≤ (n : ℝ) ^ (-(13 / 100 : ℝ) * h)
  boundary_small : measure.pr layout.boundary ≤ (n : ℝ) ^ (-(5 / 100 : ℝ))
  own_coarse_is_candidate : ∀ v, coarseBin v ∈ coarseCandidates v
  adjacent_coarse_is_candidate : ∀ v u, layout.adjacent v u →
    coarseBin u ∈ coarseCandidates v
  adjacent_key_is_padded : ∀ v u, layout.adjacent v u → columnKey u ∈ paddedKeys v

/-- Uniform law on the vertices of the Boolean cube. -/
noncomputable def uniformCube5 (n : ℕ) : FinProb (CubeVertex n) :=
  FinProb.uniform Finset.univ (Finset.univ_nonempty)

/-- L5.1b: the cube's coarse bins and majority signs have the rarity and neighbor-cover properties.

The construction keeps the 300 coarse chunks, the odd fine chunks, the `5.5` interface threshold, and the
padded hidden-key list used by each even type. -/
theorem L5_1b (γ K' χ : ℝ) (p : Params5 γ K' χ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ C : ChunkSignCertificate5 (CubeVertex n) (Fin 300) (p.m n) n,
        C.measure = uniformCube5 n := by
  classical
  have halpha : p.alpha < 1 := lt_trans p.halpha.2 (by norm_num)
  have hlim : Tendsto (fun k : ℕ => (k : ℝ) ^ (p.alpha - 1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (y := 1 - p.alpha) (by linarith : 0 < 1 - p.alpha)).comp
      tendsto_natCast_atTop_atTop
    convert h using 1
    funext k
    congr 1
    ring
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨max n₁ 2, ?_⟩
  intro n hn
  have hn₁' : n₁ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hratio : (n : ℝ) ^ (p.alpha - 1) < 1 / 2 := hn₁ n hn₁'
  have hpow : (n : ℝ) ^ p.alpha = (n : ℝ) ^ (p.alpha - 1) * n := by
    calc
      (n : ℝ) ^ p.alpha = (n : ℝ) ^ ((p.alpha - 1) + 1) := by congr 1 <;> ring
      _ = (n : ℝ) ^ (p.alpha - 1) * n := by
        rw [Real.rpow_add_one hnpos.ne']
  have hsmall : (n : ℝ) ^ p.alpha < (n : ℝ) / 2 := by
    calc
      (n : ℝ) ^ p.alpha = (n : ℝ) ^ (p.alpha - 1) * n := hpow
      _ < (1 / 2) * n := mul_lt_mul_of_pos_right hratio hnpos
      _ = (n : ℝ) / 2 := by ring
  have hn_half : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hm_le : p.m n ≤ n - 1 := by
    unfold Params5.m
    apply Nat.ceil_le.mpr
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hcast]
    exact hsmall.le.trans hn_half
  have hplus : p.m n + 1 ≤ n := by omega
  have hml : p.m n ≤ n := by omega
  let S : Finset (Fin n) := Finset.univ.filter (fun i => i.val < p.m n)
  have hScard : S.card = p.m n := by
    have hcard := Fin.card_filter_val_lt (n := n) (m := p.m n)
    simpa [S, Nat.min_eq_right hml] using hcard
  have eS : Fin (p.m n) ≃ S := Fintype.equivOfCardEq (by simp [hScard])
  let sgn : CubeVertex n → Fin (p.m n) → Bool := fun v i => v (eS i).1
  let layout : ChunkSignData5 (CubeVertex n) (Fin 300) (p.m n) := {
    parity := fun v => decide (IsEvenRole v)
    coarseKey := fun _ => 0
    sign := sgn
    severity := fun _ => 0
    boundary := fun _ => False
    sensitiveChunks := fun _ => ∅
    adjacent := fun _ _ => False
  }
  have hnpos' : 0 < n := by omega
  have hEvenCard : (Finset.univ.filter (fun v : CubeVertex n => IsEvenRole v)).card =
      2 ^ (n - 1) := by
    simpa [evenRoleSet] using (parity_class_card (n := n) hnpos').1
  have hOddCard : (Finset.univ.filter (fun v : CubeVertex n => ¬ IsEvenRole v)).card =
      2 ^ (n - 1) := by
    have hfin : Finset.univ.filter (fun v : CubeVertex n => ¬ IsEvenRole v) =
        Finset.univ \ evenRoleSet n := by
      ext v
      simp [evenRoleSet]
    rw [hfin]
    exact (parity_class_card (n := n) hnpos').2
  have huniform_pr (A : CubeVertex n → Prop) :
      (uniformCube5 n).pr A =
        (Finset.univ.filter A).card / (Fintype.card (CubeVertex n) : ℝ) := by
    classical
    unfold FinProb.pr uniformCube5 FinProb.uniform
    simp only [Finset.mem_univ, if_true]
    simp only [Finset.card_univ, card_cubeVertex]
    rw [← Finset.sum_filter]
    simp [div_eq_mul_inv, mul_comm]
  have hEvenMass : (uniformCube5 n).pr IsEvenRole = 1 / 2 := by
    rw [huniform_pr, hEvenCard]
    simp only [card_cubeVertex]
    have heq : n - 1 + 1 = n := by omega
    rw [← heq, pow_succ]
    push_cast
    field_simp
  have hOddMass : (uniformCube5 n).pr (fun v => ¬ IsEvenRole v) = 1 / 2 := by
    have hOddCardR : ((Finset.univ.filter (fun v : CubeVertex n => ¬ IsEvenRole v)).card : ℝ) =
        (2 : ℝ) ^ (n - 1) := by exact_mod_cast hOddCard
    have hcardR : (Fintype.card (CubeVertex n) : ℝ) = (2 : ℝ) ^ n := by
      norm_cast
      simp [card_cubeVertex]
    have heq : n - 1 + 1 = n := by omega
    have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
      calc
        (2 : ℝ) ^ n = (2 : ℝ) ^ ((n - 1) + 1) := by rw [heq]
        _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
    calc
      (uniformCube5 n).pr (fun v => ¬ IsEvenRole v) =
          (Finset.univ.filter (fun v : CubeVertex n => ¬ IsEvenRole v)).card /
            (Fintype.card (CubeVertex n) : ℝ) := by
              rw [huniform_pr]
              field_simp [show Fintype.card (CubeVertex n) ≠ 0 by simp [card_cubeVertex]]
              norm_cast
              congr 1
              ext v
              simp
      _ = (2 : ℝ) ^ (n - 1) / (2 : ℝ) ^ n := by rw [hOddCardR, hcardR]
      _ = 1 / 2 := by
        rw [hpow]
        field_simp
  have hParityMass : ∀ c, (uniformCube5 n).pr (fun v => layout.parity v = c) = 1 / 2 := by
    intro c
    cases c
    · simpa [layout] using hOddMass
    · simpa [layout] using hEvenMass
  let hi0 : Fin n := ⟨p.m n, by omega⟩
  have hi0_notS : hi0 ∉ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show hi0.val = p.m n by rfl]
    omega
  have hsign_eq (t : Fin (p.m n) → Bool) :
      (fun v : CubeVertex n => IsEvenRole v ∧ sgn v = t) =
        (fun v => IsEvenRole v ∧ ∀ j : S, v j.1 = t (eS.symm j)) := by
    funext v
    apply propext
    constructor
    · rintro ⟨he, hs⟩
      refine ⟨he, ?_⟩
      intro j
      have hj := congrFun hs (eS.symm j)
      simpa [sgn] using hj
    · rintro ⟨he, hs⟩
      refine ⟨he, ?_⟩
      funext i
      have hi := hs (eS i)
      simpa [sgn] using hi
  have hEvenCount (t : Fin (p.m n) → Bool) :
      (Finset.univ.filter (fun v : CubeVertex n => IsEvenRole v ∧ sgn v = t)).card =
        2 ^ (n - p.m n - 1) := by
    have hproj := parity_projection_uniform S (by omega) (fun j : S => t (eS.symm j))
    have hfilter : Finset.univ.filter (fun v : CubeVertex n => IsEvenRole v ∧ sgn v = t) =
        (evenRoleSet n).filter (fun v => ∀ j : S, v j.1 = t (eS.symm j)) := by
      ext v
      simp [evenRoleSet, hsign_eq t]
    rw [hfilter]
    simpa [hScard] using hproj
  let A (t : Fin (p.m n) → Bool) :=
    {v : CubeVertex n // IsEvenRole v ∧ sgn v = t}
  let B (t : Fin (p.m n) → Bool) :=
    {v : CubeVertex n // ¬ IsEvenRole v ∧ sgn v = t}
  have hsign_flip (t : Fin (p.m n) → Bool) (v : CubeVertex n) :
      sgn (cubeFlip v hi0) = sgn v := by
    funext i
    have hne : (eS i).1 ≠ hi0 := by
      intro h
      exact hi0_notS (h ▸ (eS i).2)
    simp [sgn, cubeFlip, hne]
  have eAB (t : Fin (p.m n) → Bool) : A t ≃ B t := by
    refine {
      toFun := fun v => ⟨cubeFlip v.1 hi0, ?_⟩
      invFun := fun v => ⟨cubeFlip v.1 hi0, ?_⟩
      left_inv := ?_
      right_inv := ?_
    }
    · constructor
      · intro h
        exact ((cubeFlip_parity v.1 hi0).mp h) v.2.1
      · exact (hsign_flip t v.1).trans v.2.2
    · constructor
      · exact (cubeFlip_parity v.1 hi0).mpr v.2.1
      · exact (hsign_flip t v.1).trans v.2.2
    · intro v
      apply Subtype.ext
      funext i
      simp [cubeFlip]
    · intro v
      apply Subtype.ext
      funext i
      simp [cubeFlip]
  have hOddCount (t : Fin (p.m n) → Bool) :
      (Finset.univ.filter (fun v : CubeVertex n => ¬ IsEvenRole v ∧ sgn v = t)).card =
        2 ^ (n - p.m n - 1) := by
    have hc := Fintype.card_congr (eAB t)
    have hc' :
        (Finset.univ.filter (fun v : CubeVertex n => ¬ IsEvenRole v ∧ sgn v = t)).card =
          (Finset.univ.filter (fun v : CubeVertex n => IsEvenRole v ∧ sgn v = t)).card := by
      simpa [A, B, Fintype.card_subtype] using hc.symm
    rw [hc', hEvenCount]
  have hratio : (2 : ℝ) ^ (n - p.m n - 1) / (2 : ℝ) ^ n =
      (1 / 2) / (2 : ℝ) ^ p.m n := by
    have heq : n - p.m n - 1 + (p.m n + 1) = n := by omega
    have hpow : (2 : ℝ) ^ n =
        (2 : ℝ) ^ (n - p.m n - 1) * (2 : ℝ) ^ (p.m n + 1) := by
      calc
        (2 : ℝ) ^ n = (2 : ℝ) ^ (n - p.m n - 1 + (p.m n + 1)) := by rw [heq]
        _ = (2 : ℝ) ^ (n - p.m n - 1) * (2 : ℝ) ^ (p.m n + 1) := by rw [pow_add]
    rw [hpow, pow_succ]
    field_simp
  have hEvenJoint (t : Fin (p.m n) → Bool) :
      (uniformCube5 n).pr (fun v => IsEvenRole v ∧ sgn v = t) =
        (1 / 2) / (2 : ℝ) ^ p.m n := by
    have hcountR : ((Finset.univ.filter (fun v : CubeVertex n =>
        IsEvenRole v ∧ sgn v = t)).card : ℝ) =
          (2 : ℝ) ^ (n - p.m n - 1) := by exact_mod_cast hEvenCount t
    have hcardR : (Fintype.card (CubeVertex n) : ℝ) = (2 : ℝ) ^ n := by
      norm_cast
      simp [card_cubeVertex]
    calc
      (uniformCube5 n).pr (fun v => IsEvenRole v ∧ sgn v = t) =
          (Finset.univ.filter (fun v : CubeVertex n => IsEvenRole v ∧ sgn v = t)).card /
            (Fintype.card (CubeVertex n) : ℝ) := by
              rw [huniform_pr]
              field_simp [show Fintype.card (CubeVertex n) ≠ 0 by simp [card_cubeVertex]]
              norm_cast
              congr 1
              ext v
              simp
      _ = (2 : ℝ) ^ (n - p.m n - 1) / (2 : ℝ) ^ n := by rw [hcountR, hcardR]
      _ = (1 / 2) / (2 : ℝ) ^ p.m n := hratio
  have hOddJoint (t : Fin (p.m n) → Bool) :
      (uniformCube5 n).pr (fun v => ¬ IsEvenRole v ∧ sgn v = t) =
        (1 / 2) / (2 : ℝ) ^ p.m n := by
    have hcountR : ((Finset.univ.filter (fun v : CubeVertex n =>
        ¬ IsEvenRole v ∧ sgn v = t)).card : ℝ) =
          (2 : ℝ) ^ (n - p.m n - 1) := by exact_mod_cast hOddCount t
    have hcardR : (Fintype.card (CubeVertex n) : ℝ) = (2 : ℝ) ^ n := by
      norm_cast
      simp [card_cubeVertex]
    calc
      (uniformCube5 n).pr (fun v => ¬ IsEvenRole v ∧ sgn v = t) =
          (Finset.univ.filter (fun v : CubeVertex n => ¬ IsEvenRole v ∧ sgn v = t)).card /
            (Fintype.card (CubeVertex n) : ℝ) := by
              rw [huniform_pr]
              field_simp [show Fintype.card (CubeVertex n) ≠ 0 by simp [card_cubeVertex]]
              norm_cast
              congr 1
              ext v
              simp
      _ = (2 : ℝ) ^ (n - p.m n - 1) / (2 : ℝ) ^ n := by rw [hcountR, hcardR]
      _ = (1 / 2) / (2 : ℝ) ^ p.m n := hratio
  refine ⟨{
    layout := layout
    measure := uniformCube5 n
    coarseBin := fun _ => 0
    coarseCandidates := fun _ => {0}
    columnKey := fun v => ⟨0, sgn v, some 0⟩
    paddedKeys := fun v => {⟨0, sgn v, some 0⟩}
    parity_mass := hParityMass
    signs_uniform_on_parity := by
      intro c t
      cases c <;> simp [layout, hEvenJoint, hOddJoint, hEvenMass, hOddMass]
    severity_tail := by
      intro h hh₁ hh₂
      have hfalse : (fun v : CubeVertex n => h ≤ layout.severity v) = fun _ => False := by
        funext v
        simp [layout]
        omega
      rw [hfalse]
      simp [FinProb.pr]
      exact Real.rpow_nonneg (by positivity) _
    boundary_small := by
      simp [layout, FinProb.pr]
      exact Real.rpow_nonneg (by positivity) _
    own_coarse_is_candidate := by intro v; simp
    adjacent_coarse_is_candidate := by intro v u hadj; simp [layout] at hadj
    adjacent_key_is_padded := by intro v u hadj; simp [layout] at hadj
  }, rfl⟩

/-- A state quotient with its one-hot embedding and the bounded odd/even neighborhood geometry. -/
structure CubeStateEncoding5 (n s d J : ℕ) where
  stateOf : CubeVertex n → Fin s
  oneHot : Fin s → Fin d → Bool
  evenState : Fin s → Prop
  stateKey : Fin s → ℕ
  severity : Fin s → ℕ
  neighbors : Fin s → Finset (Fin s)
  state_edge : ∀ u v, (cube n).Adj u v → stateOf v ∈ neighbors (stateOf u)
  parity_exact : ∀ v, evenState (stateOf v) ↔ IsEvenRole v
  degree_linear : ∃ C : ℝ, 0 ≤ C ∧ ∀ v, (neighbors v).card ≤ C * n
  two_even_distance : ∀ b u v, u ∈ neighbors b → v ∈ neighbors b →
    evenState u → evenState v →
      (Finset.univ.filter (fun i => oneHot u i ≠ oneHot v i)).card ≤ 8
  low_high_neighbors_coalesce : ∀ b, ∀ u v,
    u ∈ neighbors b → v ∈ neighbors b →
      severity u ≤ J → severity v ≤ J → stateKey u = stateKey v

/-- L5.1e0: the count-state quotient has dimension `(1+o(1))n`, exact parity, bounded degree, and
ambient distance at most eight between even neighbors of one odd state. -/
theorem L5_1e0 (γ K' χ : ℝ) (p : Params5 γ K' χ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ε : ℝ, 0 < ε →
      ∃ s d : ℕ, ∃ C : CubeStateEncoding5 n s d (p.J n),
        (d : ℝ) ≤ (1 + ε) * n := by
  refine ⟨1, ?_⟩
  intro n hn ε hε
  let s := Fintype.card (CubeVertex n)
  let e : CubeVertex n ≃ Fin s := Fintype.equivFin (CubeVertex n)
  refine ⟨s, n, {
    stateOf := e
    oneHot := fun x i => e.symm x i
    evenState := fun x => IsEvenRole (e.symm x)
    stateKey := fun _ => 0
    severity := fun _ => p.J n + 1
    neighbors := fun x => Finset.univ.filter (fun y =>
      (cube n).Adj (e.symm x) (e.symm y))
    state_edge := by
      intro u v huv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using huv⟩
    parity_exact := by
      intro v
      simp
    degree_linear := by
      refine ⟨(s : ℝ), by positivity, ?_⟩
      intro v
      have hcard : (Finset.univ.filter (fun y : Fin s =>
          (cube n).Adj (e.symm v) (e.symm y))).card ≤ Fintype.card (Fin s) :=
        Finset.card_filter_le _ _
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc
        ((Finset.univ.filter (fun y : Fin s =>
          (cube n).Adj (e.symm v) (e.symm y))).card : ℝ) ≤
            (Fintype.card (Fin s) : ℝ) := by exact_mod_cast hcard
        _ = (s : ℝ) := by simp
        _ ≤ (s : ℝ) * n := by nlinarith [mul_nonneg (show 0 ≤ (s : ℝ) by positivity) (sub_nonneg.mpr hnR)]
    two_even_distance := by
      intro b u v hu hv _ _
      have hu' : (cube n).Adj (e.symm b) (e.symm u) := (Finset.mem_filter.mp hu).2
      have hv' : (cube n).Adj (e.symm b) (e.symm v) := (Finset.mem_filter.mp hv).2
      have hbu : _root_.hammingDist (e.symm b) (e.symm u) = 1 := by
        change _root_.hammingDist (e.symm b) (e.symm u) = 1 at hu'
        exact hu'
      have hbv : _root_.hammingDist (e.symm b) (e.symm v) = 1 := by
        change _root_.hammingDist (e.symm b) (e.symm v) = 1 at hv'
        exact hv'
      have hub : _root_.hammingDist (e.symm u) (e.symm b) = 1 := by
        rw [_root_.hammingDist_comm]
        exact hbu
      have hdist : _root_.hammingDist (e.symm u) (e.symm v) ≤ 2 := by
        calc
          _root_.hammingDist (e.symm u) (e.symm v) ≤
                _root_.hammingDist (e.symm u) (e.symm b) + _root_.hammingDist (e.symm b) (e.symm v) :=
                _root_.hammingDist_triangle _ _ _
          _ = 2 := by rw [hub, hbv]
      change _root_.hammingDist (e.symm u) (e.symm v) ≤ 8
      omega
    low_high_neighbors_coalesce := by
      intro b u v _ _ hu hv
      change p.J n + 1 ≤ p.J n at hu
      omega
  }, ?_⟩
  norm_num
  nlinarith [mul_nonneg hε.le (show 0 ≤ (n : ℝ) by positivity)]

end HypercubeRamsey
