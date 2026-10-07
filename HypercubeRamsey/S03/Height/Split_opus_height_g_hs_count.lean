import HypercubeRamsey.S03.Height.Selection_p_height_main

namespace HypercubeRamsey

namespace Lane_g_hs_count

open Classical
open OAI.HypercubeRamsey
open Lane_p_height_main

/-- The sum of binomial coefficients up to `s` is at most `(d + 1)^s`. -/
theorem choose_sum_le_pow (d s : ℕ) :
    ∑ i ∈ Finset.range (s + 1), Nat.choose d i ≤ (d + 1) ^ s := by
  induction s with
  | zero =>
    simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have hterm : Nat.choose d (s + 1) ≤ d * (d + 1) ^ s := by
      cases d with
      | zero => simp
      | succ d' =>
        calc
          Nat.choose (d' + 1) (s + 1) ≤ (d' + 1) ^ (s + 1) := Nat.choose_le_pow (d' + 1) (s + 1)
          _ = (d' + 1) * (d' + 1) ^ s := by rw [pow_succ, Nat.mul_comm]
          _ ≤ (d' + 1) * (d' + 1 + 1) ^ s :=
            Nat.mul_le_mul_left (d' + 1) (Nat.pow_le_pow_left (by omega) s)
    calc
      (∑ i ∈ Finset.range (s + 1), Nat.choose d i) + Nat.choose d (s + 1) ≤
          (d + 1) ^ s + d * (d + 1) ^ s := Nat.add_le_add ih hterm
      _ = (d + 1) ^ (s + 1) := by
        rw [pow_succ, Nat.mul_comm]
        ring

/-- The cardinality of a Hamming ball of radius `s` in `CubeVertex d` is at most `(d + 1)^s`. -/
theorem cube_ball_card_le_pow (d s : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ s)).card ≤ (d + 1) ^ s := by
  have heq : (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ s)) =
      (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ s)) := by
    apply Finset.filter_congr
    intro u _
    rw [hammingDist_custom_eq_root]
  rw [heq]
  by_cases hsd : s ≤ d
  · rw [cube_ball_card_eq_choose_sum v hsd]
    exact choose_sum_le_pow d s
  · have hds : d < s := not_le.mp hsd
    have hcard : (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ s)).card ≤ 2 ^ d := by
      calc
        (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ s)).card ≤
            (Finset.univ : Finset (CubeVertex d)).card := Finset.card_filter_le _ _
        _ = 2 ^ d := by
          simp only [Finset.card_univ]
          have hc : Fintype.card (CubeVertex d) = Fintype.card (Fin d → Bool) := rfl
          rw [hc, Fintype.card_fun]
          simp
    have h2d : 2 ^ d ≤ (d + 1) ^ d := by
      cases d with
      | zero => simp
      | succ d' =>
        exact Nat.pow_le_pow_left (by omega) (d' + 1)
    have hd_le_s : (d + 1) ^ d ≤ (d + 1) ^ s :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact hcard.trans (h2d.trans hd_le_s)

/-- If metric scale distance is strictly below `R`, Hamming distance is at most `D * R`. -/
theorem hammingDist_le_of_hdScaleDistance_lt {p : HDParams} (hD : 0 < p.D)
    (s t : HDState p) (R : ℕ) (hdist : hdScaleDistance p.D s t < R) :
    _root_.hammingDist s.1 t.1 ≤ p.D * R := by
  unfold hdScaleDistance at hdist
  have hspaceDiv :
      (_root_.hammingDist s.1 t.1 + max 1 p.D - 1) / max 1 p.D < R :=
    lt_of_le_of_lt (Nat.le_max_right _ _) hdist
  have hmax : max 1 p.D = p.D := max_eq_right (by omega : 1 ≤ p.D)
  rw [hmax] at hspaceDiv
  have hspaceNum : _root_.hammingDist s.1 t.1 + p.D - 1 < R * p.D :=
    (Nat.div_lt_iff_lt_mul hD).1 hspaceDiv
  rw [Nat.mul_comm] at hspaceNum
  omega

/-- The number of state pairs within metric scale distance `R` of `x` is bounded by
`(H + 1) * (d + 1)^(D * R)`. -/
theorem scale_pairs_card_le (p : HDParams) (hD : 0 < p.D) (x : HDState p) (R : ℕ) :
    (((Finset.univ : Finset (CubeVertex p.d × Fin (p.H + 1))).filter (fun y =>
      hdScaleDistance p.D x (y.1, y.2.val) < R)).image (fun y => (y.1, y.2.val))).card ≤
        (p.H + 1) * (p.d + 1) ^ (p.D * R) := by
  let S := (Finset.univ : Finset (CubeVertex p.d × Fin (p.H + 1))).filter (fun y =>
    hdScaleDistance p.D x (y.1, y.2.val) < R)
  have himage : (S.image (fun y => (y.1, y.2.val))).card ≤ S.card :=
    Finset.card_image_le
  let B : Finset (CubeVertex p.d) :=
    Finset.univ.filter (fun u => _root_.hammingDist u x.1 ≤ p.D * R)
  let L : Finset (Fin (p.H + 1)) := Finset.univ
  have hsub : S ⊆ B ×ˢ L := by
    intro y hy
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := hammingDist_le_of_hdScaleDistance_lt hD x (y.1, y.2.val) R hy
    rw [_root_.hammingDist_comm] at h1
    exact h1
  have hScard : S.card ≤ B.card * L.card := by
    calc
      S.card ≤ (B ×ˢ L).card := Finset.card_le_card hsub
      _ = B.card * L.card := Finset.card_product B L
  have hLcard : L.card = p.H + 1 := by simp [L]
  have hBcard : B.card ≤ (p.d + 1) ^ (p.D * R) :=
    cube_ball_card_le_pow p.d (p.D * R) x.1
  have hS_le : S.card ≤ (p.H + 1) * (p.d + 1) ^ (p.D * R) := by
    rw [hLcard] at hScard
    calc
      S.card ≤ B.card * (p.H + 1) := hScard
      _ = (p.H + 1) * B.card := Nat.mul_comm _ _
      _ ≤ (p.H + 1) * (p.d + 1) ^ (p.D * R) := Nat.mul_le_mul_left _ hBcard
  exact himage.trans hS_le

/-- The number of subsets of size `q` satisfying any predicate is at most `s.card ^ q`. -/
theorem powerset_filter_card_le_pow {α : Type*} (s : Finset α) (q : ℕ)
    (P : Finset α → Prop) :
    (s.powerset.filter (fun (Y : Finset α) => Y.card = q ∧ P Y)).card ≤ s.card ^ q := by
  classical
  have hsub : s.powerset.filter (fun Y => Y.card = q ∧ P Y) ⊆ Finset.powersetCard q s := by
    intro Y hY
    simp only [Finset.mem_filter] at hY
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.mem_powerset.mp hY.1, hY.2.1⟩
  have hpow := Finset.card_le_card hsub
  have hchoose : (Finset.powersetCard q s).card = Nat.choose s.card q := by
    exact Finset.card_powersetCard q s
  rw [hchoose] at hpow
  exact hpow.trans (Nat.choose_le_pow s.card q)

end Lane_g_hs_count

end HypercubeRamsey
