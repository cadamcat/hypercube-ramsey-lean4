import HypercubeRamsey.Framework.Stage
import HypercubeRamsey.Tools.Binomial
import HypercubeRamsey.Tools.CubeGeometry_p_tools_cube_r

/-!
# Cube geometry and Hamming-ball bounds

F-Cube provides explicit finite-cube operations, parity classes, prefix leaves, internal coordinates, slices,
and the stage-level `CubeIn` predicate. X-HammingBall supplies entropy volume, layer ratios, and the
hypergeometric intersection tail used by the height argument.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey

/-- Flip one coordinate of a Boolean cube vertex. -/
def cubeFlip {n : ℕ} (v : CubeVertex n) (i : Fin n) : CubeVertex n :=
  Function.update v i (!v i)

/-- Hamming distance on the Boolean cube. -/
def hammingDist {n : ℕ} (u v : CubeVertex n) : ℕ :=
  (Finset.univ.filter (fun i => u i ≠ v i)).card

/-- The radius-`r` Hamming ball around `v`. -/
def hammingBall {n : ℕ} (v : CubeVertex n) (r : ℕ) : Finset (CubeVertex n) :=
  Finset.univ.filter (fun u => hammingDist v u ≤ r)

/-- Finset of even-role cube vertices. -/
noncomputable def evenRoleSet (n : ℕ) : Finset (CubeVertex n) :=
  by classical exact Finset.univ.filter (fun v => IsEvenRole v)

/-- A prefix leaf fixes the first `ell` coordinates to the word `w`. -/
def cubeLeaf {n ell : ℕ} (hle : ell ≤ n) (w : Fin ell → Bool) : Finset (CubeVertex n) :=
  Finset.univ.filter (fun v => ∀ j : Fin ell, v (Fin.castLE hle j) = w j)

/-- The final `h` coordinates, used as an internal coordinate set. -/
def topCoordinates (n h : ℕ) (_hle : h ≤ n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => n - h ≤ j.val)

/-- A slice of a prefix leaf fixes all coordinates outside the supplied internal set. -/
def cubeSlice {n ell : ℕ} (hle : ell ≤ n) (w : Fin ell → Bool)
    (internal : Finset (Fin n)) (outside : CubeVertex n) : Finset (CubeVertex n) :=
  Finset.univ.filter (fun v =>
    (∀ j : Fin ell, v (Fin.castLE hle j) = w j) ∧
    (∀ j, j ∉ internal → v j = outside j))

/-- `CubeIn` is the stage-level monochromatic cube predicate from Part C §3.15. -/
def CubeIn (T : Stage) (k : ℕ) (c : Colour) : Prop :=
  Nonempty ((cube (T.S.n k)).Copy (crossGraph (Hits (T.S.E k) c)))

/-- F-Cube: flipping one coordinate gives adjacent cube vertices. -/
theorem cubeFlip_adj {n : ℕ} (v : CubeVertex n) (i : Fin n) :
    (cube n).Adj v (cubeFlip v i) := by
  change _root_.hammingDist v (cubeFlip v i) = 1
  classical
  change (Finset.univ.filter (fun j : Fin n => v j ≠ cubeFlip v i j)).card = 1
  have hset : Finset.univ.filter (fun j : Fin n => v j ≠ cubeFlip v i j) = {i} := by
    ext j
    by_cases hji : j = i
    · subst j
      cases hv : v i <;> simp [cubeFlip, hv]
    · have hflip : cubeFlip v i j = v j := Function.update_of_ne hji _ _
      simp [hflip, hji]
  rw [hset]
  simp

/-- F-Cube: one-coordinate flips exchange the two parity classes. -/
theorem cubeFlip_parity {n : ℕ} (v : CubeVertex n) (i : Fin n) :
    IsEvenRole (cubeFlip v i) ↔ ¬ IsEvenRole v := by
  classical
  let A := Finset.univ.filter (fun j : Fin n => v j = true)
  let B := Finset.univ.filter (fun j : Fin n => cubeFlip v i j = true)
  change Even B.card ↔ ¬ Even A.card
  by_cases hvi : v i = true
  · have hset : A = insert i B := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [A, B, cubeFlip, hvi]
      · have hflip : cubeFlip v i j = v j := Function.update_of_ne hji _ _
        simp [A, B, hflip, hji]
    have hi_notB : i ∉ B := by simp [B, cubeFlip, hvi]
    have hcard : A.card = B.card + 1 := by
      rw [hset, Finset.card_insert_of_notMem hi_notB]
    rw [hcard]
    have hparity : Even (B.card + 1) ↔ ¬ Even B.card := Nat.even_add_one
    tauto
  · have hvi' : v i = false := Bool.eq_false_iff.mpr hvi
    have hset : B = insert i A := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [A, B, cubeFlip, hvi']
      · have hflip : cubeFlip v i j = v j := Function.update_of_ne hji _ _
        simp [A, B, hflip, hji]
    have hi_notA : i ∉ A := by simp [A, hvi']
    have hcard : B.card = A.card + 1 := by
      rw [hset, Finset.card_insert_of_notMem hi_notA]
    rw [hcard]
    exact Nat.even_add_one

/-- F-Cube: Hamming distance satisfies the triangle inequality. -/
theorem hammingDist_triangle {n : ℕ} (u v w : CubeVertex n) :
    hammingDist u w ≤ hammingDist u v + hammingDist v w := by
  exact _root_.hammingDist_triangle u v w

/-- F-Cube: for positive dimension, each parity class has exactly half the vertices. -/
theorem parity_class_card {n : ℕ} (hn : 0 < n) :
    (evenRoleSet n).card = 2 ^ (n - 1) ∧
    (Finset.univ \ evenRoleSet n).card = 2 ^ (n - 1) := by
  classical
  let E := evenRoleSet n
  let O := Finset.univ \ E
  let flip : CubeVertex n → CubeVertex n := fun v => cubeFlip v ⟨0, by omega⟩
  have hinv : Function.Involutive flip := by
    intro v
    funext j
    by_cases hj : j = ⟨0, by omega⟩
    · subst j
      simp [flip, cubeFlip]
    · simp [flip, cubeFlip, hj]
  have himage : E.image flip = O := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hEven
      have hEven' : IsEvenRole (cubeFlip x ⟨0, by omega⟩) := by
        simpa [E, evenRoleSet] using hEven
      have hx' : IsEvenRole x := by simpa [E, evenRoleSet] using hx
      exact (cubeFlip_parity x ⟨0, by omega⟩).mp hEven' hx'
    · intro hy
      have hy' : ¬ IsEvenRole y := by
        simpa [E, evenRoleSet] using (Finset.mem_sdiff.mp hy).2
      have hx : IsEvenRole (cubeFlip y ⟨0, by omega⟩) :=
        (cubeFlip_parity y ⟨0, by omega⟩).mpr hy'
      refine Finset.mem_image.mpr ⟨flip y, ?_, hinv y⟩
      simpa [flip, E, evenRoleSet] using hx
  have heq : E.card = O.card := by
    rw [← Finset.card_image_of_injective E hinv.injective, himage]
  have htot : E.card + O.card = 2 ^ n := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
    simpa [O, Nat.add_comm, OAI.HypercubeRamsey.card_cubeVertex] using h
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := by ring
  have hdouble : 2 * E.card = 2 * 2 ^ (n - 1) := by
    omega
  have hcard : E.card = 2 ^ (n - 1) := Nat.mul_left_cancel (by omega) hdouble
  exact ⟨by simpa [E] using hcard, by simpa [O, E, hcard] using heq.symm⟩

/-- F-Cube: fixing a proper coordinate set leaves equally many even-role completions for every assignment. -/
theorem parity_projection_uniform {n : ℕ} (S : Finset (Fin n)) (hS : S.card < n)
    (z : ∀ i : S, Bool) :
    ((evenRoleSet n).filter (fun v : CubeVertex n => ∀ i : S, v i.1 = z i)).card =
      2 ^ (n - S.card - 1) := by
  classical
  let agree : CubeVertex n → Prop := fun v => ∀ i : S, v i.1 = z i
  let F : Finset (CubeVertex n) := Finset.univ.filter agree
  let E : Finset (CubeVertex n) := F.filter IsEvenRole
  let O : Finset (CubeVertex n) := F.filter fun v => ¬ IsEvenRole v
  let choices : ∀ i : Fin n, Finset Bool := fun i =>
    if hi : i ∈ S then {z ⟨i, hi⟩} else Finset.univ
  have hFpi : F = Fintype.piFinset choices := by
    ext v
    constructor
    · intro hv
      apply Fintype.mem_piFinset.mpr
      intro j
      by_cases hj : j ∈ S
      · have hz := (Finset.mem_filter.mp hv).2 ⟨j, hj⟩
        simpa [choices, hj] using hz
      · simp [choices, hj]
    · intro hv
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i
      have hi := Fintype.mem_piFinset.mp hv i.1
      simpa [choices, i.2] using hi
  have hFcard : F.card = 2 ^ (n - S.card) := by
    rw [hFpi, Fintype.card_piFinset]
    have hchoice : ∀ i : Fin n, (choices i).card = if i ∈ S then 1 else 2 := by
      intro i
      by_cases hi : i ∈ S <;> simp [choices, hi]
    simp_rw [hchoice]
    rw [Finset.prod_ite]
    have hfilter : Finset.univ.filter (fun i : Fin n => i ∉ S) = Finset.univ \ S := by
      ext i
      simp
    rw [hfilter, Finset.prod_const_one, Finset.prod_const (b := 2),
      Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp
  have hlt : S.card < (Finset.univ : Finset (Fin n)).card := by simpa using hS
  obtain ⟨j, hjU, hjS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  let flip : CubeVertex n → CubeVertex n := fun v => cubeFlip v j
  have hinv : Function.Involutive flip := by
    intro v
    funext i
    by_cases hij : i = j
    · subst i
      simp [flip, cubeFlip]
    · simp [flip, cubeFlip, hij]
  have hpres : ∀ v, v ∈ F → flip v ∈ F := by
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    have hi := (Finset.mem_filter.mp hv).2 i
    have hne : i.1 ≠ j := by
      intro hij
      exact hjS (hij ▸ i.2)
    simpa [flip, cubeFlip, hne] using hi
  have himage : E.image flip = O := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      rcases Finset.mem_filter.mp hx with ⟨hxF, hxE⟩
      apply Finset.mem_filter.mpr
      refine ⟨hpres x hxF, ?_⟩
      intro hflipE
      exact (cubeFlip_parity x j).mp hflipE hxE
    · intro hy
      rcases Finset.mem_filter.mp hy with ⟨hyF, hyO⟩
      apply Finset.mem_image.mpr
      refine ⟨flip y, Finset.mem_filter.mpr ⟨hpres y hyF, ?_⟩, hinv y⟩
      exact (cubeFlip_parity y j).mpr hyO
  have heq : E.card = O.card := by
    rw [← Finset.card_image_of_injective E hinv.injective, himage]
  have hsplit : E.card + O.card = F.card := by
    simpa [E, O] using (Finset.card_filter_add_card_filter_not (s := F) IsEvenRole)
  have hdouble : 2 * E.card = 2 ^ (n - S.card) := by
    rw [← hFcard]
    omega
  let q := n - S.card
  have hpos : 1 ≤ q := by dsimp [q]; omega
  have hpow : 2 ^ q = 2 * 2 ^ (q - 1) := by
    calc
      2 ^ q = 2 ^ (q - 1 + 1) := by rw [Nat.sub_add_cancel hpos]
      _ = 2 ^ (q - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (q - 1) := by ring
  have hcardE : E.card = 2 ^ (n - S.card - 1) := by
    have hcardEq : E.card = 2 ^ (q - 1) := by
      have htwo : 0 < (2 : ℕ) := by decide
      have hdoubleQ : 2 * E.card = 2 ^ q := by simpa [q] using hdouble
      exact Nat.mul_left_cancel htwo (hdoubleQ.trans hpow)
    simpa [q] using hcardEq
  have htarget :
      ((evenRoleSet n).filter (fun v : CubeVertex n => ∀ i : S, v i.1 = z i)).card = E.card := by
    simp [E, F, agree, evenRoleSet, Finset.filter_filter, and_comm]
  rw [htarget]
  exact hcardE

/-- X-HammingBall: the Hamming-ball volume is at most `exp(n H_bin(r/n))` for `r ≤ n/2`. -/
theorem hammingBall_volume_bound {n r : ℕ} (hn : 0 < n) (hr : r ≤ n / 2) (v : CubeVertex n) :
    (hammingBall v r).card ≤
      Real.exp (Real.binEntropy ((r : ℝ) / n) * n) := by
  classical
  let support : CubeVertex n → Finset (Fin n) := fun u =>
    Finset.univ.filter (fun i => u i ≠ v i)
  let B := hammingBall v r
  let Q := (Finset.univ : Finset (Fin n)).powerset.filter (fun s => s.card ≤ r)
  have hsupportDist (u : CubeVertex n) : (support u).card = hammingDist v u := by
    simp [support, hammingDist, ne_comm]
  have hinj : Set.InjOn support (B : Set (CubeVertex n)) := by
    intro x hx y hy hxy
    funext i
    have hiff : x i ≠ v i ↔ y i ≠ v i := by
      have h := congrArg (fun s : Finset (Fin n) => i ∈ s) hxy
      simpa [support] using h
    cases hv : v i <;> cases hxv : x i <;> cases hyv : y i <;> simp_all
  have hsubset : B.image support ⊆ Q := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    have hu' : u ∈ hammingBall v r := by simpa [B] using hu
    have hdistle : hammingDist v u ≤ r := (Finset.mem_filter.mp hu').2
    rw [hsupportDist]
    exact hdistle
  have hcard : B.card ≤ Q.card := by
    calc
      B.card = (B.image support).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Q.card := Finset.card_le_card hsubset
  have hQsum : Q.card =
      ∑ k ∈ Finset.range (n + 1), if k ≤ r then Nat.choose n k else 0 := by
    calc
      Q.card = ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
          if s.card ≤ r then 1 else 0 := by
        simpa [Q] using
          (Finset.natCast_card_filter (R := ℕ)
            (p := fun s : Finset (Fin n) => s.card ≤ r)
            (s := (Finset.univ : Finset (Fin n)).powerset))
      _ = ∑ k ∈ Finset.range (n + 1),
          Nat.choose n k * (if k ≤ r then 1 else 0) := by
        simpa [Fintype.card_fin, nsmul_eq_mul] using
          (Finset.sum_powerset_apply_card
            (f := fun k : ℕ => if k ≤ r then (1 : ℕ) else 0)
            (x := (Finset.univ : Finset (Fin n))))
      _ = _ := by simp
  have hQreal : (Q.card : ℝ) =
      ∑ k ∈ Finset.range (n + 1),
        if k ≤ r then (Nat.choose n k : ℝ) else 0 := by
    exact_mod_cast hQsum
  by_cases hr0 : r = 0
  · subst r
    have hQone : Q.card = 1 := by simpa using hQsum
    have hBone : B.card ≤ 1 := by simpa [hQone] using hcard
    simpa [Real.binEntropy_zero] using hBone
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    let q : ℝ := (r : ℝ) / n
    let b : ℝ := 1 - q
    let F : ℝ := q ^ r * b ^ (n - r)
    have h2r : 2 * r ≤ n := by omega
    have hrn : r ≤ n := le_trans hr (Nat.div_le_self n 2)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hq0 : 0 < q := by dsimp [q]; positivity
    have hqmul : q * n = (r : ℝ) := by
      dsimp [q]
      field_simp [ne_of_gt hnR]
    have hqhalf : q ≤ b := by
      have h2rR : (2 : ℝ) * r ≤ n := by exact_mod_cast h2r
      dsimp [b]
      dsimp [q]
      rw [div_le_iff₀ hnR]
      norm_num
      nlinarith
    have hb0 : 0 < b := by dsimp [b]; linarith
    have hbn : b * n = ((n - r : ℕ) : ℝ) := by
      dsimp [b]
      rw [sub_mul, one_mul, hqmul]
      exact (Nat.cast_sub hrn).symm
    have hFpos : 0 < F := by positivity
    have hfactor_le : ∀ k, k ≤ r → F ≤ q ^ k * b ^ (n - k) := by
      intro k hkr
      have hqpow : q ^ r = q ^ k * q ^ (r - k) := by
        have hexp : k + (r - k) = r := Nat.add_sub_of_le hkr
        calc
          q ^ r = q ^ (k + (r - k)) := congrArg (fun m : ℕ => q ^ m) hexp.symm
          _ = q ^ k * q ^ (r - k) := pow_add q k (r - k)
      have hbpw : b ^ (n - k) = b ^ (n - r) * b ^ (r - k) := by
        have hexp : (n - r) + (r - k) = n - k := by omega
        calc
          b ^ (n - k) = b ^ ((n - r) + (r - k)) :=
            congrArg (fun m : ℕ => b ^ m) hexp.symm
          _ = b ^ (n - r) * b ^ (r - k) := pow_add b (n - r) (r - k)
      change q ^ r * b ^ (n - r) ≤ q ^ k * b ^ (n - k)
      rw [hqpow]
      calc
        q ^ k * q ^ (r - k) * b ^ (n - r) ≤
            q ^ k * b ^ (r - k) * b ^ (n - r) := by gcongr
        _ = q ^ k * b ^ (n - k) := by rw [hbpw]; ring
    have hbinomial :
        (∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * q ^ k * b ^ (n - k)) = 1 := by
      have hqb : q + b = 1 := by dsimp [b]; ring
      have hadd := add_pow q b n
      rw [hqb, one_pow] at hadd
      calc
        (∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * q ^ k * b ^ (n - k)) =
            ∑ k ∈ Finset.range (n + 1),
              q ^ k * b ^ (n - k) * (Nat.choose n k : ℝ) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
        _ = 1 := hadd.symm
    have hweighted :
        (∑ k ∈ Finset.range (n + 1),
          if k ≤ r then F * (Nat.choose n k : ℝ) else 0) ≤ 1 := by
      calc
        _ ≤ ∑ k ∈ Finset.range (n + 1),
            (Nat.choose n k : ℝ) * q ^ k * b ^ (n - k) := by
          apply Finset.sum_le_sum
          intro k hk
          by_cases hkr : k ≤ r
          · simp only [if_pos hkr]
            have hterm := hfactor_le k hkr
            have hchoose : 0 ≤ (Nat.choose n k : ℝ) := by positivity
            nlinarith [hterm]
          · simp [hkr]
            positivity
        _ = 1 := hbinomial
    have hFQ : F * (Q.card : ℝ) ≤ 1 := by
      calc
        F * (Q.card : ℝ) =
            ∑ k ∈ Finset.range (n + 1),
              if k ≤ r then F * (Nat.choose n k : ℝ) else 0 := by
          rw [hQreal, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkr : k ≤ r <;> simp [hkr]
        _ ≤ 1 := hweighted
    have hQle : (Q.card : ℝ) ≤ F⁻¹ := by
      have hmul : (Q.card : ℝ) * F ≤ F⁻¹ * F := by
        rw [inv_mul_cancel₀ hFpos.ne']
        nlinarith [hFQ]
      exact le_of_mul_le_mul_right hmul hFpos
    have harg : Real.binEntropy q * n =
        (r : ℝ) * Real.log q⁻¹ + ((n - r : ℕ) : ℝ) * Real.log b⁻¹ := by
      rw [Real.binEntropy]
      calc
        (q * Real.log q⁻¹ + (1 - q) * Real.log (1 - q)⁻¹) * n =
            (q * n) * Real.log q⁻¹ + ((1 - q) * n) * Real.log (1 - q)⁻¹ := by ring
        _ = (r : ℝ) * Real.log q⁻¹ + ((n - r : ℕ) : ℝ) * Real.log b⁻¹ := by
            rw [hqmul, show 1 - q = b from rfl, hbn]
    have hexp : Real.exp (Real.binEntropy q * n) = F⁻¹ := by
      rw [harg, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (inv_pos.mpr hq0), Real.exp_log (inv_pos.mpr hb0)]
      simp [F, mul_inv]
      ring
    calc
      (B.card : ℝ) ≤ Q.card := by exact_mod_cast hcard
      _ ≤ F⁻¹ := hQle
      _ = Real.exp (Real.binEntropy q * n) := hexp.symm
      _ = Real.exp (Real.binEntropy ((r : ℝ) / n) * n) := by rfl

/-- X-HammingBall: adjacent binomial layers have the exact ratio `r/(d-r+1)`. -/
theorem hammingLayer_ratio (d r : ℕ) (hr : 0 < r) (hrd : r ≤ d) :
    (Nat.choose d (r - 1) : ℝ) * (d - r + 1 : ℕ) =
      (Nat.choose d r : ℝ) * r := by
  have hr' : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega))
  have h := Nat.choose_succ_right_eq d (r - 1)
  rw [hr'] at h
  have hsub : d - (r - 1) = d - r + 1 := by omega
  rw [hsub] at h
  exact_mod_cast h.symm

/-- X-HammingBall: a uniform `s`-subset has a sub-Gaussian upper tail for its intersection with a fixed
subset (the hypergeometric tail used in ball-intersection estimates). -/
theorem hypergeometric_intersection_tail (d s : ℕ) (hd : 0 < d) (hs : 0 < s) (hsd : s ≤ d)
    (A : Finset (Fin d)) (t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter (fun B : Finset (Fin d) =>
      B.card = s ∧ ((B ∩ A).card : ℝ) ≥
        (s : ℝ) * A.card / d + t)).card : ℝ) / Nat.choose d s ≤
      Real.exp (-2 * t ^ 2 / s) := by
  exact CubeGeometryPToolsCubeR.hypergeometricIntersectionTailAux d s hd hs hsd A t ht

end HypercubeRamsey
