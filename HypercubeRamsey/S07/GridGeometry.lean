import HypercubeRamsey.Framework.Embedding
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Tools.Binomial
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# L7.1a: grid geometry

Source: `sections/07-…tex`, lines 55–68 and 77–82.  The geometry records disjoint special chunks, auxiliary
coordinates, a residual coordinate, and monotone binning maps whose binomial masses are small.  A cube vertex
reads the cell `(g, t)`: `g` is the vector of bin indices of its chunk counts (the grid key), `t` its bits on
the auxiliary coordinates (the auxiliary word).

Grid distance is the number of one-bin moves (`keyDist`), auxiliary distance is Hamming distance (`auxDist`);
their sum is the distance in the grid-times-auxiliary graph used by the local lemma (07:250–253).  The cross
names of a cell `(g, t)` are `(h, t)` for the keys `h` at grid distance one; its own names are `(g, t')` for
the words `t'` at auxiliary distance at most one (07:73–82).
-/

namespace HypercubeRamsey.S07

open OAI.HypercubeRamsey
open Filter

/-- A grid partition of cube coordinates with small binomial mass in every bin. -/
structure GridGeom (d : ℝ) (n s ℓ q : ℕ) where
  chunk : Fin s → Finset (Fin n)
  aux : Finset (Fin n)
  chunk_card : ∀ r, (chunk r).card = ℓ
  chunks_disjoint : Pairwise fun r r' => Disjoint (chunk r) (chunk r')
  aux_card : aux.card = q
  aux_disjoint : ∀ r, Disjoint aux (chunk r)
  residual_nonempty : ∃ j : Fin n, j ∉ aux ∧ ∀ r, j ∉ chunk r
  bins : Fin s → ℕ
  bin : ∀ r, Fin (ℓ + 1) → Fin (bins r)
  bin_monotone : ∀ r k k', k.val ≤ k'.val → (bin r k).val ≤ (bin r k').val
  bin_surjective : ∀ r, Function.Surjective (bin r)
  bin_mass : ∀ r b,
    (∑ k : Fin (ℓ + 1),
      if bin r k = b then ((Nat.choose ℓ k.val : ℕ) : ℝ) / (2 : ℝ) ^ ℓ else 0) ≤
        2 * (n : ℝ) ^ (-(d / 4))

/-- A key is one bin index for each special chunk. -/
abbrev GridGeom.Key {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) :=
  ∀ r, Fin (Γ.bins r)

/-- An auxiliary word records the bits on the auxiliary coordinate set. -/
abbrev GridGeom.AuxWord {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) :=
  Γ.aux → Bool

/-- A grid cell pairs a key with an auxiliary word. -/
abbrev GridGeom.Cell {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) :=
  GridGeom.Key Γ × GridGeom.AuxWord Γ

/-- The grid key read by a cube vertex: one bin index per special chunk and the auxiliary bits. -/
noncomputable def GridGeom.key {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (v : CubeVertex n) : (∀ r, Fin (Γ.bins r)) × (Γ.aux → Bool) := by
  classical
  let b : ∀ r, Fin (ℓ + 1) := fun r =>
    ⟨((Γ.chunk r).filter (fun j => v j = true)).card,
      Nat.lt_succ_of_le (by
        calc
          ((Γ.chunk r).filter (fun j => v j = true)).card ≤ (Γ.chunk r).card :=
            Finset.card_filter_le _ _
          _ = ℓ := Γ.chunk_card r)⟩
  exact (fun r => Γ.bin r (b r), fun j => v j)

/-- The number of special chunks, `s = ⌈n^d⌉` (07:55). -/
noncomputable def gS (d : ℝ) (n : ℕ) : ℕ := Nat.ceil ((n : ℝ) ^ d)

/-- The chunk length, `⌊n^d⌋` (07:56). -/
noncomputable def gL (d : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ d⌋₊

/-- The number of auxiliary bits, `q = ⌈n^{4d}⌉` (07:57). -/
noncomputable def gQ (d : ℝ) (n : ℕ) : ℕ := Nat.ceil ((n : ℝ) ^ (4 * d))

/-- The Section 7 geometry at dimension `n`. -/
abbrev Geom (d : ℝ) (n : ℕ) := GridGeom d n (gS d n) (gL d n) (gQ d n)

/-- L7.1a (07:55–68): for large `n` the prescribed chunks, auxiliary bits, residual coordinate and bins exist.
The bound `d < 1/8` (the paper has `d < D₀/1000 < 10⁻⁴`) makes `sℓ + q + 1 ≤ n` for large `n`; each bin has
`Binomial(ℓ, 1/2)`-mass at most `2n^{-d/4}` because every atom is `O(n^{-d/2})`. -/
theorem gridGeom_exists (d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Nonempty (Geom d n) := by
  classical
  have hhalf : 0 < d / 2 := by linarith
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (d / 2)) atTop atTop :=
    (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop, 256 ≤ n ∧ 2 ≤ (n : ℝ) ^ (d / 2) := by
    filter_upwards [eventually_ge_atTop 256,
      (tendsto_atTop.1 hpow 2)] with n hn hn'
    exact ⟨hn, hn'⟩
  obtain ⟨n₀, hn₀⟩ := (eventually_atTop.1 hevent)
  refine ⟨n₀, ?_⟩
  intro n hn
  have hn0 := hn₀ n hn
  have hnlarge : 256 ≤ n := hn0.1
  have hnlargeR : (256 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlarge
  have hrootlower : 2 ≤ (n : ℝ) ^ (d / 2) := hn0.2
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  let x : ℝ := (n : ℝ) ^ d
  let s : ℕ := gS d n
  let ell : ℕ := gL d n
  let q : ℕ := gQ d n
  let root : ℝ := (n : ℝ) ^ (1 / 2 : ℝ)
  have hroot_sq : root ^ 2 = n := by
    have hroot : root = Real.sqrt (n : ℝ) := by
      dsimp [root]
      rw [← Real.sqrt_eq_rpow]
    simpa [hroot] using (Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)))
  have hroot_ge : 16 ≤ root := by
    have h := Real.sqrt_le_sqrt (show (256 : ℝ) ≤ (n : ℝ) by exact_mod_cast hnlarge)
    have hsqrt : (Real.sqrt (256 : ℝ)) = 16 := by norm_num
    simpa [root, ← Real.sqrt_eq_rpow, hsqrt] using h
  have hroot_small : root ≤ (n : ℝ) / 16 := by
    have hmul := mul_le_mul_of_nonneg_right hroot_ge (show 0 ≤ root by positivity)
    nlinarith [hroot_sq, hmul]
  have hxlarge : 4 ≤ x := by
    dsimp [x]
    have hsq : ((n : ℝ) ^ (d / 2)) ^ 2 = (n : ℝ) ^ d := by
      calc
        ((n : ℝ) ^ (d / 2)) ^ 2 = (n : ℝ) ^ ((d / 2) * 2) :=
          (Real.rpow_mul_natCast (by positivity : 0 ≤ (n : ℝ)) (d / 2) 2).symm
        _ = (n : ℝ) ^ d := by congr 1 <;> ring
    rw [← hsq]
    nlinarith [hrootlower]
  have hs_le : (s : ℝ) ≤ x + 1 := by
    dsimp [s, gS, x]
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ d)).le
  have hell_le : (ell : ℝ) ≤ x := by
    dsimp [ell, gL, x]
    exact Nat.floor_le (by positivity : 0 ≤ (n : ℝ) ^ d)
  have hell_ge : (n : ℝ) ^ (d / 2) ≤ (ell : ℝ) := by
    have hfloor : x - 1 ≤ (ell : ℝ) := by
      have h : x < (ell : ℝ) + 1 := by
        dsimp [ell, gL, x]
        exact Nat.lt_floor_add_one ((n : ℝ) ^ d)
      linarith
    have hsq : ((n : ℝ) ^ (d / 2)) ^ 2 = x := by
      dsimp [x]
      calc
        ((n : ℝ) ^ (d / 2)) ^ 2 = (n : ℝ) ^ ((d / 2) * 2) :=
          (Real.rpow_mul_natCast (by positivity : 0 ≤ (n : ℝ)) (d / 2) 2).symm
        _ = (n : ℝ) ^ d := by congr 1 <;> ring
    nlinarith [hrootlower, hxlarge]
  have hd8 : d ≤ (1 : ℝ) / 8 := hd'.le
  have h2d4 : 2 * d ≤ (1 : ℝ) / 4 := by nlinarith
  have h4d2 : 4 * d ≤ (1 : ℝ) / 2 := by nlinarith
  have hpow_d : (n : ℝ) ^ d ≤ (n : ℝ) ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR hd8
  have hpow_2d : (n : ℝ) ^ (2 * d) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR h2d4
  have hpow_4d : (n : ℝ) ^ (4 * d) ≤ root := by
    simpa [root] using
      (Real.rpow_le_rpow_of_exponent_le hnR h4d2)
  have hpow_1_8_root : (n : ℝ) ^ (1 / 8 : ℝ) ≤ root := by
    apply Real.rpow_le_rpow_of_exponent_le hnR
    norm_num
  have hpow_1_4_root : (n : ℝ) ^ (1 / 4 : ℝ) ≤ root := by
    apply Real.rpow_le_rpow_of_exponent_le hnR
    norm_num
  have hs_ell : (s : ℝ) * (ell : ℝ) ≤ 2 * root := by
    have hmul : (s : ℝ) * (ell : ℝ) ≤ (x + 1) * x :=
      mul_le_mul hs_le hell_le (by positivity) (by linarith [hxlarge])
    have hx_sq : x * x = (n : ℝ) ^ (2 * d) := by
      dsimp [x]
      calc
        (n : ℝ) ^ d * (n : ℝ) ^ d = ((n : ℝ) ^ d) ^ 2 := by ring
        _ = (n : ℝ) ^ (d * 2) :=
          (Real.rpow_mul_natCast (by positivity : 0 ≤ (n : ℝ)) d 2).symm
        _ = (n : ℝ) ^ (2 * d) := by congr 1 <;> ring
    have hsum : (x + 1) * x = (n : ℝ) ^ (2 * d) + x := by
      rw [add_mul, one_mul, hx_sq]
    rw [hsum] at hmul
    calc
      (s : ℝ) * (ell : ℝ) ≤ (n : ℝ) ^ (2 * d) + x := hmul
      _ ≤ root + root := by
        have h1 := hpow_2d.trans hpow_1_4_root
        have h2 := hpow_d.trans hpow_1_8_root
        linarith
      _ = 2 * root := by ring
  have hq_le : (q : ℝ) ≤ root + 1 := by
    dsimp [q, gQ]
    calc
      (Nat.ceil ((n : ℝ) ^ (4 * d)) : ℝ) ≤ (n : ℝ) ^ (4 * d) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      _ ≤ root + 1 := by linarith [hpow_4d]
  have hused_real : (s : ℝ) * (ell : ℝ) + (q : ℝ) + 1 ≤ (n : ℝ) := by
    calc
      (s : ℝ) * (ell : ℝ) + (q : ℝ) + 1 ≤ 3 * root + 2 := by linarith [hs_ell, hq_le]
      _ ≤ (3 / 16 : ℝ) * n + 2 := by nlinarith [hroot_small]
      _ ≤ n := by nlinarith [hnlargeR]
  have hused : s * ell + q + 1 ≤ n := by exact_mod_cast hused_real
  have hmul_succ (a : ℕ) : (a + 1) * ell = a * ell + ell := by
    rw [Nat.add_mul]
    simp
  let chunk : Fin s → Finset (Fin n) := fun r =>
    Finset.univ.image (fun i : Fin ell =>
      ⟨r.val * ell + i.val, by
        have hr : r.val + 1 ≤ s := Nat.succ_le_iff.mpr r.isLt
        have hr' : (r.val + 1) * ell ≤ s * ell := Nat.mul_le_mul_right ell hr
        have hri : r.val * ell + i.val < (r.val + 1) * ell := by
          rw [hmul_succ]
          omega
        have hs' : (r.val + 1) * ell + q + 1 ≤ n := by omega
        omega⟩)
  let aux : Finset (Fin n) :=
    Finset.univ.image (fun i : Fin q => ⟨s * ell + i.val, by omega⟩)
  have hchunk_inj (r : Fin s) :
      Function.Injective (fun i : Fin ell =>
        (⟨r.val * ell + i.val, by
          have hr : r.val + 1 ≤ s := Nat.succ_le_iff.mpr r.isLt
          have hr' : (r.val + 1) * ell ≤ s * ell := Nat.mul_le_mul_right ell hr
          have hri : r.val * ell + i.val < (r.val + 1) * ell := by
            rw [hmul_succ]
            omega
          have hs' : (r.val + 1) * ell + q + 1 ≤ n := by omega
          omega⟩ : Fin n)) := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp at hv
    omega
  have haux_inj :
      Function.Injective (fun i : Fin q => (⟨s * ell + i.val, by omega⟩ : Fin n)) := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp at hv
    omega
  have hchunk_mem (r : Fin s) (j : Fin n) :
      j ∈ chunk r ↔ r.val * ell ≤ j.val ∧ j.val < (r.val + 1) * ell := by
    constructor
    · intro hj
      rcases Finset.mem_image.mp hj with ⟨i, -, rfl⟩
      constructor
      · simp only [Fin.val_mk]
        omega
      · simp only [Fin.val_mk]
        rw [hmul_succ r.val]
        omega
    · intro hj
      rcases hj with ⟨hlo, hhi⟩
      have hhi' : j.val - r.val * ell < ell := by
        have hmul := hmul_succ r.val
        omega
      let i : Fin ell := ⟨j.val - r.val * ell, hhi'⟩
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      dsimp [i]
      omega
  have haux_mem (j : Fin n) :
      j ∈ aux ↔ s * ell ≤ j.val ∧ j.val < s * ell + q := by
    constructor
    · intro hj
      rcases Finset.mem_image.mp hj with ⟨i, -, rfl⟩
      constructor
      · simp only [Fin.val_mk]
        omega
      · simp only [Fin.val_mk]
        omega
    · intro hj
      rcases hj with ⟨hlo, hhi⟩
      have hi : j.val - s * ell < q := by omega
      let i : Fin q := ⟨j.val - s * ell, hi⟩
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      dsimp [i]
      omega
  have hchunks_card (r : Fin s) : (chunk r).card = ell := by
    dsimp [chunk]
    rw [Finset.card_image_of_injective _ (hchunk_inj r)]
    simp
  have haux_card : aux.card = q := by
    dsimp [aux]
    rw [Finset.card_image_of_injective _ haux_inj]
    simp
  have hchunks_disjoint : Pairwise fun r r' => Disjoint (chunk r) (chunk r') := by
    intro r r' hne
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have h1 := (hchunk_mem r j).mp hj
    have h2 := (hchunk_mem r' j).mp hj'
    have hrr : r.val ≠ r'.val := by
      intro heq
      exact hne (Fin.ext heq)
    rcases lt_or_gt_of_ne hrr with hlt | hgt
    · have hnext : r.val + 1 ≤ r'.val := by omega
      have hmul := Nat.mul_le_mul_right ell hnext
      omega
    · have hnext : r'.val + 1 ≤ r.val := by omega
      have hmul := Nat.mul_le_mul_right ell hnext
      omega
  have haux_disjoint : ∀ r, Disjoint aux (chunk r) := by
    intro r
    apply Finset.disjoint_left.mpr
    intro j hjA hjC
    have h1 := (haux_mem j).mp hjA
    have h2 := (hchunk_mem r j).mp hjC
    have hr : r.val + 1 ≤ s := Nat.succ_le_iff.mpr r.isLt
    have hmul := Nat.mul_le_mul_right ell hr
    omega
  let jres : Fin n := ⟨s * ell + q, by omega⟩
  have hres : ∃ j : Fin n, j ∉ aux ∧ ∀ r, j ∉ chunk r := by
    refine ⟨jres, ?_, ?_⟩
    · intro hj
      have h1 := (haux_mem jres).mp hj
      have hupper : s * ell + q < s * ell + q := by simpa [jres] using h1.2
      omega
    · intro r hj
      have h1 := (hchunk_mem r jres).mp hj
      have hupper : s * ell + q < (r.val + 1) * ell := by simpa [jres] using h1.2
      have hr : r.val + 1 ≤ s := Nat.succ_le_iff.mpr r.isLt
      have hmul := Nat.mul_le_mul_right ell hr
      omega
  have hell_pos : 0 < ell := by
    have h : (n : ℝ) ^ (d / 2) ≤ (ell : ℝ) := hell_ge
    exact_mod_cast (show (1 : ℝ) ≤ (ell : ℝ) by linarith [hrootlower, h])
  have hmass (r : Fin s) (b : Fin (ell + 1)) :
      (∑ k : Fin (ell + 1),
        if k = b then ((Nat.choose ell k.val : ℕ) : ℝ) / (2 : ℝ) ^ ell else 0) ≤
        2 * (n : ℝ) ^ (-(d / 4)) := by
    have hsum : (∑ k : Fin (ell + 1),
        if k = b then ((Nat.choose ell k.val : ℕ) : ℝ) / (2 : ℝ) ^ ell else 0) =
        ((Nat.choose ell b.val : ℕ) : ℝ) / (2 : ℝ) ^ ell := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro k hk hkb
        simp [hkb]
      · simp
    rw [hsum]
    have hatom := centralBinomialUpper ell hell_pos b.val (Nat.le_of_lt_succ b.isLt)
    have hsqrt : (n : ℝ) ^ (d / 4) ≤ Real.sqrt (ell : ℝ) := by
      have hle := Real.sqrt_le_sqrt hell_ge
      have hsqrt_pow : Real.sqrt ((n : ℝ) ^ (d / 2)) = (n : ℝ) ^ (d / 4) := by
        have hleft : Real.sqrt ((n : ℝ) ^ (d / 2)) ^ 2 = (n : ℝ) ^ (d / 2) :=
          Real.sq_sqrt (by positivity)
        have hright : ((n : ℝ) ^ (d / 4)) ^ 2 = (n : ℝ) ^ (d / 2) := by
          calc
            ((n : ℝ) ^ (d / 4)) ^ 2 = (n : ℝ) ^ ((d / 4) * 2) :=
              (Real.rpow_mul_natCast (by positivity : 0 ≤ (n : ℝ)) (d / 4) 2).symm
            _ = (n : ℝ) ^ (d / 2) := by congr 1 <;> ring
        apply (mul_self_inj_of_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)).mp
        rw [← sq, ← sq, hleft, hright]
      simpa [hsqrt_pow] using hle
    have hnfracpos : 0 < (n : ℝ) ^ (d / 4) := Real.rpow_pos_of_pos (by positivity) _
    have hrecip : 1 / Real.sqrt (ell : ℝ) ≤ 1 / (n : ℝ) ^ (d / 4) :=
      one_div_le_one_div_of_le hnfracpos hsqrt
    have hatom' : ((Nat.choose ell b.val : ℕ) : ℝ) / (2 : ℝ) ^ ell ≤
        2 / Real.sqrt (ell : ℝ) := by simpa using hatom
    calc
      ((Nat.choose ell b.val : ℕ) : ℝ) / (2 : ℝ) ^ ell ≤ 2 / Real.sqrt (ell : ℝ) := hatom'
      _ ≤ 2 * (1 / (n : ℝ) ^ (d / 4)) := by
        have hmul := mul_le_mul_of_nonneg_left hrecip (by norm_num : 0 ≤ (2 : ℝ))
        simpa [div_eq_mul_inv] using hmul
      _ = 2 * (n : ℝ) ^ (-(d / 4)) := by
        rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ))]
        simp [one_div]
  refine ⟨GridGeom.mk chunk aux hchunks_card hchunks_disjoint haux_card haux_disjoint hres
    (fun _ => ell + 1) (fun _ k => k) ?_ ?_ ?_⟩
  · intro r k k' hkk'
    exact hkk'
  · intro r b
    exact ⟨b, rfl⟩
  · intro r b
    simpa using hmass r b

namespace GridGeom

variable {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)

/-- Grid distance: the number of one-bin moves between two keys. -/
def keyDist (g h : Γ.Key) : ℕ := ∑ r, Nat.dist (g r : ℕ) (h r : ℕ)

/-- Auxiliary distance: Hamming distance of auxiliary words. -/
def auxDist (t t' : Γ.AuxWord) : ℕ := (Finset.univ.filter fun j => t j ≠ t' j).card

/-- Distance in the grid-times-auxiliary graph (07:250–253). -/
def cellDist (c c' : Γ.Cell) : ℕ := Γ.keyDist c.1 c'.1 + Γ.auxDist c.2 c'.2

/-- Keys within grid distance `R`. -/
def keyBall (g : Γ.Key) (R : ℕ) : Finset Γ.Key := Finset.univ.filter fun h => Γ.keyDist g h ≤ R

/-- Auxiliary words within auxiliary distance `R`. -/
def auxBall (t : Γ.AuxWord) (R : ℕ) : Finset Γ.AuxWord :=
  Finset.univ.filter fun t' => Γ.auxDist t t' ≤ R

/-- Cells within distance `R`. -/
def cellBall (c : Γ.Cell) (R : ℕ) : Finset Γ.Cell := Finset.univ.filter fun c' => Γ.cellDist c c' ≤ R

/-- `E(g)`: the keys obtained by one bin move in one coordinate (07:61–63). -/
def keyNbrs (g : Γ.Key) : Finset Γ.Key := Finset.univ.filter fun h => Γ.keyDist g h = 1

/-- The fixed order of the cross keys of `g`; it does not depend on the auxiliary word (07:85–86). -/
noncomputable def crossKeys (g : Γ.Key) : List Γ.Key := (Γ.keyNbrs g).toList

/-- The cross order with the key `h₀` last (07:85–87). -/
noncomputable def crossOrder (g h₀ : Γ.Key) : List Γ.Key := (Γ.crossKeys g).erase h₀ ++ [h₀]

/-- The auxiliary words at distance at most one, in a fixed order. -/
noncomputable def ownWords (t : Γ.AuxWord) : List Γ.AuxWord := (Γ.auxBall t 1).toList

/-- Cross names `W_{h,t}`, `h ∈ E(g)` (07:76). -/
noncomputable def crossNames (g : Γ.Key) (t : Γ.AuxWord) : List Γ.Cell :=
  (Γ.crossKeys g).map fun h => (h, t)

/-- Own names `W_{g,t'}`, `d_H(t,t') ≤ 1` (07:77). -/
noncomputable def ownNames (g : Γ.Key) (t : Γ.AuxWord) : List Γ.Cell :=
  (Γ.ownWords t).map fun t' => (g, t')

/-- All listed names of the odd cell `c`: the cross list followed by the own list. -/
noncomputable def fullNames (c : Γ.Cell) : List Γ.Cell := Γ.crossNames c.1 c.2 ++ Γ.ownNames c.1 c.2

/-- The `Binomial(ℓ, 1/2)` mass of bin `b` in chunk `r`. -/
noncomputable def binMass (r : Fin s) (b : Fin (Γ.bins r)) : ℝ :=
  ∑ k : Fin (ℓ + 1), if Γ.bin r k = b then ((Nat.choose ℓ k.val : ℕ) : ℝ) / (2 : ℝ) ^ ℓ else 0

/-- The product mass of a key: the fraction of chunk patterns reading it (07:65–66). -/
noncomputable def keyMass (g : Γ.Key) : ℝ := ∏ r, Γ.binMass r (g r)

end GridGeom

end HypercubeRamsey.S07
