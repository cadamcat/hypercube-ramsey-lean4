import HypercubeRamsey.S05.Experiment
import HypercubeRamsey.S05.Stages_p_s05_h

namespace HypercubeRamsey

open Classical
open Filter Real
open scoped Topology
open OAI.HypercubeRamsey

theorem FinProb.trimByFiniteFamily5 {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinProb Ω) (Bad : I → Ω → Prop) (ε : ℝ)
    (hε : 0 ≤ ε) (hbad : ∀ i, P.pr (Bad i) ≤ ε)
    (hcount : (Fintype.card I : ℝ) * ε < 1 / 2) :
    ∃ Q : FinProb Ω, (∀ ω, Q.w ω ≤ 2 * P.w ω) ∧
      ∀ ω, Q.w ω ≠ 0 → ∀ i, ¬ Bad i ω := by
  classical
  let bad : Ω → Prop := fun ω => ∃ i, Bad i ω
  let good : Ω → Prop := fun ω => ¬ bad ω
  have hbadUnion : P.pr bad ≤ ∑ i, P.pr (Bad i) := by
    simpa [bad] using FinProb.pr_exists_le_sum5 P Bad
  have hsum : (∑ i, P.pr (Bad i)) ≤ (Fintype.card I : ℝ) * ε := by
    calc
      (∑ i, P.pr (Bad i)) ≤ ∑ _i : I, ε := Finset.sum_le_sum fun i _ => hbad i
      _ = (Fintype.card I : ℝ) * ε := by simp
  have hprobBad : P.pr bad < 1 / 2 := by linarith
  have hprobGood : 1 / 2 < P.pr good := by
    have hcompl := FinProb.pr_compl5 P bad
    change 1 / 2 < P.pr (fun ω => ¬ bad ω)
    rw [hcompl]
    linarith
  have hpositive : 0 < P.pr good := lt_trans (by norm_num) hprobGood
  let Q : FinProb Ω := FinProb.cond P good hpositive
  refine ⟨Q, ?_, ?_⟩
  · intro ω
    by_cases hω : good ω
    · simp only [Q, FinProb.cond, if_pos hω]
      apply (div_le_iff₀ hpositive).2
      have htwo : 1 ≤ 2 * P.pr good := by linarith
      calc
        P.w ω = 1 * P.w ω := by ring
        _ ≤ (2 * P.pr good) * P.w ω :=
          mul_le_mul_of_nonneg_right htwo (P.nonneg ω)
        _ = 2 * P.w ω * P.pr good := by ring
    · simp [Q, FinProb.cond, hω, P.nonneg ω]
  · intro ω hω i
    by_contra hfail
    have hnot : ¬ good ω := by
      intro hg
      exact hg ⟨i, hfail⟩
    have hzero : Q.w ω = 0 := by simp [Q, FinProb.cond, hnot, good]
    exact hω hzero

theorem FinProb.pi_pr_singleton5 {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (P : I → FinProb Ω) (i : I) (A : Ω → Prop) (ω₀ : Ω) :
    (FinProb.pi P).pr (fun ω => A (ω i)) = (P i).pr A := by
  classical
  let f : (∀ j : I, Ω) → ℝ := fun ω => if A (ω i) then 1 else 0
  have hdep : FinProb.DependsOn f {i} := by
    intro ω ω' h
    have hi := h i (by simp)
    simp [f, hi]
  letI : Unique {j : I // j ∈ ({i} : Finset I)} := {
    default := ⟨i, Finset.mem_singleton_self i⟩
    uniq := by
      intro j
      apply Subtype.ext
      exact Finset.mem_singleton.mp j.property
  }
  let e : (∀ j : {j : I // j ∈ ({i} : Finset I)}, Ω) ≃ Ω := Equiv.piUnique (fun _ => Ω)
  have h := FinProb.pi_expect_depends P {i} f (fun _ => ω₀) hdep
  have hpr : (FinProb.pi P).pr (fun ω => A (ω i)) = (FinProb.pi P).expect f := by
    simp [FinProb.pr, FinProb.expect, FinProb.pi, f]
  rw [show (FinProb.pi P).pr (fun ω => A (ω i)) = (FinProb.pi P).expect f by
    exact hpr]
  rw [h]
  simp only [FinProb.expect, FinProb.pi]
  have hidx : (⟨i, Finset.mem_singleton_self i⟩ : {j : I // j ∈ ({i} : Finset I)}) = default :=
    Subsingleton.elim _ _
  simp only [f]
  simp only [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos (Finset.mem_singleton_self i), hidx,
    Fintype.prod_unique]
  simp only [mul_ite, mul_one, mul_zero]
  have hdefault : (default : {j : I // j ∈ ({i} : Finset I)}).1 = i := rfl
  simp_rw [hdefault]
  rw [FinProb.pr]
  simpa [e, Equiv.piUnique] using
    (Equiv.sum_comp e (fun y => if A y then (P i).w y else 0))

def binNeighborVal5 {n : ℕ} (w : Fin (n + 1)) (d : Fin 3) : Fin (n + 1) :=
  if d.val = 0 then
    ⟨w.val - 1, Nat.lt_succ_of_le
      (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt_succ w.isLt))⟩
  else if d.val = 1 then w
  else
    ⟨min n (w.val + 1), Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩

theorem exists_binNeighborVal5 {n : ℕ} (w z : Fin (n + 1))
    (hnear₁ : w.val ≤ z.val + 1) (hnear₂ : z.val ≤ w.val + 1) :
    ∃ d : Fin 3, z = binNeighborVal5 w d := by
  have hcases : z.val = w.val ∨ z.val + 1 = w.val ∨ z.val = w.val + 1 := by omega
  rcases hcases with h | h | h
  · refine ⟨⟨1, by omega⟩, ?_⟩
    apply Fin.ext
    simp [binNeighborVal5, h]
  · refine ⟨⟨0, by omega⟩, ?_⟩
    apply Fin.ext
    simp [binNeighborVal5, h]
    omega
  · refine ⟨⟨2, by omega⟩, ?_⟩
    apply Fin.ext
    change z.val = min n (w.val + 1)
    rw [h]
    rw [Nat.min_eq_right (by omega : w.val + 1 ≤ n)]

def binNeighborVals5 {n : ℕ} (w : BinVector5 n) (i : Fin coarseChunkCount5) : Finset (Fin (n + 1)) :=
  Finset.univ.image (binNeighborVal5 (w i))

def nearBinVectors5 {n : ℕ} (w : BinVector5 n) : Finset (BinVector5 n) :=
  (Finset.univ.pi (binNeighborVals5 w)).image
    (fun f : ∀ i : Fin coarseChunkCount5, i ∈ Finset.univ → Fin (n + 1) =>
      fun i => f i (Finset.mem_univ i))

theorem binNeighborVals5_card_le {n : ℕ} (w : BinVector5 n) (i : Fin coarseChunkCount5) :
    (binNeighborVals5 w i).card ≤ 3 := by
  unfold binNeighborVals5
  calc
    (Finset.univ.image (binNeighborVal5 (w i))).card ≤ Finset.univ.card := Finset.card_image_le
    _ = 3 := by simp

set_option maxHeartbeats 0 in
theorem nearBinVectors5_card_le {n : ℕ} (w : BinVector5 n) :
    (nearBinVectors5 w).card ≤ 3 ^ coarseChunkCount5 := by
  unfold nearBinVectors5
  calc
    _ ≤ (Finset.univ.pi (binNeighborVals5 w)).card := Finset.card_image_le
    _ = ∏ i ∈ (Finset.univ : Finset (Fin coarseChunkCount5)), (binNeighborVals5 w i).card := by simp
    _ ≤ ∏ _i ∈ (Finset.univ : Finset (Fin coarseChunkCount5)), 3 := by
      apply Finset.prod_le_prod
      intro i hi
      exact binNeighborVals5_card_le w i
    _ = 3 ^ coarseChunkCount5 := by simp

def nearCoarseKeys5 {n : ℕ} (w : BinVector5 n) : Finset (CoarseKey5 n) :=
  (nearBinVectors5 w).product Finset.univ

theorem nearCoarseKeys5_card_le {n : ℕ} (w : BinVector5 n) :
    (nearCoarseKeys5 w).card ≤ 2 * 3 ^ coarseChunkCount5 := by
  unfold nearCoarseKeys5
  calc
    _ = (nearBinVectors5 w).card * (Finset.univ : Finset Bool).card := by simp
    _ ≤ 3 ^ coarseChunkCount5 * 2 := Nat.mul_le_mul_right 2 (nearBinVectors5_card_le w)
    _ = 2 * 3 ^ coarseChunkCount5 := by omega

theorem Fintype.card_subsets_le5 {α : Type*} [Fintype α] [DecidableEq α] (C : Finset α) :
    Fintype.card {S : Finset α // S ⊆ C} ≤ 2 ^ C.card := by
  classical
  let code : {S : Finset α // S ⊆ C} → Finset {x // x ∈ C} :=
    fun S => C.attach.filter fun x => x.1 ∈ S.1
  have hcode : Function.Injective code := by
    intro S T hST
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ C
    · have hmem : (⟨x, hx⟩ : {x // x ∈ C}) ∈ code S ↔
          (⟨x, hx⟩ : {x // x ∈ C}) ∈ code T := by rw [hST]
      simpa [code] using hmem
    · have hS : x ∉ S.1 := fun h => hx (S.2 h)
      have hT : x ∉ T.1 := fun h => hx (T.2 h)
      simp [hS, hT]
  calc
    Fintype.card {S : Finset α // S ⊆ C} ≤ Fintype.card (Finset {x // x ∈ C}) :=
      Fintype.card_le_of_injective code hcode
    _ = 2 ^ C.card := by simp

theorem Params5.tendsto_uStarSeg_atTop5 {γ K' χ : ℝ} (p : Params5 γ K' χ) :
    Tendsto (fun n => (p.uStarSeg n : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ p.alpha) atTop atTop :=
    (tendsto_rpow_atTop p.halpha.1).comp tendsto_natCast_atTop_atTop
  have hmle (n : ℕ) : (n : ℝ) ^ p.alpha ≤ (p.m n : ℝ) := by
    dsimp [Params5.m]
    exact Nat.le_ceil _
  have hm : Tendsto (fun n => (p.m n : ℝ)) atTop atTop := tendsto_atTop_mono hmle hpow
  have hlog : Tendsto (fun n => Real.log (p.m n : ℝ)) atTop atTop := tendsto_log_atTop.comp hm
  have hcoef : 0 < p.eta / (p.q0 : ℝ) := div_pos p.heta.1 (by exact_mod_cast p.hq0.1)
  have hraw : Tendsto (fun n => p.eta * Real.log (p.m n : ℝ) / (p.q0 : ℝ)) atTop atTop := by
    have h := hlog.const_mul_atTop hcoef
    convert h using 1 <;> ext n <;> ring
  refine tendsto_atTop_mono ?_ hraw
  intro n
  change p.eta * Real.log (p.m n : ℝ) / (p.q0 : ℝ) ≤ (p.uStarSeg n : ℝ)
  dsimp [Params5.uStarSeg]
  exact Nat.le_ceil _

theorem Params5.tendsto_optTestEps5 {γ K' χ : ℝ} (p : Params5 γ K' χ) :
    Tendsto (fun n => Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 8)) atTop (𝓝 0) := by
  have hq : (0 : ℝ) < p.q0 := by exact_mod_cast p.hq0.1
  have hcoef : 0 < p.delta * (p.q0 : ℝ) / 8 := div_pos (mul_pos p.hdelta.1 hq) (by norm_num)
  have hlin : Tendsto (fun n => (p.delta * (p.q0 : ℝ) / 8) * (p.uStarSeg n : ℝ)) atTop atTop :=
    (p.tendsto_uStarSeg_atTop5).const_mul_atTop hcoef
  have h := tendsto_exp_neg_atTop_nhds_zero.comp hlin
  refine h.congr' ?_
  filter_upwards with n
  apply congrArg Real.exp
  push_cast
  ring

theorem mem_nearBinVectors5_of_coords {n : ℕ} (w z : BinVector5 n)
    (hz : ∀ i, z i ∈ binNeighborVals5 w i) : z ∈ nearBinVectors5 w := by
  classical
  unfold nearBinVectors5
  apply Finset.mem_image.mpr
  refine ⟨(fun i (_hi : i ∈ Finset.univ) => z i), ?_, ?_⟩
  · simp only [Finset.mem_pi]
    intro i hi
    exact hz i
  · rfl

theorem binVector_self_mem_neighborVals5 {n : ℕ} (w : BinVector5 n) (i : Fin coarseChunkCount5) :
    w i ∈ binNeighborVals5 w i := by
  unfold binNeighborVals5
  apply Finset.mem_image.mpr
  refine ⟨1, Finset.mem_univ _, ?_⟩
  simp [binNeighborVal5]

theorem binVector_self_mem_near5 {n : ℕ} (w : BinVector5 n) : w ∈ nearBinVectors5 w :=
  mem_nearBinVectors5_of_coords w w (fun i => binVector_self_mem_neighborVals5 w i)
namespace ChunkGeometry5

variable {n m : ℕ} (g : ChunkGeometry5 n m)

theorem coarseCount_flip_in_chunk (x : CubeVertex n) (a : Fin n) (i : Fin coarseChunkCount5)
    (ha : a ∈ g.coarseChunks i) :
    g.coarseCount (flipVertex5 x a) i =
      if x a then g.coarseCount x i - 1 else g.coarseCount x i + 1 := by
  classical
  unfold coarseCount
  by_cases hxa : x a
  · have hmem : a ∈ (g.coarseChunks i).filter (fun b => x b = true) := by
      simp [ha, hxa]
    have hfilter :
        (g.coarseChunks i).filter (fun b => flipVertex5 x a b = true) =
          ((g.coarseChunks i).filter (fun b => x b = true)).erase a := by
      ext b
      by_cases hba : b = a
      · subst b
        simp [ha, hxa, flipVertex5]
      · have hflip : flipVertex5 x a b = x b := by
          unfold flipVertex5
          rw [Function.update_of_ne hba]
        simp [hflip, hba]
    rw [hfilter, Finset.card_erase_of_mem hmem]
    simp [hxa]
  · have hmem : a ∉ (g.coarseChunks i).filter (fun b => x b = true) := by
      simp [hxa]
    have hfilter :
        (g.coarseChunks i).filter (fun b => flipVertex5 x a b = true) =
          insert a ((g.coarseChunks i).filter (fun b => x b = true)) := by
      ext b
      by_cases hba : b = a
      · subst b
        simp [ha, hxa, flipVertex5]
      · have hflip : flipVertex5 x a b = x b := by
          unfold flipVertex5
          rw [Function.update_of_ne hba]
        simp [hflip, hba]
    rw [hfilter, Finset.card_insert_of_notMem hmem]
    simp [hxa]

theorem coarseCount_flip_outside_chunk (x : CubeVertex n) (a : Fin n) (i : Fin coarseChunkCount5)
    (ha : a ∉ g.coarseChunks i) :
    g.coarseCount (flipVertex5 x a) i = g.coarseCount x i := by
  classical
  unfold coarseCount
  congr 1
  ext b
  by_cases hba : b = a
  · subst b
    simp [ha]
  · have hba' : b ≠ a := hba
    have hflip : flipVertex5 x a b = x b := by
      unfold flipVertex5
      rw [Function.update_of_ne hba']
    simp [hflip]

theorem coarseBin_flip_in_chunk (x : CubeVertex n) (a : Fin n) (i : Fin coarseChunkCount5)
    (ha : a ∈ g.coarseChunks i) :
    g.coarseBin (flipVertex5 x a) =
      Function.update (g.coarseBin x) i
        (g.bin i (if x a then g.coarseCount x i - 1 else g.coarseCount x i + 1)) := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    simp only [coarseBin, Function.update_self]
    rw [coarseCount_flip_in_chunk g x a i ha]
  · have hai : a ∉ g.coarseChunks j := by
      intro haj
      have hdis := Finset.disjoint_left.mp (g.chunks_disjoint.1 j i hji)
      exact hdis haj ha
    change g.bin j (g.coarseCount (flipVertex5 x a) j) =
      (Function.update (fun k => g.bin k (g.coarseCount x k)) i
        (g.bin i (if x a then g.coarseCount x i - 1 else g.coarseCount x i + 1))) j
    rw [coarseCount_flip_outside_chunk g x a j hai, Function.update_of_ne hji]

theorem flippedBinValue_mem_neighborVals (x : CubeVertex n) (a : Fin n) (i : Fin coarseChunkCount5)
    (ha : a ∈ g.coarseChunks i) :
    g.bin i (if x a then g.coarseCount x i - 1 else g.coarseCount x i + 1) ∈
      binNeighborVals5 (g.coarseBin x) i := by
  classical
  by_cases hxa : x a = true
  · have hcpos : 0 < g.coarseCount x i := by
      unfold coarseCount
      apply Finset.card_pos.mpr
      exact ⟨a, Finset.mem_filter.mpr ⟨ha, hxa⟩⟩
    let w := g.coarseBin x i
    let z := g.bin i (g.coarseCount x i - 1)
    have hmono := g.bin_monotone i (g.coarseCount x i - 1) (g.coarseCount x i)
      (Nat.sub_le _ _)
    have hcon := g.bin_consecutive i (g.coarseCount x i - 1)
    have hadd : (g.coarseCount x i - 1) + 1 = g.coarseCount x i := Nat.sub_add_cancel hcpos
    rw [hadd] at hcon
    have hnear₁ : w.val ≤ z.val + 1 := by dsimp [w, z, ChunkGeometry5.coarseBin] at *; omega
    have hnear₂ : z.val ≤ w.val + 1 := by dsimp [w, z, ChunkGeometry5.coarseBin] at *; omega
    obtain ⟨d, hd⟩ := exists_binNeighborVal5 w z hnear₁ hnear₂
    unfold binNeighborVals5
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, by simpa [w, z, hxa] using hd.symm⟩
  · have hxa' : x a = false := by cases h : x a <;> simp_all
    let w := g.coarseBin x i
    let z := g.bin i (g.coarseCount x i + 1)
    have hmono := g.bin_monotone i (g.coarseCount x i) (g.coarseCount x i + 1) (by omega)
    have hcon := g.bin_consecutive i (g.coarseCount x i)
    have hnear₁ : w.val ≤ z.val + 1 := by dsimp [w, z, ChunkGeometry5.coarseBin] at *; omega
    have hnear₂ : z.val ≤ w.val + 1 := by dsimp [w, z, ChunkGeometry5.coarseBin] at *; omega
    obtain ⟨d, hd⟩ := exists_binNeighborVal5 w z hnear₁ hnear₂
    unfold binNeighborVals5
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, by simpa [w, z, hxa'] using hd.symm⟩

theorem flippedCoarseBin_mem_near5 (x : CubeVertex n) (a : Fin n) (i : Fin coarseChunkCount5)
    (ha : a ∈ g.coarseChunks i) :
    g.coarseBin (flipVertex5 x a) ∈ nearBinVectors5 (g.coarseBin x) := by
  apply mem_nearBinVectors5_of_coords
  intro j
  rw [coarseBin_flip_in_chunk g x a i ha]
  by_cases hji : j = i
  · subst j
    rw [Function.update_self]
    exact flippedBinValue_mem_neighborVals g x a i ha
  · rw [Function.update_of_ne hji]
    exact binVector_self_mem_neighborVals5 (g.coarseBin x) j

theorem coarseRange_subset_nearKeys5 (x : CubeVertex n) :
    g.coarseRange x ⊆ nearCoarseKeys5 (g.coarseBin x) := by
  classical
  unfold nearCoarseKeys5
  intro q hq
  unfold ChunkGeometry5.coarseRange at hq
  rcases Finset.mem_insert.mp hq with hbase | hflip
  · subst q
    have hvec := binVector_self_mem_near5 (g.coarseBin x)
    simpa [ChunkGeometry5.key] using
      (Finset.mem_product.mpr ⟨hvec, Finset.mem_univ (decide (g.boundary x))⟩ :
        g.key x ∈ nearCoarseKeys5 (g.coarseBin x))
  · rcases Finset.mem_image.mp hflip with ⟨a, ha, rfl⟩
    change a ∈ Finset.univ.biUnion g.coarseChunks at ha
    rcases Finset.mem_biUnion.mp ha with ⟨i, hi, hai⟩
    have hvec := flippedCoarseBin_mem_near5 g x a i hai
    simpa [ChunkGeometry5.key] using
      (Finset.mem_product.mpr ⟨hvec, Finset.mem_univ (decide (g.boundary (flipVertex5 x a)))⟩ :
        g.key (flipVertex5 x a) ∈ nearCoarseKeys5 (g.coarseBin x))

theorem coarseRange_card_le (x : CubeVertex n) :
    (g.coarseRange x).card ≤ coarseChunkCount5 * 4 + 1 := by
  classical
  let flipKey : Fin n → CoarseKey5 n := fun a => g.key (flipVertex5 x a)
  let chunkImage : Fin coarseChunkCount5 → Finset (CoarseKey5 n) :=
    fun i => (g.coarseChunks i).image flipKey
  have hchunk (i : Fin coarseChunkCount5) : (chunkImage i).card ≤ 4 := by
    let nextBin (b : Bool) : BinVector5 n :=
      Function.update (g.coarseBin x) i
        (g.bin i (if b then g.coarseCount x i - 1 else g.coarseCount x i + 1))
    let encode (z : Bool × Bool) : CoarseKey5 n := (nextBin z.1, z.2)
    let candidates : Finset (CoarseKey5 n) := Finset.univ.image encode
    have hsubset : chunkImage i ⊆ candidates := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨a, ha, rfl⟩
      have hkey : flipKey a = encode (x a, decide (g.boundary (flipVertex5 x a))) := by
        dsimp [flipKey, encode, nextBin]
        simp only [ChunkGeometry5.key]
        rw [coarseBin_flip_in_chunk g x a i ha]
      exact Finset.mem_image.mpr ⟨(x a, decide (g.boundary (flipVertex5 x a))),
        Finset.mem_univ _, hkey.symm⟩
    calc
      (chunkImage i).card ≤ candidates.card := Finset.card_le_card hsubset
      _ ≤ (Finset.univ : Finset (Bool × Bool)).card := Finset.card_image_le
      _ = 4 := by simp
  let allImages : Finset (CoarseKey5 n) := Finset.univ.biUnion chunkImage
  have himage_subset : (g.coarseCoords.image flipKey) ⊆ allImages := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨a, ha, rfl⟩
    change a ∈ Finset.univ.biUnion g.coarseChunks at ha
    rcases Finset.mem_biUnion.mp ha with ⟨i, hi, hai⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨a, hai, rfl⟩⟩
  have hallImages : allImages.card ≤ coarseChunkCount5 * 4 := by
    calc
      allImages.card ≤ ∑ i : Fin coarseChunkCount5, (chunkImage i).card := by
        exact Finset.card_biUnion_le (s := Finset.univ) (t := chunkImage)
      _ ≤ ∑ _i : Fin coarseChunkCount5, 4 := Finset.sum_le_sum fun i _ => hchunk i
      _ = coarseChunkCount5 * 4 := by simp
  have himage : (g.coarseCoords.image flipKey).card ≤ coarseChunkCount5 * 4 :=
    (Finset.card_le_card himage_subset).trans hallImages
  rw [ChunkGeometry5.coarseRange]
  by_cases hk : g.key x ∈ g.coarseCoords.image flipKey
  · rw [Finset.insert_eq_of_mem hk]
    omega
  · rw [Finset.card_insert_of_notMem hk]
    omega

end ChunkGeometry5

namespace Setup5

theorem step1Fail_irrel_sign5 {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (b : X.Base) (ℓ ℓ' : X.Key)
    (w : BinVector5 n) (k : ℕ) (hcoarse : ℓ.coarse = ℓ'.coarse) (hlevel : ℓ.level = ℓ'.level) :
    X.step1Fail b ℓ w k ↔ X.step1Fail b ℓ' w k := by
  have hweight : ∀ y, X.colWeight b ℓ b.2.2 (fun _ _ => True) y =
      X.colWeight b ℓ' b.2.2 (fun _ _ => True) y := by
    intro y
    simp [Setup5.colWeight, hcoarse, hlevel]
  have hweightDel : ∀ y, X.colWeight b ℓ b.2.2
      (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k)) y =
        X.colWeight b ℓ' b.2.2 (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k)) y := by
    intro y
    simp [Setup5.colWeight, hcoarse, hlevel]
  have hprior : ∀ y, (X.prior b ℓ).w y = (X.prior b ℓ').w y := by
    intro y
    have hLaw : X.prior b ℓ = X.prior b ℓ' := by
      simpa only [Setup5.prior] using congrArg (fun f => normalize5 f X.y₀) (funext hweight)
    exact congrArg (fun L : Law N => L.w y) hLaw
  have hpriorDel : ∀ y, (X.priorDel b ℓ w k).w y = (X.priorDel b ℓ' w k).w y := by
    intro y
    have hLaw : X.priorDel b ℓ w k = X.priorDel b ℓ' w k := by
      simpa only [Setup5.priorDel] using congrArg (fun f => normalize5 f X.y₀) (funext hweightDel)
    exact congrArg (fun L : Law N => L.w y) hLaw
  simp only [Setup5.step1Fail]
  simp_rw [hprior, hpriorDel]

theorem capFail_irrel_sign5 {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (b : X.Base) (ℓ ℓ' : X.Key)
    (hcoarse : ℓ.coarse = ℓ'.coarse) (hlevel : ℓ.level = ℓ'.level) :
    X.capFail b ℓ ↔ X.capFail b ℓ' := by
  have hweight : ∀ y, X.colWeight b ℓ b.2.2 (fun _ _ => True) y =
      X.colWeight b ℓ' b.2.2 (fun _ _ => True) y := by
    intro y
    simp [Setup5.colWeight, hcoarse, hlevel]
  have hprior : ∀ y, (X.prior b ℓ).w y = (X.prior b ℓ').w y := by
    intro y
    have hLaw : X.prior b ℓ = X.prior b ℓ' := by
      simpa only [Setup5.prior] using congrArg (fun f => normalize5 f X.y₀) (funext hweight)
    exact congrArg (fun L : Law N => L.w y) hLaw
  simp only [Setup5.capFail, hlevel]
  simp_rw [hprior]

theorem blockMass_ext5 {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (H H' : X.KeyHist) (K : X.Ty)
    (S : Finset X.Key) (hbase : H.1 = H'.1)
    (hcols : ∀ ℓ ∈ S, H.2 ℓ = H'.2 ℓ) :
    X.blockMass H K S = X.blockMass H' K S := by
  classical
  unfold blockMass
  apply Finset.sum_congr rfl
  intro z hz
  unfold blockWeight
  rw [hbase]
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  rw [hcols ℓ hℓ]

theorem optOccurs_high_type_keys_near5 {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G) (K : X.Ty) (t : CubeVertex (X.p.m n))
    (hOpt : X.OptOccurs K t) :
    K.2.2 = none ∧ (∀ ℓ ∈ K.2.1, ∃ i, ℓ = .inr i) ∧
      K.2.1 ⊆ (nearCoarseKeys5 K.1.1).image (fun i => (.inr i : X.Key)) := by
  classical
  rcases hOpt with ⟨x, hEven, hType, hOptional⟩
  have hsev : X.g.severity x = X.p.J n + 1 := by
    by_contra hn
    simp [ChunkGeometry5.optionalKey, hn] at hOptional
  have hnot : ¬ X.g.severity x ≤ X.p.J n := by omega
  have hnone : K.2.2 = none := by
    rw [← hType]
    simp [ChunkGeometry5.evenType, hnot]
  have hbin : K.1.1 = X.g.coarseBin x := by
    rw [← hType]
    simp [ChunkGeometry5.evenType, ChunkGeometry5.key]
  have hkeys : K.2.1 = (X.g.coarseRange x).image (fun i => (.inr i : X.Key)) := by
    rw [← hType]
    simp [ChunkGeometry5.evenType, ChunkGeometry5.typeKeys, hnot]
  refine ⟨hnone, ?_, ?_⟩
  · rw [hkeys]
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨i, hi, rfl⟩
    exact ⟨i, rfl⟩
  · rw [hkeys, hbin]
    exact Finset.image_subset_image (X.g.coarseRange_subset_nearKeys5 x)

theorem optPatternCount_le5 {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} (X : Setup5 γ K' χ n N E G)
    (k : CoarseKey5 n × CubeVertex (X.p.m n) × Fin (X.p.J n + 1)) :
    (F : Fintype {K : X.Ty // X.OptOccurs K k.2.1 ∧ X.optKeyOf K k.2.1 = .inl k}) →
    (@Fintype.card _ F : ℝ) ≤ Real.rpow 2 ((2 * 3 ^ coarseChunkCount5 : ℕ) : ℝ) := by
  classical
  let C : Finset X.Key := (nearCoarseKeys5 k.1.1).image fun i => (.inr i)
  let I := {K : X.Ty // X.OptOccurs K k.2.1 ∧ X.optKeyOf K k.2.1 = .inl k}
  intro fI
  letI : Fintype I := fI
  let SType := {S : Finset X.Key // S ⊆ C}
  letI : Fintype SType := Subtype.fintype _
  have hsubset (q : I) : q.1.2.1 ⊆ C := by
    have hFacts := X.optOccurs_high_type_keys_near5 q.1 k.2.1 q.2.1
    have hcoarse : q.1.1 = k.1 := by
      have h := q.2.2
      simp [Setup5.optKeyOf] at h
      exact congrArg Prod.fst h
    simpa [C, hcoarse] using hFacts.2.2
  let code : I → {S : Finset X.Key // S ⊆ C} := fun q => ⟨q.1.2.1, hsubset q⟩
  have hcode : Function.Injective code := by
    intro q r hqr
    apply Subtype.ext
    have hS : q.1.2.1 = r.1.2.1 := congrArg Subtype.val hqr
    have hcoarseQ : q.1.1 = k.1 := by
      have h := q.2.2
      simp [Setup5.optKeyOf] at h
      exact congrArg Prod.fst h
    have hcoarseR : r.1.1 = k.1 := by
      have h := r.2.2
      simp [Setup5.optKeyOf] at h
      exact congrArg Prod.fst h
    have hnoneQ : q.1.2.2 = none := (X.optOccurs_high_type_keys_near5 q.1 k.2.1 q.2.1).1
    have hnoneR : r.1.2.2 = none := (X.optOccurs_high_type_keys_near5 r.1 k.2.1 r.2.1).1
    exact Prod.ext (hcoarseQ.trans hcoarseR.symm)
      (Prod.ext hS (hnoneQ.trans hnoneR.symm))
  have hcardI : Fintype.card I ≤ 2 ^ C.card := by
    exact (Fintype.card_le_of_injective code hcode).trans (Fintype.card_subsets_le5 C)
  have hC : C.card ≤ 2 * 3 ^ coarseChunkCount5 := by
    dsimp [C]
    exact (Finset.card_image_le.trans (nearCoarseKeys5_card_le k.1.1))
  have hcardReal : (Fintype.card I : ℝ) ≤ Real.rpow 2 (C.card : ℝ) := by
    calc
      (Fintype.card I : ℝ) ≤ ((2 ^ C.card : ℕ) : ℝ) := by exact_mod_cast hcardI
      _ = (2 : ℝ) ^ C.card := by norm_cast
      _ = Real.rpow 2 (C.card : ℝ) := (Real.rpow_natCast 2 C.card).symm
  have hCcast : (C.card : ℝ) ≤ (2 * 3 ^ coarseChunkCount5 : ℕ) := by exact_mod_cast hC
  calc
    (Fintype.card I : ℝ) ≤ Real.rpow 2 (C.card : ℝ) := hcardReal
    _ ≤ Real.rpow 2 ((2 * 3 ^ coarseChunkCount5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hCcast

end Setup5

end HypercubeRamsey
