import HypercubeRamsey.S05.Even_setup_records_sol_s05_even
import HypercubeRamsey.Tools.CubeGeometry

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical OAI.HypercubeRamsey
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem hammingDist_restrict_le {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (f : J → I) (hf : Function.Injective f) (x y : I → Bool) :
    _root_.hammingDist (x ∘ f) (y ∘ f) ≤ _root_.hammingDist x y := by
  classical
  have hsub : (Finset.univ.filter (fun j : J => x (f j) ≠ y (f j))).image f ⊆
      Finset.univ.filter (fun i : I => x i ≠ y i) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf] at hcard
  exact hcard

def residualVertex (v : CubeVertex n) : X.g.residual → Bool := fun a => v a.1

def residualLocation {h : X.HeightChoice5} (l : h.hp.Loc) : X.g.residual → Bool :=
  fun a => l.1 (X.St.resCoord a)

theorem residualDist_eq (v w : CubeVertex n) :
    X.g.residualDist v w = _root_.hammingDist (residualVertex X v) (residualVertex X w) := by
  let e : {a : X.g.residual // v a.1 ≠ w a.1} ≃
      (X.g.residual.filter fun a => v a ≠ w a) :=
    { toFun a := ⟨a.1.1, Finset.mem_filter.mpr ⟨a.1.2, a.2⟩⟩
      invFun a := ⟨⟨a.1, (Finset.mem_filter.mp a.2).1⟩, (Finset.mem_filter.mp a.2).2⟩
      left_inv a := rfl
      right_inv a := rfl }
  have he := (Fintype.card_congr e).symm
  simp only [Fintype.card_coe] at he
  simp only [Fintype.card_subtype] at he
  exact he

def residualScope {h : X.HeightChoice5} (v : CubeVertex n) (R : ℕ) : Finset h.hp.Loc :=
  Finset.univ.filter fun l => _root_.hammingDist (residualLocation X l) (residualVertex X v) ≤ R

theorem scopeBall_subset_residual {h : X.HeightChoice5} (v : CubeVertex n) (R : ℕ) :
    X.scopeBall (h := h) v R ⊆ residualScope X (h := h) v R := by
  intro l hl
  have hd := (Finset.mem_filter.mp hl).2
  change _root_.hammingDist l.1 (X.St.oneHot (X.St.stateOf v)) ≤ R at hd
  have hr := hammingDist_restrict_le X.St.resCoord X.St.resCoord_injective l.1
    (X.St.oneHot (X.St.stateOf v))
  have heq : (X.St.oneHot (X.St.stateOf v) ∘ X.St.resCoord) = residualVertex X v := by
    funext a
    exact X.St.oneHot_residual v a
  rw [heq] at hr
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.trans hd⟩

theorem adjacent_residualDist (v w : CubeVertex n) (hadj : (cube n).Adj v w) :
    X.g.residualDist v w ≤ 1 := by
  rw [residualDist_eq]
  have hh := hammingDist_restrict_le (fun a : X.g.residual => a.1) Subtype.val_injective v w
  change _root_.hammingDist v w = 1 at hadj
  exact hh.trans_eq hadj

theorem odd_scope_subset_residual {h : X.HeightChoice5} (v : EvenRole5 n) (b : OddRole5 n)
    (hadj : (cube n).Adj v.1 b.1) (R : ℕ) :
    X.scopeBall (h := h) b.1 R ⊆ residualScope X (h := h) v.1 (R + 1) := by
  intro l hl
  have hr := (Finset.mem_filter.mp (scopeBall_subset_residual X b.1 R hl)).2
  have ha := adjacent_residualDist X v.1 b.1 hadj
  rw [residualDist_eq] at ha
  rw [_root_.hammingDist_comm (residualVertex X v.1)] at ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact (_root_.hammingDist_triangle (residualLocation X l) (residualVertex X b.1) (residualVertex X v.1)).trans
    (Nat.add_le_add hr ha)

theorem residualScopes_disjoint {h : X.HeightChoice5} (v w : CubeVertex n) (R S : ℕ)
    (hfar : R + S < X.g.residualDist v w) :
    Disjoint (residualScope X (h := h) v R) (residualScope X (h := h) w S) := by
  apply Finset.disjoint_left.mpr
  intro l hlv hlw
  have hv := (Finset.mem_filter.mp hlv).2
  have hw := (Finset.mem_filter.mp hlw).2
  have htri := _root_.hammingDist_triangle_left (residualVertex X v) (residualVertex X w) (residualLocation X l)
  rw [← residualDist_eq] at htri
  exact (Nat.not_le_of_lt hfar) (htri.trans (Nat.add_le_add hv hw))

theorem residual_complement_card :
    (((Finset.univ \ X.g.residual).card : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hsub : Finset.univ \ X.g.residual ⊆
      (Finset.univ.biUnion X.g.coarseChunks) ∪ (Finset.univ.biUnion X.g.fineChunks) := by
    intro a ha
    have hfull : a ∈ Finset.univ := Finset.mem_univ _
    rw [← X.g.chunks_cover] at hfull
    rcases Finset.mem_union.mp hfull with hocc | hres
    · exact hocc
    · exact ((Finset.mem_sdiff.mp ha).2 hres).elim
  have hcard := Finset.card_le_card hsub
  exact (by exact_mod_cast hcard : (((Finset.univ \ X.g.residual).card : ℕ) : ℝ) ≤
    (((Finset.univ.biUnion X.g.coarseChunks) ∪ (Finset.univ.biUnion X.g.fineChunks)).card : ℝ)).trans
      X.g.occupied_sublinear

theorem ambientDist_le_residual_add (v w : CubeVertex n) :
    _root_.hammingDist v w ≤ X.g.residualDist v w + (Finset.univ \ X.g.residual).card := by
  let D := Finset.univ.filter fun i : Fin n => v i ≠ w i
  have hsplit := Finset.card_filter_add_card_filter_not (s := D) (p := fun i => i ∈ X.g.residual)
  have hres : (D.filter fun i => i ∈ X.g.residual).card = X.g.residualDist v w := by
    apply congrArg Finset.card
    ext i
    simp [D, ChunkGeometry5.residualDist, and_comm]
  have hother : (D.filter fun i => i ∉ X.g.residual).card ≤ (Finset.univ \ X.g.residual).card :=
    Finset.card_le_card (by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
  change D.card ≤ _
  omega

def evenNear (v : EvenRole5 n) (R : ℕ) : Finset (EvenRole5 n) :=
  Finset.univ.filter fun w => X.g.residualDist v.1 w.1 ≤ R

theorem evenNear_self (v : EvenRole5 n) (R : ℕ) : v ∈ evenNear X v R := by
  simp [evenNear, ChunkGeometry5.residualDist]

theorem evenNear_card (v : EvenRole5 n) (R : ℕ) :
    (evenNear X v R).card ≤ (hammingBall v.1 (R + (Finset.univ \ X.g.residual).card)).card := by
  have hsub : (evenNear X v R).image (fun w => w.1) ⊆
      hammingBall v.1 (R + (Finset.univ \ X.g.residual).card) := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    have hd := ambientDist_le_residual_add X v.1 u.1
    have hnear := (Finset.mem_filter.mp hu).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd.trans (Nat.add_le_add_right hnear _)⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem evenNear_entropy_bound (v : EvenRole5 n) (R : ℕ) (t : ℝ) (hn : 0 < n)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hR : ((R + (Finset.univ \ X.g.residual).card : ℕ) : ℝ) / n ≤ t)
    (hRn : R + (Finset.univ \ X.g.residual).card ≤ n / 2) :
    ((evenNear X v R).card : ℝ) ≤ Real.exp (Real.binEntropy t * n) := by
  have hball := hammingBall_volume_bound hn hRn v.1
  have hq0 : 0 ≤ ((R + (Finset.univ \ X.g.residual).card : ℕ) : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hent : Real.binEntropy (((R + (Finset.univ \ X.g.residual).card : ℕ) : ℝ) / n) ≤ Real.binEntropy t :=
    Real.binEntropy_strictMonoOn.monotoneOn ⟨hq0, by simpa using hR.trans ht⟩ ⟨ht0, by simpa using ht⟩ hR
  exact (by exact_mod_cast evenNear_card X v R : ((evenNear X v R).card : ℝ) ≤
    (hammingBall v.1 (R + (Finset.univ \ X.g.residual).card)).card).trans
      (hball.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hent (Nat.cast_nonneg _))))

end
end HypercubeRamsey.Lane_sol_s05_even
