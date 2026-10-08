import HypercubeRamsey.S18.Nodes_sol_s18_2lm_iteration

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm.SmallCylinder

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

private theorem pr_mono {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω)
    (A B : Ω → Prop) (h : ∀ s, A s → B s) : Q.pr A ≤ Q.pr B := by
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro s _
  by_cases ha : A s
  · simp [ha, h s ha]
  · simp only [ha, ↓reduceIte]
    split_ifs <;> simp [Q.nonneg]

/-- Only the actual image of a finite observation enters this atom cutoff.
The observation type itself need not be finite. -/
theorem observation_small_mass {Ω B : Type*} [Fintype Ω] [DecidableEq B]
    (Q : FinLaw Ω) (f : Ω → B) (γ : ℝ) (hγ : 0 ≤ γ) :
    Q.pr (fun s => Q.pr (fun u => f u = f s) < γ) ≤
      ((Finset.univ.image f).card : ℝ) * γ := by
  let image := Finset.univ.image f
  let g : Ω → image := fun s => ⟨f s, Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩⟩
  let R := FinLaw.map Q g
  have hmass (b : image) : R.w b = Q.pr (fun u => f u = b.1) := by
    rw [Cylinder.map_mass]
    have hevent : (fun u => g u = b) = (fun u => f u = b.1) := by
      funext u; apply propext; exact Subtype.ext_iff
    rw [hevent]
  have hevent : (fun s => Q.pr (fun u => f u = f s) < γ) = (fun s => R.w (g s) < γ) := by
    funext s; rw [hmass]
  rw [hevent, ← Cylinder.map_event Q g (fun b => R.w b < γ)]
  change R.pr (fun b => R.w b < γ) ≤ _
  calc
    _ ≤ ∑ b : image, γ := by
      unfold FinLaw.pr
      apply Finset.sum_le_sum
      intro b _
      split_ifs with hb
      · exact hb.le
      · exact hγ
    _ = _ := by simp [image]

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

abbrev Outside (X : CriticalTransferData D) (a : Fin (T.S.n k)) :=
  ∀ C : {C : D.geom.Cell // C ∉ X.blockCells a}, D.fresh.Pool C.1 × D.fresh.State C.1

def outside (a : Fin (T.S.n k)) (s : X.Raw) : Outside X a := fun C => s C.1

noncomputable def replaceOutside (a : Fin (T.S.n k)) (s : X.Raw) (v : Outside X a) : X.Raw :=
  fun C => if h : C ∈ X.blockCells a then s C else v ⟨C, h⟩

theorem replaceOutside_eq_on (a : Fin (T.S.n k)) (s : X.Raw) (v : Outside X a)
    (C : D.geom.Cell) (hC : C ∈ X.blockCells a) : replaceOutside a s v C = s C := by
  simp only [replaceOutside, dif_pos hC]

theorem replaceOutside_local (a : Fin (T.S.n k)) (s s' : X.Raw) (v : Outside X a)
    (he : ∀ C ∈ X.blockCells a, s C = s' C) : replaceOutside a s v = replaceOutside a s' v := by
  funext C
  by_cases hC : C ∈ X.blockCells a
  · simp only [replaceOutside, dif_pos hC, he C hC]
  · simp only [replaceOutside, dif_neg hC]

theorem replaceOutside_self (a : Fin (T.S.n k)) (s : X.Raw) (v : Outside X a)
    (he : outside a s = v) : replaceOutside a s v = s := by
  funext C
  by_cases hC : C ∈ X.blockCells a
  · simp [replaceOutside, hC]
  · have hh := congrFun he ⟨C, hC⟩
    simpa only [outside, replaceOutside, dif_neg hC] using hh.symm

/-- Fixing other blocks makes one local cylinder exactly the transcript
fiber on the responding block, even for an adaptive request sequence. -/
theorem replies_eq_iff_cylinder_of_outside (hgeom : TransferGeometry X)
    (P : TransferProtocol X) (seed : P.Seed) (s u : X.Raw) (t : ℕ)
    (a : Fin (T.S.n k)) (hout : ∀ C, C ∉ X.blockCells a → u C = s C) :
    P.replies seed u t = P.replies seed s t ↔ Blocks.cylinder P seed s t a u := by
  constructor
  · intro ht j hj _
    have he := replies_prefix_eq P seed u s (Nat.le_of_lt hj) ht
    have hn := replies_prefix_eq P seed u s (Nat.succ_le_of_lt hj) ht
    rw [P.replies_step, P.replies_step, he] at hn
    exact List.singleton_inj.mp (List.append_cancel_left hn)
  · intro hc
    have hp : ∀ j, j ≤ t → P.replies seed u j = P.replies seed s j := by
      intro j
      induction j with
      | zero => intro _; rw [P.replies_zero, P.replies_zero]
      | succ j ih =>
        intro hj
        have he := ih (by omega)
        rw [P.replies_step, P.replies_step, he]
        congr 2
        by_cases hreq : X.sameBlock a (P.request seed (P.replies seed s j))
        · exact hc j (by omega) hreq
        · apply P.answer_local
          intro C hC
          apply hout
          intro ha
          exact Finset.disjoint_left.mp (Blocks.blockCells_disjoint hgeom hreq) ha hC
    exact hp t le_rfl

theorem local_mass_eq_fiber (hgeom : TransferGeometry X) (P : TransferProtocol X)
    (seed : P.Seed) (a : Fin (T.S.n k)) (v : Outside X a) (s : X.Raw) (t : ℕ) :
    X.rawLaw.pr (Blocks.cylinder P seed (replaceOutside a s v) t a) =
      X.rawLaw.pr (fun u => P.replies seed (replaceOutside a u v) t =
        P.replies seed (replaceOutside a s v) t) := by
  have hevent : Blocks.cylinder P seed (replaceOutside a s v) t a =
      (fun u => P.replies seed (replaceOutside a u v) t = P.replies seed (replaceOutside a s v) t) := by
    funext u
    apply propext
    rw [Blocks.cylinder_local P seed (replaceOutside a s v) t a u (replaceOutside a u v)
      (fun C hC => (replaceOutside_eq_on a u v C hC).symm)]
    exact (replies_eq_iff_cylinder_of_outside hgeom P seed
      (replaceOutside a s v) (replaceOutside a u v) t a (by
        intro C hC; simp only [replaceOutside, dif_neg hC])).symm
  rw [hevent]

/-- Every prefix range with other cells fixed is an image of the complete
reply range; the latter is the bound supplied in the frozen hypotheses. -/
theorem replaced_range_bound (P : TransferProtocol X) (hR : ReplyRangeBound P) (seed : P.Seed)
    (a : Fin (T.S.n k)) (v : Outside X a) (t : ℕ) (ht : t ≤ P.steps) :
    ((Finset.univ.image fun s : X.Raw => P.replies seed (replaceOutside a s v) t).card : ℝ) ≤
      Real.exp (Real.rpow (T.S.n k : ℝ) 0.4) := by
  let base : X.Raw := fun C => (D.l16_valid.pools_nonempty.choose C, X.fixed C)
  let fixed := replaceOutside a base v
  let F := ((Finset.univ : Finset X.Raw).filter fun s => ∀ C, C ∉ X.blockCells a → s C = fixed C).image
    (fun s => P.replies seed s P.steps)
  have hsub : (Finset.univ.image fun s : X.Raw => P.replies seed (replaceOutside a s v) t) ⊆
      F.image (fun replies => replies.take t) := by
    intro reply hr
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hr
    have hmem : replaceOutside a s v ∈ (Finset.univ : Finset X.Raw).filter
        (fun s => ∀ C, C ∉ X.blockCells a → s C = fixed C) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro C hC
      simp only [fixed, replaceOutside, dif_neg hC]
    refine Finset.mem_image.mpr ⟨P.replies seed (replaceOutside a s v) P.steps,
      Finset.mem_image.mpr ⟨replaceOutside a s v, hmem, rfl⟩, ?_⟩
    rw [replies_take P seed _ ht]
    exact hs
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_image_le : (F.image (fun replies => replies.take t)).card ≤ F.card)
  have hcardR : ((Finset.univ.image fun s : X.Raw => P.replies seed (replaceOutside a s v) t).card : ℝ) ≤ F.card := by
    exact_mod_cast hcard
  exact hcardR.trans (hR seed a fixed)

/-- The small-cylinder probability is averaged by fixing outside cells and
using independence. No union over global transcripts or their values occurs. -/
theorem small_local_cylinder_mass (hgeom : TransferGeometry X) (P : TransferProtocol X)
    (hR : ReplyRangeBound P) (seed : P.Seed) (a : Fin (T.S.n k)) (t : ℕ) (ht : t ≤ P.steps)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    X.rawLaw.pr (fun s => X.rawLaw.pr (Blocks.cylinder P seed s t a) < γ) ≤
      Real.exp (Real.rpow (T.S.n k : ℝ) 0.4) * γ := by
  let Small := fun s => X.rawLaw.pr (Blocks.cylinder P seed s t a) < γ
  let K := Real.exp (Real.rpow (T.S.n k : ℝ) 0.4)
  let E := fun (v : Outside X a) (s : X.Raw) => Small (replaceOutside a s v)
  have hE (v : Outside X a) : X.rawLaw.pr (E v) ≤ K * γ := by
    have hevent : E v = (fun s => X.rawLaw.pr (fun u =>
        P.replies seed (replaceOutside a u v) t = P.replies seed (replaceOutside a s v) t) < γ) :=
      funext fun s => by rw [← local_mass_eq_fiber hgeom P seed a v s t]
    rw [hevent]
    apply (observation_small_mass _ _ γ hγ).trans
    exact mul_le_mul_of_nonneg_right (replaced_range_bound P hR seed a v t ht) hγ
  let factors := fun C => if C ∈ X.criticalCells then D.typicalFresh C
    else FinLaw.dirac (D.l16_valid.pools_nonempty.choose C, X.fixed C)
  have hsplit (v : Outside X a) : X.rawLaw.pr (fun s => Small s ∧ outside a s = v) =
      X.rawLaw.pr (E v) * X.rawLaw.pr (fun s => outside a s = v) := by
    have hevent : (fun s => Small s ∧ outside a s = v) =
        (fun s => E v s ∧ outside a s = v) := by
      funext s
      apply propext
      constructor
      · rintro ⟨hs, hv⟩; exact ⟨by simpa [E, replaceOutside_self a s v hv] using hs, hv⟩
      · rintro ⟨hs, hv⟩; exact ⟨by simpa [E, replaceOutside_self a s v hv] using hs, hv⟩
    rw [hevent]
    exact Blocks.pi_pr_and factors (E v) (fun s => outside a s = v)
      (X.blockCells a) (Finset.univ \ X.blockCells a)
      (by intro s s' he; simp only [E, replaceOutside_local a s s' v he])
      (by
        intro s s' he
        have hout : outside (X := X) a s = outside (X := X) a s' := by
          funext C
          exact he C.1 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, C.2⟩)
        exact ⟨fun hs => hout.symm.trans hs, fun hs => hout.trans hs⟩) (by
        apply Finset.disjoint_left.mpr
        intro C hC hc
        exact (Finset.mem_sdiff.mp hc).2 hC)
  change X.rawLaw.pr Small ≤ K * γ
  rw [← Cylinder.pr_partition X.rawLaw (outside a) Small]
  calc
    _ = ∑ v, X.rawLaw.pr (fun s => Small s ∧ outside a s = v) := by
      apply Finset.sum_congr rfl
      intro v _
      congr 1
      funext s
      exact propext and_comm
    _ = ∑ v, X.rawLaw.pr (E v) * X.rawLaw.pr (fun s => outside a s = v) := by simp_rw [hsplit]
    _ ≤ ∑ v, K * γ * X.rawLaw.pr (fun s => outside a s = v) := Finset.sum_le_sum fun v _ =>
      mul_le_mul_of_nonneg_right (hE v) (by
        unfold FinLaw.pr; exact Finset.sum_nonneg fun s _ => by split_ifs <;> simp [X.rawLaw.nonneg])
    _ = K * γ := by
      rw [← Finset.mul_sum]
      have hmass : (∑ v : Outside X a, X.rawLaw.pr (fun s => outside (X := X) a s = v)) = 1 := by
        have h := Cylinder.pr_partition X.rawLaw (outside (X := X) a) (fun _ => True)
        simp only [and_true] at h
        have htrue : X.rawLaw.pr (fun _ => True) = 1 := by simp [FinLaw.pr, X.rawLaw.sum_one]
        rw [htrue] at h
        exact h
      rw [hmass, mul_one]

end HypercubeRamsey.S18.Lane_sol_s18_2lm.SmallCylinder
