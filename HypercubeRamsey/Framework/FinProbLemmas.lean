import HypercubeRamsey.Framework.FinProb

namespace HypercubeRamsey

open scoped BigOperators

namespace FinProb

variable {Ω α β : Type*} [Fintype Ω]

theorem expect_add (P : FinProb Ω) (f g : Ω → ℝ) :
    P.expect (fun ω => f ω + g ω) = P.expect f + P.expect g := by
  simp [expect, Finset.sum_add_distrib, mul_add]

theorem expect_smul (P : FinProb Ω) (r : ℝ) (f : Ω → ℝ) :
    P.expect (fun ω => r * f ω) = r * P.expect f := by
  simp [expect, ← Finset.mul_sum, mul_assoc, mul_comm]

theorem expect_mono (P : FinProb Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    P.expect f ≤ P.expect g := by
  unfold expect
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hfg ω) (P.nonneg ω)

theorem expect_const (P : FinProb Ω) (r : ℝ) : P.expect (fun _ => r) = r := by
  simp [expect, ← Finset.sum_mul, P.sum_eq_one]

theorem pr_union (P : FinProb Ω) (A B : Ω → Prop) :
    P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  letI : DecidablePred A := fun ω => Classical.propDecidable (A ω)
  letI : DecidablePred B := fun ω => Classical.propDecidable (B ω)
  letI : DecidablePred (fun ω => A ω ∨ B ω) :=
    fun ω => Classical.propDecidable (A ω ∨ B ω)
  unfold pr
  calc
    Finset.univ.sum (fun ω => if A ω ∨ B ω then P.w ω else 0) ≤
        Finset.univ.sum (fun ω => (if A ω then P.w ω else 0) + (if B ω then P.w ω else 0)) := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]
    _ = Finset.univ.sum (fun ω => if A ω then P.w ω else 0) +
        Finset.univ.sum (fun ω => if B ω then P.w ω else 0) := by
      rw [Finset.sum_add_distrib]

theorem markov (P : FinProb Ω) (f : Ω → ℝ) (t : ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (ht : 0 < t) :
    P.pr (fun ω => t ≤ f ω) ≤ P.expect f / t := by
  classical
  let A : Ω → Prop := fun ω => t ≤ f ω
  have hpoint : t * P.pr A ≤ P.expect f := by
    change t * (∑ ω ∈ Finset.univ, if A ω then P.w ω else 0) ≤ P.expect f
    rw [Finset.mul_sum]
    calc
      (∑ ω ∈ Finset.univ, t * (if A ω then P.w ω else 0)) =
          ∑ ω ∈ Finset.univ, P.w ω * (if A ω then t else 0) := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hA : A ω <;> simp [hA, mul_comm]
      _ ≤ ∑ ω ∈ Finset.univ, P.w ω * f ω := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases hA : A ω
        · simpa [hA] using mul_le_mul_of_nonneg_left hA (P.nonneg ω)
        · simpa [hA] using mul_nonneg (P.nonneg ω) (hf ω)
  apply (le_div_iff₀ ht).2
  calc
    P.pr A * t = t * P.pr A := by ring
    _ ≤ P.expect f := hpoint

theorem bind_expect [Fintype α] [Fintype β] (P : FinProb α) (K : α → FinProb β)
    (f : α → β → ℝ) :
    (bind P K).expect (fun ab => f ab.1 ab.2) =
      ∑ a, P.w a * (K a).expect (f a) := by
  classical
  simp only [expect, bind, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b ∈ Finset.univ, P.w a * (K a).w b * f a b) =
    P.w a * ∑ b ∈ Finset.univ, (K a).w b * f a b
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem map_expect [Fintype α] [Fintype β] [DecidableEq β] (P : FinProb α)
    (f : α → β) (g : β → ℝ) :
    (map P f).expect g = P.expect (fun a => g (f a)) := by
  classical
  simp only [expect, map]
  change Finset.univ.sum (fun b =>
      (Finset.univ.sum (fun a => if f a = b then P.w a else 0)) * g b) =
    Finset.univ.sum (fun a => P.w a * g (f a))
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [eq_comm]

private theorem nonempty_of_finProb {α : Type*} [Fintype α] (P : FinProb α) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := ⟨fun a => h ⟨a⟩⟩
  have hsum : (∑ a, P.w a) = 0 := by simp
  rw [P.sum_eq_one] at hsum
  norm_num at hsum

private theorem pi_weight_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (ω : ∀ i, Ω i) :
    (∏ i, (P i).w (ω i)) =
      (∏ i : {i // i ∈ s}, (P i.1).w (ω i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (ω i.1)) := by
  classical
  let f : ι → ℝ := fun i => (P i).w (ω i)
  let t : Finset ι := Finset.univ.filter (fun i => i ∉ s)
  have hs : (∏ i : {i // i ∈ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∈ s, f i := by
    rw [Finset.univ_eq_attach]
    simpa [f] using Finset.prod_attach s f
  let ecomp : {i // i ∉ s} ≃ {i // i ∈ t} := {
    toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
    invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl
  }
  have hnot : (∏ i : {i // i ∉ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∉ s, f i := by
    calc
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 := by
        exact Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  calc
    (∏ i, f i) =
        (∏ i ∈ Finset.univ with i ∈ s, f i) *
          (∏ i ∈ Finset.univ with i ∉ s, f i) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun i : ι => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) *
          (∏ i : {i // i ∉ s}, f i.1) := by rw [← hs, ← hnot]

private theorem pi_expect_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
            f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [pi_weight_split P s (e.symm (a, b))]
  change ((∏ i : {i // i ∈ s}, (P i.1).w (e.symm (a, b) i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (e.symm (a, b) i.1))) * f (e.symm (a, b)) = _
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  simp_rw [hleft, hright]
  rfl

private theorem sum_product_factor {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ) (u : α → ℝ) (v : β → ℝ) :
    (∑ a, ∑ b, p a * q b * u a * v b) =
      (∑ a, p a * u a) * (∑ b, q b * v b) := by
  classical
  calc
    (∑ a, ∑ b, p a * q b * u a * v b) =
        ∑ a, ∑ b, (p a * u a) * (q b * v b) := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro b
      ring
    _ = (∑ a, p a * u a) * (∑ b, q b * v b) := by
      symm
      exact Fintype.sum_mul_sum _ _

theorem pi_expect_depends {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) (ω₀ : ∀ i, Ω i)
    (hf : DependsOn f s) :
    (FinProb.pi P).expect f =
      (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).expect
        (fun a => f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
          (a, fun i => ω₀ i.1))) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  let Ps := FinProb.pi (fun i : {i // i ∈ s} => P i.1)
  let Pc := FinProb.pi (fun i : {i // i ∉ s} => P i.1)
  let b₀ : ∀ i : {i // i ∉ s}, Ω i.1 := fun i => ω₀ i.1
  let F : (∀ i : {i // i ∈ s}, Ω i.1) → ℝ := fun a => f (e.symm (a, b₀))
  have hF : ∀ a b, f (e.symm (a, b)) = F a := by
    intro a b
    apply hf _ _
    intro i hi
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hi]
  rw [pi_expect_split P s f]
  calc
    (∑ a, ∑ b, Ps.w a * Pc.w b * f (e.symm (a, b))) =
        ∑ a, ∑ b, Ps.w a * Pc.w b * F a * 1 := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro b
      rw [hF a b]
      ring
    _ = (∑ a, Ps.w a * F a) * (∑ b, Pc.w b * 1) :=
      sum_product_factor (fun a => Ps.w a) (fun b => Pc.w b) F (fun _ => 1)
    _ = Ps.expect F := by simp [FinProb.expect, Pc.sum_eq_one]

theorem pi_expect_mul_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (f g : (∀ i, Ω i) → ℝ) (s t : Finset ι)
    (hf : DependsOn f s) (hg : DependsOn g t) (hst : Disjoint s t) :
    (FinProb.pi P).expect (fun ω => f ω * g ω) =
      (FinProb.pi P).expect f * (FinProb.pi P).expect g := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  let Ps := FinProb.pi (fun i : {i // i ∈ s} => P i.1)
  let Pc := FinProb.pi (fun i : {i // i ∉ s} => P i.1)
  let ω₀ : ∀ i, Ω i := Classical.choice (nonempty_of_finProb (FinProb.pi P))
  let a₀ : ∀ i : {i // i ∈ s}, Ω i.1 := fun i => ω₀ i.1
  let b₀ : ∀ i : {i // i ∉ s}, Ω i.1 := fun i => ω₀ i.1
  let F : (∀ i : {i // i ∈ s}, Ω i.1) → ℝ := fun a => f (e.symm (a, b₀))
  let G : (∀ i : {i // i ∉ s}, Ω i.1) → ℝ := fun b => g (e.symm (a₀, b))
  have hF : ∀ a b, f (e.symm (a, b)) = F a := by
    intro a b
    apply hf _ _
    intro i hi
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hi]
  have hG : ∀ a b, g (e.symm (a, b)) = G b := by
    intro a b
    apply hg _ _
    intro i hi
    have his : (i : ι) ∉ s := fun hmem => (Finset.disjoint_left.mp hst) hmem hi
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg his]
  have hfexp : (FinProb.pi P).expect f = Ps.expect F := by
    exact pi_expect_depends P s f ω₀ hf
  have hgexp : (FinProb.pi P).expect g = Pc.expect G := by
    rw [pi_expect_split P s g]
    calc
      (∑ a, ∑ b, Ps.w a * Pc.w b * g (e.symm (a, b))) =
          ∑ a, ∑ b, Ps.w a * Pc.w b * 1 * G b := by
        apply Fintype.sum_congr
        intro a
        apply Fintype.sum_congr
        intro b
        rw [hG a b]
        ring
      _ = (∑ a, Ps.w a * 1) * (∑ b, Pc.w b * G b) :=
        sum_product_factor (fun a => Ps.w a) (fun b => Pc.w b) (fun _ => 1) G
      _ = Pc.expect G := by simp [FinProb.expect, Ps.sum_eq_one]
  rw [pi_expect_split P s (fun ω => f ω * g ω)]
  calc
    (∑ a, ∑ b, Ps.w a * Pc.w b * (f (e.symm (a, b)) * g (e.symm (a, b)))) =
        ∑ a, ∑ b, Ps.w a * Pc.w b * F a * G b := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro b
      rw [hF a b, hG a b]
      ring
    _ = Ps.expect F * Pc.expect G := by
      rw [sum_product_factor]
      simp [FinProb.expect]
    _ = (FinProb.pi P).expect f * (FinProb.pi P).expect g := by
      rw [← hfexp, ← hgexp]

theorem pi_marginal_expect {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (g : (∀ i : {i // i ∈ s}, Ω i.1) → ℝ) :
    (FinProb.pi P).expect (fun ω => g (fun i => ω i.1)) =
      (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).expect g := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  let Ps := FinProb.pi (fun i : {i // i ∈ s} => P i.1)
  let Pc := FinProb.pi (fun i : {i // i ∉ s} => P i.1)
  rw [pi_expect_split P s (fun ω => g (fun i => ω i.1))]
  have hproj : ∀ a b, g (fun i => e.symm (a, b) i.1) = g a := by
    intro a b
    congr 1
    funext i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos i.2]
  calc
    (∑ a, ∑ b, Ps.w a * Pc.w b * g (fun i => e.symm (a, b) i.1)) =
        ∑ a, ∑ b, Ps.w a * Pc.w b * g a * 1 := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro b
      rw [hproj a b]
      ring
    _ = (∑ a, Ps.w a * g a) * (∑ b, Pc.w b * 1) :=
      sum_product_factor (fun a => Ps.w a) (fun b => Pc.w b) g (fun _ => 1)
    _ = Ps.expect g := by simp [FinProb.expect, Pc.sum_eq_one]

theorem pi_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (s : Finset ι)
    (a : ∀ i : {i // i ∈ s}, Ω i.1) :
    (FinProb.map (FinProb.pi P) (fun ω (i : {i // i ∈ s}) => ω i.1)).w a =
      (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a := by
  classical
  have h := FinProb.map_expect (FinProb.pi P) (fun ω (i : {i // i ∈ s}) => ω i.1)
    (fun x => if x = a then 1 else 0)
  have hm := pi_marginal_expect P s (fun x => if x = a then 1 else 0)
  rw [hm] at h
  simpa [FinProb.expect] using h

end FinProb

end HypercubeRamsey
