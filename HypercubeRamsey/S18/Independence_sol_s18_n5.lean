import HypercubeRamsey.S18.Pools_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem pi_product_local {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (s : Finset J) (F : J → (∀ i, Ω i) → ℝ)
    (scope : J → Finset I)
    (hdep : ∀ j x y, (∀ i ∈ scope j, x i = y i) → F j x = F j y)
    (hdisj : ∀ i j, i ≠ j → Disjoint (scope i) (scope j)) :
    (FinLaw.pi P).E (fun x => ∏ j ∈ s, F j x) = ∏ j ∈ s, (FinLaw.pi P).E (F j) := by
  induction s using Finset.induction_on with
  | empty => exact E_const _ 1
  | @insert a s ha ih =>
    have hprodDep : FinProb.DependsOn (fun x => ∏ j ∈ s, F j x) (s.biUnion scope) := by
      intro x y hxy
      apply Finset.prod_congr rfl
      intro j hj
      apply hdep j
      intro i hi
      exact hxy i (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩)
    have hunion : Disjoint (scope a) (s.biUnion scope) := by
      apply Finset.disjoint_left.mpr
      intro i hi hmem
      obtain ⟨j, hj, hji⟩ := Finset.mem_biUnion.mp hmem
      exact Finset.disjoint_left.mp (hdisj a j (by intro he; subst j; exact ha hj)) hi hji
    have hmul := FinProb.pi_expect_mul_of_disjoint
      (fun i => (⟨(P i).w, (P i).nonneg, (P i).sum_one⟩ : FinProb (Ω i)))
      (F a) (fun x => ∏ j ∈ s, F j x) (scope a) (s.biUnion scope) (hdep a) hprodDep hunion
    have hmul' : (FinLaw.pi P).E (fun x => F a x * ∏ j ∈ s, F j x) =
        (FinLaw.pi P).E (F a) * (FinLaw.pi P).E (fun x => ∏ j ∈ s, F j x) := by
      simpa only [FinLaw.E, FinProb.expect, FinLaw.pi, FinProb.pi] using hmul
    simp_rw [Finset.prod_insert ha]
    rw [hmul', ih]

theorem iidLaw_pi (D : LateData hPT) :
    D.encoding.iidLaw = FinLaw.pi (fun C =>
      FinLaw.uniform (Finset.univ : Finset (D.fresh.Pool C))
        ⟨D.encoding.pools_nonempty.choose C, Finset.mem_univ _⟩) := by
  have h := uniform_pi_sets (fun C => (Finset.univ : Finset (D.fresh.Pool C)))
    (fun C => (⟨D.encoding.pools_nonempty.choose C, Finset.mem_univ _⟩ :
      (Finset.univ : Finset (D.fresh.Pool C)).Nonempty))
  simpa only [LateEncoding.iidLaw, iidPoolLaw, Finset.mem_univ, implies_true,
    Finset.filter_true_of_mem] using h

/-- Independent complete input regions factor before initial resampling.
Each test may read whole cell pools and all finite tape entries in its region. -/
theorem iid_input_product_local (D : LateData hPT) {J : Type*} [Fintype J] [DecidableEq J]
    (s : Finset J) (F : J → D.encoding.InitInput → ℝ) (scope : J → Finset D.geom.Cell)
    (hdep : ∀ j x y, (∀ C ∈ scope j, x.1 C = y.1 C ∧ x.2 C = y.2 C) → F j x = F j y)
    (hdisj : ∀ i j, i ≠ j → Disjoint (scope i) (scope j)) :
    (D.encoding.initialLaw D.encoding.iidLaw).E (fun x => ∏ j ∈ s, F j x) =
      ∏ j ∈ s, (D.encoding.initialLaw D.encoding.iidLaw).E (F j) := by
  let g := fun j pools => (tapeLaw D.fresh D.encoding.Ts).E (fun t => F j (pools, t))
  have htape : ∀ pools, (tapeLaw D.fresh D.encoding.Ts).E
      (fun t => ∏ j ∈ s, F j (pools, t)) = ∏ j ∈ s, g j pools := by
    intro pools
    apply pi_product_local _ s (fun j t => F j (pools, t)) scope
    · intro j t t' htt'
      apply hdep j
      intro C hC
      exact ⟨rfl, htt' C hC⟩
    · exact hdisj
  have hg : ∀ j pools pools', (∀ C ∈ scope j, pools C = pools' C) → g j pools = g j pools' := by
    intro j pools pools' hpp'
    apply congrArg (tapeLaw D.fresh D.encoding.Ts).E
    funext t
    apply hdep j
    intro C hC
    exact ⟨hpp' C hC, rfl⟩
  simp only [LateEncoding.initialLaw, bind_E]
  simp_rw [htape]
  rw [iidLaw_pi]
  exact pi_product_local _ s g scope hg hdisj

end HypercubeRamsey.S18.Lane_sol_s18_n5
