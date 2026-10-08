import HypercubeRamsey.S16.Producers_q_s16_prod2

namespace HypercubeRamsey.S16.Lane_sol_s16_prod2
open Classical
open scoped BigOperators
open Lane_q_s16_prod2

/-- A finite product projected through an injective coordinate map. -/
theorem pi_injective_map {I J B : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype B] [DecidableEq B]
    (law : I → FinLaw B) (e : J → I) (he : Function.Injective e) :
    FinLaw.map (FinLaw.pi law) (fun a j => a (e j)) = FinLaw.pi (fun j => law (e j)) := by
  classical
  let default : I → B := fun i => by
    have htrue : 0 < (law i).pr (fun _ => True) := by rw [finLaw_pr_const]; norm_num
    exact Classical.choose (finLaw_pr_pos_has_nonzero_atom (law i) (fun _ => True) htrue)
  apply finLaw_ext
  intro a
  let extend : I → B := fun i => if h : ∃ j, e j = i then a (Classical.choose h) else default i
  have hExt (j : J) : extend (e j) = a j := by
    have hx : ∃ j', e j' = e j := ⟨j, rfl⟩
    rw [show extend (e j) = a (Classical.choose hx) by simp [extend, hx]]
    rw [he (Classical.choose_spec hx)]
  have hEvent (x : I → B) : (fun j => x (e j)) = a ↔
      ∀ i ∈ Finset.univ.image e, x i = extend i := by
    constructor
    · intro hx i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      rw [hExt]
      exact congrFun hx j
    · intro hx
      funext j
      have h := hx (e j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      simpa [hExt] using h
  calc
    (FinLaw.map (FinLaw.pi law) (fun x j => x (e j))).w a =
        (FinLaw.pi law).pr (fun x => (fun j => x (e j)) = a) := by
      simp only [FinLaw.map, FinLaw.pr]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : (fun j => x (e j)) = a <;> simp [h]
    _ = (FinLaw.pi law).pr (fun x => ∀ i ∈ Finset.univ.image e, x i = extend i) := by
      congr 1
      funext x
      exact propext (hEvent x)
    _ = ∏ i ∈ Finset.univ.image e, (law i).w (extend i) :=
      finLaw_pi_pr_cylinder law _ extend
    _ = ∏ j, (law (e j)).w (a j) := by
      rw [Finset.prod_image]
      · apply Finset.prod_congr rfl
        intro j _
        rw [hExt]
      · exact he.injOn
    _ = (FinLaw.pi (fun j => law (e j))).w a := rfl

/-- Expectations depending on injectively selected coordinates integrate only those rows. -/
theorem pi_injective_E {I J B : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype B] [DecidableEq B]
    (law : I → FinLaw B) (e : J → I) (he : Function.Injective e) (f : (J → B) → ℝ) :
    (FinLaw.pi law).E (fun x => f (fun j => x (e j))) =
      (FinLaw.pi (fun j => law (e j))).E f := by
  calc
    _ = (FinLaw.map (FinLaw.pi law) (fun a j => a (e j))).E f :=
      (finLaw_map_E _ _ f).symm
    _ = _ := by rw [pi_injective_map law e he]

/-- Reference bin/label sampling preserves the law on an injectively selected star. -/
theorem reference_projection_E {Gp Gq Rp J B Y : Type*}
    [Fintype Gp] [DecidableEq Gp] [Fintype Gq] [DecidableEq Gq]
    [Fintype Rp] [DecidableEq Rp] [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y]
    (Q : Gp → FinLaw B) (U : Gp → B → FinLaw Y) (gp : Rp → Gp)
    (r : J → Rp) (hr : Function.Injective r)
    (e : Gq → Gp) (he : Function.Injective e)
    (q : Gq → FinLaw B) (u : Gq → B → FinLaw Y) (g : J → Gq)
    (hg : ∀ j, gp (r j) = e (g j))
    (hq : ∀ j, Q (e j) = q j) (hu : ∀ j D, U (e j) D = u j D)
    (f : (J → Y) → ℝ) :
    (FinLaw.bind (FinLaw.pi Q) (fun a => FinLaw.pi (fun z => U (gp z) (a (gp z))))).E
        (fun ω => f (fun j => ω.2 (r j))) =
      (FinLaw.pi q).E (fun a => (FinLaw.pi (fun j => u (g j) (a (g j)))).E f) := by
  rw [Lane_q_s16_comp2.bind_expect]
  have hInner (a : Gp → B) :
      (FinLaw.pi (fun z => U (gp z) (a (gp z)))).E (fun ys => f (fun j => ys (r j))) =
        (FinLaw.pi (fun j => u (g j) (a (e (g j))))).E f := by
    rw [pi_injective_E _ r hr]
    congr 2
    funext j
    rw [hg, hu]
  simp_rw [hInner]
  have h := pi_injective_E Q e he
    (fun a => (FinLaw.pi (fun j => u (g j) (a (g j)))).E f)
  have hQ : (fun j => Q (e j)) = q := funext hq
  simpa only [hQ] using h

/-- Flipping different cube coordinates gives different words. -/
theorem flip_index_injective {n : ℕ} (v : CubePos n) :
    Function.Injective (flipPos v) := by
  intro i j h
  by_contra hij
  have hv := congrFun h i
  cases hx : v i <;> simp [flipPos, hij, Ne.symm hij, hx] at hv

end HypercubeRamsey.S16.Lane_sol_s16_prod2
