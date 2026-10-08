import HypercubeRamsey.S18.Nodes_sol_s18_3e

namespace HypercubeRamsey.Lane_q_s18_cylf
open Classical
open scoped BigOperators

private theorem kernel_push_weight {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinLaw A) (K : A → FinLaw B) (b : B) :
    (FinLaw.map (FinLaw.bind P K) Prod.snd).w b = ∑ a, P.w a * (K a).w b := by
  change (∑ z : A × B, if z.2 = b then P.w z.1 * (K z.1).w z.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  simp

private theorem product_cond_mass {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (P : FinLaw A) (Q : FinLaw B)
    (s : Finset A) (t : Finset B) :
    (∑ z ∈ Finset.univ.filter (fun z : A × B => z.1 ∈ s ∧ z.2 ∈ t),
      (FinLaw.bind P (fun _ => Q)).w z) =
      (∑ a ∈ s, P.w a) * (∑ b ∈ t, Q.w b) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hterm : ∀ a b, (if a ∈ s ∧ b ∈ t then P.w a * Q.w b else 0) =
      (if a ∈ s then P.w a else 0) * (if b ∈ t then Q.w b else 0) := by
    intro a b
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ t <;> simp [ha, hb]
  change (∑ a, ∑ b, if a ∈ s ∧ b ∈ t then P.w a * Q.w b else 0) = _
  simp_rw [hterm, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp [Finset.sum_ite_mem]

private theorem product_cond {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (P : FinLaw A) (Q : FinLaw B)
    (s : Finset A) (t : Finset B)
    (hs : 0 < ∑ a ∈ s, P.w a) (ht : 0 < ∑ b ∈ t, Q.w b)
    (hp : 0 < ∑ z ∈ Finset.univ.filter (fun z : A × B => z.1 ∈ s ∧ z.2 ∈ t),
      (FinLaw.bind P (fun _ => Q)).w z) :
    FinLaw.cond (FinLaw.bind P (fun _ => Q))
      (Finset.univ.filter fun z : A × B => z.1 ∈ s ∧ z.2 ∈ t) hp =
        FinLaw.bind (FinLaw.cond P s hs) (fun _ => FinLaw.cond Q t ht) := by
  apply Lane_q_s16_comp1.finlaw_ext
  rintro ⟨a, b⟩
  simp only [FinLaw.cond]
  rw [product_cond_mass]
  simp only [FinLaw.bind, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ t <;>
    simp [ha, hb, div_mul_div_comm]

private theorem product_kernel_push {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (P : FinLaw A) (Q : FinLaw B)
    (f : A → A) (K : B → FinLaw B) :
    FinLaw.map (FinLaw.bind (FinLaw.bind P (fun _ => Q))
      (fun x => FinLaw.map (K x.2) (fun u => (f x.1, u)))) Prod.snd =
        FinLaw.bind (FinLaw.map P f) (fun _ => FinLaw.map (FinLaw.bind Q K) Prod.snd) := by
  have hmk : ∀ a b y, (FinLaw.map (K b) (fun u => (f a, u))).w y =
      if f a = y.1 then (K b).w y.2 else 0 := by
    intro a b y
    change (∑ u, if (f a, u) = y then (K b).w u else 0) = _
    rw [Finset.sum_eq_single y.2]
    · by_cases h : f a = y.1 <;> simp [Prod.ext_iff, h]
    · intro u hu hne
      have h : (f a, u) ≠ y := fun heq => hne (congrArg Prod.snd heq)
      simp [h]
    · simp
  apply Lane_q_s16_comp1.finlaw_ext
  rintro ⟨a', b'⟩
  rw [kernel_push_weight]
  simp_rw [hmk]
  rw [Fintype.sum_prod_type]
  change (∑ a, ∑ b, (P.w a * Q.w b) *
      (if f a = a' then (K b).w b' else 0)) = _
  have hterm : ∀ a b, (P.w a * Q.w b) * (if f a = a' then (K b).w b' else 0) =
      (if f a = a' then P.w a else 0) * (Q.w b * (K b).w b') := by
    intro a b
    by_cases h : f a = a' <;> simp [h, mul_assoc]
  simp_rw [hterm, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  change _ = (FinLaw.map P f).w a' *
    (FinLaw.map (FinLaw.bind Q K) Prod.snd).w b'
  rw [kernel_push_weight]
  rfl

private theorem positive_map_preimage {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (P : FinLaw A) (f : A → B) (y : B)
    (hy : 0 < (FinLaw.map P f).w y) : ∃ x, f x = y := by
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hy)
  by_cases h : f x = y
  · exact ⟨x, h⟩
  · exact False.elim (hx (by simp [h]))

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

theorem cylinder_forcing_proof (D : S18.LateData hPT) (R : Finset D.geom.Cell)
    (target : ∀ C, D.fresh.Pool C) (ht : target ∈ permPools D.geom)
    (event : Finset (Tapes D.fresh D.encoding.Ts))
    (hlocal : ∀ t u : Tapes D.fresh D.encoding.Ts,
      (∀ C ∈ R, t C = u C) → (t ∈ event ↔ u ∈ event))
    (A : Finset D.encoding.InitInput)
    (hA : ∀ x, x ∈ A ↔ (∀ C ∈ R, x.1 C = target C) ∧ x.2 ∈ event)
    (hpos : 0 < ∑ x ∈ A, D.encoding.permLaw.w x) :
    ∃ force : D.encoding.InitInput → FinLaw D.encoding.InitInput,
      FinLaw.map (FinLaw.bind D.encoding.permLaw force) Prod.snd =
        FinLaw.cond D.encoding.permLaw A hpos ∧
      ∀ x y, 0 < (force x).w y →
        (∀ C, C ∉ R → y.2 C = x.2 C) ∧
    ∀ (C : D.geom.Cell) (s : Fin (D.geom.nslot C)), C ∉ R →
      (∀ C' ∈ R, ∀ s' : Fin (D.geom.nslot C'),
        D.geom.cellPatch C' = D.geom.cellPatch C →
          (x.1 C s).1 ≠ (target C' s').1) →
      y.1 C s = x.1 C s := by
  obtain ⟨x₀, _, _⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
  letI : Nonempty (Tapes D.fresh D.encoding.Ts) := ⟨x₀.2⟩
  let S := Lane_sol_s18_3e.prescribedPools D R target
  let P := D.encoding.poolLaw
  let Q := tapeLaw D.fresh D.encoding.Ts
  have hrect : A = Finset.univ.filter
      (fun x : D.encoding.InitInput => x.1 ∈ S ∧ x.2 ∈ event) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hA x]
    simp [S, Lane_sol_s18_3e.prescribedPools]
  have hmass : (∑ p ∈ S, P.w p) * (∑ t ∈ event, Q.w t) =
      ∑ x ∈ A, D.encoding.permLaw.w x := by
    rw [hrect]
    exact (product_cond_mass P Q S event).symm
  have hPnonneg : 0 ≤ ∑ p ∈ S, P.w p :=
    Finset.sum_nonneg (fun p _ => P.nonneg p)
  have hQnonneg : 0 ≤ ∑ t ∈ event, Q.w t :=
    Finset.sum_nonneg (fun t _ => Q.nonneg t)
  have hPpos : 0 < ∑ p ∈ S, P.w p := by nlinarith [hpos, hmass]
  have hQpos : 0 < ∑ t ∈ event, Q.w t := by nlinarith [hpos, hmass]
  let Kt := fun t => FinLaw.map
    (FinLaw.cond Q event hQpos)
    (Lane_sol_s18_3e.overwriteTapes R t)
  let fp := Lane_sol_s18_3e.forcePools D R target ht
  let force := fun x : D.encoding.InitInput =>
    FinLaw.map (Kt x.2) (fun u => (fp x.1, u))
  have hpool : FinLaw.map P fp = FinLaw.cond P S hPpos := by
    simpa [P, S, fp] using
      (Lane_sol_s18_3e.forcePools_conditional D R target ht hPpos)
  have htape : FinLaw.map (FinLaw.bind Q Kt) Prod.snd =
      FinLaw.cond Q event hQpos := by
    dsimp [Kt, Q]
    apply Lane_sol_s18_3e.overwriteTapes_conditional
    exact hlocal
  have hpRect : 0 < ∑ x ∈ Finset.univ.filter
      (fun x : D.encoding.InitInput => x.1 ∈ S ∧ x.2 ∈ event),
      D.encoding.permLaw.w x := by
    rw [← hrect]
    exact hpos
  have hproduct := product_cond P Q S event hPpos hQpos hpRect
  refine ⟨force, ?_, ?_⟩
  · change FinLaw.map (FinLaw.bind (FinLaw.bind P (fun _ => Q)) force) Prod.snd = _
    rw [product_kernel_push, hpool, htape]
    rw [← hproduct]
    congr 1
    exact hrect.symm
  · intro x y hxy
    change 0 < (FinLaw.map (Kt x.2) (fun u => (fp x.1, u))).w y at hxy
    obtain ⟨u, hu⟩ := positive_map_preimage (Kt x.2)
      (fun u => (fp x.1, u)) y hxy
    have hyPool : y.1 = fp x.1 := (congrArg Prod.fst hu).symm
    have hxy' := hxy
    rw [← hu] at hxy'
    have hmap :
        (FinLaw.map (Kt x.2) (fun u => (fp x.1, u))).w (fp x.1, u) =
          (Kt x.2).w u := by
      change (∑ v, if (fp x.1, v) = (fp x.1, u) then (Kt x.2).w v else 0) = _
      rw [Finset.sum_eq_single u]
      · simp
      · intro v hv hne
        have h : (fp x.1, v) ≠ (fp x.1, u) :=
          fun heq => hne (congrArg Prod.snd heq)
        simp [h]
      · simp
    rw [hmap] at hxy'
    have hKt : 0 < (Kt x.2).w u := hxy'
    obtain ⟨t, htPre⟩ := positive_map_preimage
      (FinLaw.cond Q event hQpos)
      (Lane_sol_s18_3e.overwriteTapes R x.2) u (by simpa [Kt] using hKt)
    refine ⟨?_, ?_⟩
    · intro C hC
      have hyTape : y.2 = Lane_sol_s18_3e.overwriteTapes R x.2 t :=
        (congrArg Prod.snd hu).symm.trans htPre.symm
      rw [hyTape]
      simp [Lane_sol_s18_3e.overwriteTapes, hC]
    · intro C s hC himage
      rw [hyPool]
      simpa [fp] using
        (Lane_sol_s18_3e.forcePools_preserves D R target ht x.1 C s hC himage)

end HypercubeRamsey.Lane_q_s18_cylf
