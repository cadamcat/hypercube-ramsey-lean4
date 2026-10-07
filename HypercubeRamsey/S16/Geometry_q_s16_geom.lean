import HypercubeRamsey.PartC.Resampling

namespace HypercubeRamsey.Lane_q_s16_geom

open Classical

universe u

noncomputable def finiteEmbeddingOfCardLE {α β : Type u} [Fintype α] [Fintype β]
    (h : Fintype.card α ≤ Fintype.card β) : α ↪ β :=
  (Fintype.equivFin α).toEmbedding |>.trans
    ((Fin.castLEEmb h).trans (Fintype.equivFin β).symm.toEmbedding)

/-- A finite loopless symmetric graph with degree at most `d` admits a greedy
coloring with `d + 1` colors. -/
theorem exists_coloring_of_degree_bound {α : Type u} [Fintype α]
    (adj : α → α → Prop) (d : ℕ)
    (hsymm : ∀ ⦃x y⦄, adj x y → adj y x)
    (hirr : ∀ x, ¬ adj x x)
    (hdegree : ∀ x, (Finset.univ.filter (adj x)).card ≤ d) :
    ∃ c : α → Fin (d + 1), ∀ ⦃x y⦄, adj x y → c x ≠ c y := by
  classical
  let P : ∀ (β : Type u) [Fintype β], Prop := fun β =>
    ∀ (r : β → β → Prop), (∀ ⦃x y⦄, r x y → r y x) →
      (∀ x, ¬ r x x) →
      (∀ x, (Finset.univ.filter (r x)).card ≤ d) →
      ∃ c : β → Fin (d + 1), ∀ ⦃x y⦄, r x y → c x ≠ c y
  have hP : P α := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ α
    · intro β γ _ e ih r hr hs hd
      letI : Fintype β := Fintype.ofEquiv γ e.symm
      have hdegree' : ∀ x : β,
          (Finset.univ.filter (fun y => r (e x) (e y))).card ≤ d := by
        intro x
        let s : Finset β := Finset.univ.filter (fun y => r (e x) (e y))
        let t : Finset γ := Finset.univ.filter (r (e x))
        have hcard : s.card = t.card := by
          apply Finset.card_bij (fun y _ => e y)
          · intro y hy
            change y ∈ Finset.univ.filter (fun z => r (e x) (e z)) at hy
            have hy' := (Finset.mem_filter.mp hy).2
            change e y ∈ Finset.univ.filter (r (e x))
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩
          · intro y₁ hy₁ y₂ hy₂ heq
            exact e.injective heq
          · intro y hy
            refine ⟨e.symm y, ?_, by simp⟩
            change y ∈ Finset.univ.filter (r (e x)) at hy
            have hy' := (Finset.mem_filter.mp hy).2
            change e.symm y ∈ Finset.univ.filter (fun z => r (e x) (e z))
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hy'⟩
        calc
          s.card = t.card := hcard
          _ ≤ d := hd (e x)
      obtain ⟨c, hc⟩ := ih (fun x y => r (e x) (e y))
        (by intro x y h; exact hr h)
        (by intro x h; exact hs (e x) h) hdegree'
      refine ⟨fun x => c (e.symm x), ?_⟩
      intro x y h
      exact hc (by simpa using h)
    · intro r hr hs hd
      refine ⟨(fun x => x.elim), ?_⟩
      intro x y h
      exact x.elim
    · intro β _ ih r hr hs hd
      have hdegree' : ∀ x : β,
          (Finset.univ.filter (fun y => r (some x) (some y))).card ≤ d := by
        intro x
        let s : Finset β := Finset.univ.filter (fun y => r (some x) (some y))
        let t : Finset (Option β) := Finset.univ.filter (r (some x))
        have hsub : s.image some ⊆ t := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩
        have hcard : s.card ≤ t.card := by
          calc
            s.card = (s.image some).card := by
              symm
              exact Finset.card_image_of_injective _ (Option.some_injective β)
            _ ≤ t.card := Finset.card_le_card hsub
        exact hcard.trans (hd (some x))
      obtain ⟨c, hc⟩ := ih (fun x y => r (some x) (some y))
        (by intro x y h; exact hr h)
        (by intro x h; exact hs (some x) h) hdegree'
      let bad : Finset (Fin (d + 1)) :=
        (Finset.univ.filter (fun x : β => r none (some x))).image c
      have hbad : bad.card ≤ d := by
        let neigh : Finset β := Finset.univ.filter (fun x => r none (some x))
        let allNeigh : Finset (Option β) := Finset.univ.filter (r none)
        have hneighSub : neigh.image some ⊆ allNeigh := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        have hneigh : neigh.card ≤ allNeigh.card := by
          calc
            neigh.card = (neigh.image some).card := by
              symm
              exact Finset.card_image_of_injective _ (Option.some_injective β)
            _ ≤ allNeigh.card := Finset.card_le_card hneighSub
        calc
          bad.card ≤ neigh.card := by
            dsimp [bad, neigh]
            exact Finset.card_image_le
          _ ≤ allNeigh.card := hneigh
          _ ≤ d := hd none
      have hlt : bad.card < (Finset.univ : Finset (Fin (d + 1))).card := by
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨z, hz, hzn⟩ := bad.exists_mem_notMem_of_card_lt_card hlt
      refine ⟨(fun x => match x with | none => z | some y => c y), ?_⟩
      intro x y h
      cases x with
      | none =>
        cases y with
        | none => exact (hs none h).elim
        | some y =>
          change z ≠ c y
          intro heq
          have hy : y ∈ Finset.univ.filter (fun z : β => r none (some z)) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact h
          have hcy : c y ∈ bad := Finset.mem_image.mpr ⟨y, hy, rfl⟩
          exact hzn (heq ▸ hcy)
      | some x =>
        cases y with
        | none =>
          change c x ≠ z
          intro heq
          have h' : r none (some x) := hr h
          have hx : x ∈ Finset.univ.filter (fun z : β => r none (some z)) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact h'
          have hcx : c x ∈ bad := Finset.mem_image.mpr ⟨x, hx, rfl⟩
          exact hzn (heq.symm ▸ hcx)
        | some y =>
          change c x ≠ c y
          exact hc h
  exact hP adj hsymm hirr hdegree

/-- A Hamming ball in a Boolean cube is bounded by the sum of the binomial
layers through its radius. -/
theorem hamming_ball_card_le {m r : ℕ} (v : CubePos m) :
    (Finset.univ.filter fun w : CubePos m => hammingDist v w ≤ r).card ≤
      ∑ j ∈ Finset.range (r + 1), Nat.choose m j := by
  classical
  let diffEquiv : CubePos m ≃ Finset (Fin m) :=
    { toFun := fun w => Finset.univ.filter fun i => v i ≠ w i
      invFun := fun s i => if i ∈ s then !v i else v i
      left_inv := by
        intro w
        funext i
        by_cases h : v i = w i
        · simp [h]
        · have h' : w i = !v i := by
            cases hv : v i <;> cases hw : w i <;> simp_all
          simp [h']
      right_inv := by
        intro s
        ext i
        by_cases h : i ∈ s <;> simp [h] }
  let B : Finset (CubePos m) := Finset.univ.filter fun w => hammingDist v w ≤ r
  let S : Type := {s : Finset (Fin m) // s.card ≤ r}
  let layers : Type := Σ j : Fin (r + 1), {s : Finset (Fin m) // s.card = j.val}
  let toS : {w : CubePos m // w ∈ B} → S := fun w =>
    ⟨diffEquiv w.1, by
      have hw := w.2
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist] at hw
      simpa [diffEquiv] using hw⟩
  have hinj : Function.Injective toS := by
    intro x y h
    apply Subtype.ext
    apply diffEquiv.injective
    exact congrArg Subtype.val h
  have hball : B.card = Fintype.card {w : CubePos m // w ∈ B} := by
    rw [Fintype.card_subtype]
    simp
  have hS : Fintype.card S ≤ Fintype.card layers := by
    apply Fintype.card_le_of_injective
      (fun s : S => ⟨⟨s.1.card, by omega⟩, ⟨s.1, rfl⟩⟩)
    intro x y h
    apply Subtype.ext
    have hs := congrArg (fun z : layers => z.2.val) h
    exact hs
  have hlayers : Fintype.card layers =
      ∑ j ∈ Finset.range (r + 1), Nat.choose m j := by
    calc
      Fintype.card layers = ∑ j : Fin (r + 1),
          Fintype.card {s : Finset (Fin m) // s.card = j.val} := by
        simp [layers, Fintype.card_sigma]
      _ = ∑ j : Fin (r + 1), Nat.choose m j.val := by
        simp [Fintype.card_finset_len]
      _ = ∑ j ∈ Finset.range (r + 1), Nat.choose m j := by
        rw [Fin.sum_univ_eq_sum_range (fun j => Nat.choose m j) (r + 1)]
  calc
    B.card = Fintype.card {w : CubePos m // w ∈ B} := hball
    _ ≤ Fintype.card S := Fintype.card_le_of_injective toS hinj
    _ ≤ Fintype.card layers := hS
    _ = ∑ j ∈ Finset.range (r + 1), Nat.choose m j := hlayers

/-- A Boolean cube whose Hamming-ball layers fit in `d` colors can be colored
so that close distinct words receive different colors. -/
theorem cube_hamming_coloring {m r d : ℕ}
    (hbound : (∑ j ∈ Finset.range (r + 1), Nat.choose m j) ≤ d) :
    ∃ c : CubePos m → Fin (d + 1),
      ∀ ⦃x y⦄, x ≠ y → hammingDist x y ≤ r → c x ≠ c y := by
  classical
  let adj : CubePos m → CubePos m → Prop :=
    fun x y => x ≠ y ∧ hammingDist x y ≤ r
  letI : DecidableRel adj := fun x y => Classical.propDecidable _
  have hsymm : ∀ ⦃x y⦄, adj x y → adj y x := by
    intro x y h
    rcases h with ⟨hxy, hdist⟩
    refine ⟨hxy.symm, ?_⟩
    simpa [hammingDist, ne_comm] using hdist
  have hirr : ∀ x, ¬ adj x x := by
    intro x h
    exact h.1 rfl
  have hdegree : ∀ x, (Finset.univ.filter (adj x)).card ≤ d := by
    intro x
    let Nbr := Finset.univ.filter (adj x)
    let Ball := Finset.univ.filter (fun y : CubePos m => hammingDist x y ≤ r)
    have hsub : Nbr ⊆ Ball := by
      intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'.2⟩
    calc
      Nbr.card ≤ Ball.card := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ Finset.range (r + 1), Nat.choose m j := hamming_ball_card_le x
      _ ≤ d := hbound
  obtain ⟨c, hc⟩ := exists_coloring_of_degree_bound adj d hsymm hirr hdegree
  refine ⟨c, ?_⟩
  intro x y hxy hdist
  exact hc ⟨hxy, hdist⟩

theorem sum_choose_mono {m n r : ℕ} (hmn : m ≤ n) :
    (∑ j ∈ Finset.range (r + 1), Nat.choose m j) ≤
      ∑ j ∈ Finset.range (r + 1), Nat.choose n j := by
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.choose_le_choose j hmn

/-- The number of rank starts divisible by a positive batch size is at most
`m / q + 1`. -/
theorem card_rank_starts_le (m q : ℕ) :
    Fintype.card {j : Fin m // j.val % q = 0} ≤ m / q + 1 := by
  classical
  let f : {j : Fin m // j.val % q = 0} → Fin (m / q + 1) := fun j =>
    ⟨j.1.val / q, by
      have hj : j.1.val / q ≤ m / q := Nat.div_le_div_right j.1.isLt.le
      omega⟩
  calc
    Fintype.card {j : Fin m // j.val % q = 0} ≤ Fintype.card (Fin (m / q + 1)) :=
      Fintype.card_le_of_injective f (by
        intro a b hab
        apply Subtype.ext
        apply Fin.ext
        have hquot : a.1.val / q = b.1.val / q := congrArg Fin.val hab
        have ha : a.1.val = q * (a.1.val / q) := by
          calc
            a.1.val = a.1.val % q + q * (a.1.val / q) :=
              (Nat.mod_add_div a.1.val q).symm
            _ = q * (a.1.val / q) := by rw [a.2]; simp
        have hb' : b.1.val = q * (b.1.val / q) := by
          calc
            b.1.val = b.1.val % q + q * (b.1.val / q) :=
              (Nat.mod_add_div b.1.val q).symm
            _ = q * (b.1.val / q) := by rw [b.2]; simp
        rw [ha, hb', hquot])
    _ = m / q + 1 := by simp

/-- The first rank in a size-`q` batch. -/
def batchStart (rank q : ℕ) : ℕ := rank / q * q

theorem batchStart_le_rank (rank q : ℕ) : batchStart rank q ≤ rank :=
  Nat.div_mul_le_self _ _

theorem batchStart_add_of_mod_eq_zero {s q t : ℕ} (hq : 0 < q)
    (hs : s % q = 0) (ht : t < q) : batchStart (s + t) q = s := by
  have hrem : s % q + t % q < q := by
    calc
      s % q + t % q = t := by rw [hs, Nat.mod_eq_of_lt ht]; omega
      _ < q := ht
  have hdiv : (s + t) / q = s / q := by
    rw [Nat.add_div_eq_of_add_mod_lt hrem]
    simp [Nat.div_eq_of_lt ht]
  have hs' : q * (s / q) = s := by
    simpa [hs] using Nat.mod_add_div s q
  calc
    batchStart (s + t) q = ((s + t) / q) * q := rfl
    _ = (s / q) * q := by rw [hdiv]
    _ = q * (s / q) := Nat.mul_comm _ _
    _ = s := hs'

theorem batchStart_mod (rank q : ℕ) : batchStart rank q % q = 0 := by
  simp [batchStart]

theorem rank_eq_of_same_batch {r s q : ℕ}
    (hdiv : r / q = s / q) (hmod : r % q = s % q) : r = s := by
  calc
    r = r % q + q * (r / q) := (Nat.mod_add_div r q).symm
    _ = s % q + q * (s / q) := by rw [hmod, hdiv]
    _ = s := Nat.mod_add_div s q

/-- Any fixed positive power of `log n` is eventually bounded by any
positive multiple of `n`. -/
theorem eventually_log_rpow_le_linear {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.rpow (Real.log (n : ℝ)) s ≤ ε * (n : ℝ) := by
  have hreal : (fun x : ℝ => Real.rpow (Real.log x) s) =o[Filter.atTop] fun x => x := by
    simpa using (isLittleO_log_rpow_rpow_atTop s (by norm_num : (0 : ℝ) < 1))
  have hnat : (fun n : ℕ => Real.rpow (Real.log (n : ℝ)) s) =o[Filter.atTop]
      fun n => (n : ℝ) := hreal.comp_tendsto tendsto_natCast_atTop_atTop
  have hscaled := hnat.const_mul_right hε.ne'
  filter_upwards [hscaled.eventuallyLE, Filter.eventually_ge_atTop (2 : ℕ)] with n h hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn'
  have hleft : 0 ≤ Real.rpow (Real.log (n : ℝ)) s := Real.rpow_nonneg hlog _
  have hright : 0 ≤ ε * (n : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
  rw [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright] at h
  exact h

theorem log_eight_le_seven : Real.log (8 : ℝ) ≤ 7 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
  linarith

theorem log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

theorem log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem square_add_one_le_four_mul_sq {x : ℝ} (hx : 1 ≤ x) :
    (x + 1) ^ 2 ≤ 4 * x ^ 2 := by
  nlinarith [sq_nonneg (x - 1)]

theorem comparison_exp_argument {m a l : ℝ} (hm : 100 ≤ m)
    (ha : a ≤ m / 1000) (hl : l ≤ m / 1000) :
    Real.log 8 + 2 * a + 2 * l ≤ m * Real.log 2 := by
  have h8 := log_eight_le_seven
  have h2 := log_two_ge_half
  nlinarith

theorem capacity_exp_argument {m c l b : ℝ} (hm : 100 ≤ m)
    (hc : c ≤ l) (hl : l ≤ m / 1000) (hb : b ≤ m / 1000) :
    c + 201 * l + b ≤ m * Real.log 2 := by
  have h2 := log_two_ge_half
  have hc' : c ≤ m / 1000 := hc.trans hl
  have hmid : m / 1000 + 201 * (m / 1000) + m / 1000 ≤ m / 2 := by
    nlinarith
  calc
    c + 201 * l + b ≤ m / 1000 + 201 * (m / 1000) + m / 1000 := by gcongr
    _ ≤ m / 2 := hmid
    _ ≤ m * Real.log 2 := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (by simpa [one_div] using h2)
        (le_trans (by norm_num) hm)

theorem two_pow_le_of_log {n h : ℕ} (hn : 2 ≤ n)
    (hh : (h : ℝ) ≤ Real.log (n : ℝ)) :
    (2 : ℝ) ^ h ≤ (n : ℝ) := by
  have hlog2nonneg : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hlognnonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hmul : (h : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    calc
      (h : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hh hlog2nonneg
      _ ≤ Real.log (n : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left log_two_le_one hlognnonneg]
  have hlogpow : Real.log ((2 : ℝ) ^ h) = (h : ℝ) * Real.log 2 := by
    simpa [mul_comm] using (Real.log_pow (2 : ℝ) h)
  calc
    (2 : ℝ) ^ h = Real.exp ((h : ℝ) * Real.log 2) := by
      symm
      calc
        Real.exp ((h : ℝ) * Real.log 2) = Real.exp (Real.log ((2 : ℝ) ^ h)) :=
          congrArg Real.exp hlogpow.symm
        _ = (2 : ℝ) ^ h := Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2) _)
    _ ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr hmul
    _ = (n : ℝ) := Real.exp_log (by positivity)

theorem rpow_ac_eq_pow_200 {κ : CConsts} (hκ : κ.Admissible) (n : ℕ) :
    Real.rpow (n : ℝ) κ.Ac = (n : ℝ) ^ 200 := by
  rw [hκ.Ac_eq]
  simpa [Real.rpow_natCast]

theorem exists_paired_group_dimension {n : ℕ} (hn : 4 ≤ n) :
    ∃ h : ℕ, n ≤ 2 ^ h ∧ 2 ^ h < 2 * n := by
  let h := Nat.clog 2 n
  have hbase : 1 < 2 := by norm_num
  have hnlarge : 1 < n := by omega
  have hpos : 0 < h := by exact Nat.clog_pos hbase hnlarge
  have hpred : 2 ^ h.pred < n := Nat.pow_pred_clog_lt_self hbase hnlarge
  have hpow : 2 ^ h = 2 * 2 ^ h.pred := by
    have hpredSucc : Nat.succ h.pred = h := Nat.succ_pred_eq_of_pos hpos
    calc
      2 ^ h = 2 ^ Nat.succ h.pred := by rw [hpredSucc]
      _ = 2 ^ h.pred * 2 := by rw [Nat.pow_succ]
      _ = 2 * 2 ^ h.pred := Nat.mul_comm _ _
  refine ⟨h, ?_, ?_⟩
  · exact Nat.le_pow_clog hbase n
  · rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left hpred (by norm_num)

theorem exists_power_two_between {a : ℝ} (ha : 2 ≤ a) :
    ∃ d : ℕ, a ≤ (2 : ℝ) ^ d ∧ (2 : ℝ) ^ d < 2 * a := by
  let q := Nat.ceil a
  let d := Nat.clog 2 q
  have hqA : a ≤ (q : ℝ) := by exact Nat.le_ceil a
  have hqLt : (q : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith [ha])
  have hq2 : 2 ≤ q := by exact_mod_cast (ha.trans hqA)
  have hbase : 1 < 2 := by norm_num
  have hdPos : 0 < d := Nat.clog_pos hbase (by omega)
  have hpow : 2 ^ d = 2 * 2 ^ d.pred := by
    have hsucc : Nat.succ d.pred = d := Nat.succ_pred_eq_of_pos hdPos
    calc
      2 ^ d = 2 ^ Nat.succ d.pred := by rw [hsucc]
      _ = 2 ^ d.pred * 2 := by rw [Nat.pow_succ]
      _ = 2 * 2 ^ d.pred := Nat.mul_comm _ _
  have hpred : 2 ^ d.pred < q := Nat.pow_pred_clog_lt_self hbase (by omega)
  have hpredReal : (2 : ℝ) ^ d.pred + 1 ≤ (q : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hpred)
  have hpredLtA : (2 : ℝ) ^ d.pred < a := by linarith [hpredReal, hqLt]
  refine ⟨d, ?_, ?_⟩
  · have hqle : (q : ℝ) ≤ (2 : ℝ) ^ d := by exact_mod_cast Nat.le_pow_clog hbase q
    exact hqA.trans hqle
  · have hpowReal : (2 : ℝ) ^ d = 2 * (2 : ℝ) ^ d.pred := by exact_mod_cast hpow
    rw [hpowReal]
    nlinarith [hpredLtA]

theorem bin_card_mul_bin_size {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    (Fintype.card (Bin PT.tiling i) : ℕ) * (PT.tiling.P i).d =
      (PT.tiling.P i).M := by
  classical
  let p := PT.tiling.P i
  have hcard : Fintype.card (Bin PT.tiling i) = p.bins.parts.card := by
    change Fintype.card {B : Finset (Fin (T.S.N k)) // B ∈ p.bins.parts} = _
    rw [Fintype.card_subtype]
    simp
  calc
    Fintype.card (Bin PT.tiling i) * p.d = p.bins.parts.card * p.d := by rw [hcard]
    _ = ∑ B ∈ p.bins.parts, p.d := by simp
    _ = ∑ B ∈ p.bins.parts, B.card := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [hPT.tiling_valid.bins_card i B hB]
    _ = p.Y.card := p.bins.sum_card_parts
    _ = p.M := p.cardY

theorem two_pow_sub_zpow {n ell : ℕ} (hell : ell ≤ n) :
    (2 : ℝ) ^ n * (2 : ℝ) ^ (-(ell : ℤ)) = (2 : ℝ) ^ (n - ell) := by
  simpa [zpow_neg, zpow_natCast] using
    (pow_sub₀ (2 : ℝ) (by norm_num) hell).symm

theorem bin_size_pos {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    0 < (PT.tiling.P i).d := by
  classical
  let p := PT.tiling.P i
  have hparts : p.bins.parts.Nonempty := by
    by_contra hparts
    have hpartsEmpty : p.bins.parts = ∅ := Finset.not_nonempty_iff_eq_empty.mp hparts
    have hYempty : p.Y = ∅ := by
      rw [← p.bins.sup_parts]
      simp [hpartsEmpty]
    exact hPT.tiling_valid.patch_nonempty i |>.2.ne_empty hYempty
  by_contra hd
  have hdzero : p.d = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hd)
  obtain ⟨B, hB⟩ := hparts
  have hcard := hPT.tiling_valid.bins_card i B hB
  have hBzero : B.card = 0 := hcard.trans hdzero
  have hBempty : B = ∅ := Finset.card_eq_zero.mp hBzero
  have hBot : (∅ : Finset (Fin (T.S.N k))) ∈ p.bins.parts := by simpa [hBempty] using hB
  exact p.bins.bot_notMem hBot

theorem patch_mass_lower_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (n : ℕ) (hn : n = T.S.n k) (C0 : ℝ) (hC0 : C0 = 800 * (6 * κ.Kcell + 2))
    (hC0pos : 0 < C0) (hhost : C0 * (2 : ℝ) ^ n ≤ (T.S.N k : ℝ))
    (i : Fin PT.tiling.m) (hell : (PT.tiling.P i).ℓ ≤ n) :
    (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - (PT.tiling.P i).ℓ) ≤
      (PT.tiling.P i).M := by
  have hNpos : (0 : ℝ) < (T.S.N k : ℝ) :=
    lt_of_lt_of_le (mul_pos hC0pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)) hhost
  have hSpos : (0 : ℝ) < (PT.tiling.S : ℝ) :=
    lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 1 / 400) hNpos) hPT.tiling_valid.S_lower
  have hdyad := hPT.tiling_valid.dyadic_mass_upper i
  have hdyadMul : (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) * (PT.tiling.S : ℝ) <
      2 * (PT.tiling.P i).M := by
    have hmul := mul_lt_mul_of_pos_right hdyad hSpos
    calc
      (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) * (PT.tiling.S : ℝ) <
          (2 * (PT.tiling.P i).M / (PT.tiling.S : ℝ)) * (PT.tiling.S : ℝ) := hmul
      _ = 2 * (PT.tiling.P i).M := by field_simp [ne_of_gt hSpos]
  have hSloHalf : (T.S.N k : ℝ) / 800 ≤ (PT.tiling.S : ℝ) / 2 := by
    linarith [hPT.tiling_valid.S_lower]
  have hmassHalf : (PT.tiling.S : ℝ) / 2 *
      (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) < (PT.tiling.P i).M := by
    nlinarith [hdyadMul]
  have hmassBase : ((T.S.N k : ℝ) / 800) *
      (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) ≤ (PT.tiling.P i).M :=
    (mul_le_mul_of_nonneg_right hSloHalf (by positivity)).trans hmassHalf.le
  have hhostDiv : (C0 / 800) * (2 : ℝ) ^ n ≤ (T.S.N k : ℝ) / 800 := by
    nlinarith [hhost]
  have hhostMass : (C0 / 800) * (2 : ℝ) ^ n *
      (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) ≤
        ((T.S.N k : ℝ) / 800) * (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) :=
    mul_le_mul_of_nonneg_right hhostDiv (by positivity)
  have hC0eq : C0 / 800 = 6 * κ.Kcell + 2 := by rw [hC0]; ring
  calc
    (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - (PT.tiling.P i).ℓ) =
        (C0 / 800) * (2 : ℝ) ^ n * (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) := by
          calc
            _ = (C0 / 800) * (2 : ℝ) ^ (n - (PT.tiling.P i).ℓ) := by rw [hC0eq]
            _ = (C0 / 800) * ((2 : ℝ) ^ n *
                  (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ))) :=
              congrArg (fun x : ℝ => (C0 / 800) * x)
                (two_pow_sub_zpow hell).symm
            _ = _ := by ring
    _ ≤ ((T.S.N k : ℝ) / 800) *
          (2 : ℝ) ^ (-((PT.tiling.P i).ℓ : ℤ)) := hhostMass
    _ ≤ (PT.tiling.P i).M := hmassBase

theorem one_le_six_mul_add_two {K : ℝ} (hK : 0 < K) : 1 ≤ 6 * K + 2 := by
  nlinarith

theorem finLaw_expectation_const {α : Type*} [Fintype α] (μ : FinLaw α) (c : ℝ) :
    μ.E (fun _ => c) = c := by
  classical
  unfold FinLaw.E
  calc
    (∑ x, μ.w x * c) = (∑ x, μ.w x) * c := by rw [Finset.sum_mul]
    _ = c := by rw [μ.sum_one]; ring

theorem descFactorial_ratio_bound {B q : ℕ} (hB : 2 * q ^ 2 ≤ B) :
    (B : ℝ) ^ q / (B.descFactorial q : ℝ) ≤ 1 + (q : ℝ) ^ 2 / B := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hqplus : q ≤ q + 1 := by omega
      have hqpow : q ^ 2 ≤ (q + 1) ^ 2 := Nat.pow_le_pow_left hqplus 2
      have hBprev : 2 * q ^ 2 ≤ B := (Nat.mul_le_mul_left 2 hqpow).trans hB
      have hqplusPos : 1 ≤ q + 1 := by omega
      have hqplusBound : q + 1 ≤ 2 * (q + 1) ^ 2 := by nlinarith [hqplusPos]
      have hqleSucc : q + 1 ≤ B := hqplusBound.trans hB
      have hqle : q ≤ B := hqplus.trans hqleSucc
      have hqLt : q < B := Nat.lt_of_succ_le hqleSucc
      have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
      have hden : (0 : ℝ) < (B : ℝ) - (q : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt hqLt
      have hdescPos : (0 : ℝ) < (B.descFactorial q : ℝ) := by
        exact_mod_cast (Nat.descFactorial_pos.mpr hqle)
      have hdescSucc : (B.descFactorial (q + 1) : ℝ) =
          ((B - q : ℕ) : ℝ) * (B.descFactorial q : ℝ) := by
        rw [Nat.descFactorial_succ]
        norm_cast
      have hsub : ((B - q : ℕ) : ℝ) = (B : ℝ) - (q : ℝ) := by
        exact Nat.cast_sub hqle
      have hratioStep :
          (B : ℝ) ^ (q + 1) / (B.descFactorial (q + 1) : ℝ) =
            ((B : ℝ) ^ q / (B.descFactorial q : ℝ)) * ((B : ℝ) / ((B - q : ℕ) : ℝ)) := by
        rw [pow_succ, hdescSucc, hsub]
        field_simp [ne_of_gt hdescPos, ne_of_gt hden]
        <;> ring
      have hmono :
          ((B : ℝ) ^ q / (B.descFactorial q : ℝ)) * ((B : ℝ) / ((B - q : ℕ) : ℝ)) ≤
            (1 + (q : ℝ) ^ 2 / B) * ((B : ℝ) / ((B - q : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (ih hBprev)
          (div_nonneg (Nat.cast_nonneg B) (by rw [hsub]; exact hden.le))
      have hstepBound :
          (1 + (q : ℝ) ^ 2 / B) * ((B : ℝ) / ((B - q : ℕ) : ℝ)) ≤
            1 + ((q + 1 : ℕ) : ℝ) ^ 2 / B := by
        have hBne : (B : ℝ) ≠ 0 := hBpos.ne'
        have hBreal : 2 * ((q : ℝ) + 1) ^ 2 ≤ (B : ℝ) := by exact_mod_cast hB
        have hqB : (q : ℝ) * ((q : ℝ) + 1) ≤ (B : ℝ) := by nlinarith [hBreal]
        have hgap : 0 ≤ (B : ℝ) - (q : ℝ) * ((q : ℝ) + 1) := by linarith [hqB]
        have hterm : 0 ≤ ((q : ℝ) + 1) * ((B : ℝ) - (q : ℝ) * ((q : ℝ) + 1)) :=
          mul_nonneg (by positivity) hgap
        rw [hsub, ← mul_div_assoc]
        apply (div_le_iff₀ hden).2
        field_simp [hBne]
        have hdiff :
            ((B : ℝ) + ((q + 1 : ℕ) : ℝ) ^ 2) * ((B : ℝ) - q) -
              (B : ℝ) * ((B : ℝ) + (q : ℝ) ^ 2) =
                ((q : ℝ) + 1) * ((B : ℝ) - (q : ℝ) * ((q : ℝ) + 1)) := by
          simp only [Nat.cast_add, Nat.cast_one]
          ring
        linarith [hdiff, hterm]
      rw [hratioStep]
      exact hmono.trans hstepBound

theorem capacity_product_bound {n ell : ℕ} {K E d : ℝ}
    (hn : 4 ≤ n) (hell : ell ≤ n) (hpowEll : (2 : ℝ) ^ ell ≤ (n : ℝ))
    (hd : d ≤ (n : ℝ)) (hK : 0 < K) (hE : 0 ≤ E)
    (hcapacity : 2 * (K + 1) * (n : ℝ) ^ 201 * E ≤ (2 : ℝ) ^ n) :
    (3 * (2 : ℝ) ^ (n - ell) / (n : ℝ) ^ 200 + E) *
      (K * (n : ℝ) ^ 200 + d) ≤ (6 * K + 2) * (2 : ℝ) ^ (n - ell) := by
  let N : ℝ := n
  let u : ℝ := (2 : ℝ) ^ (n - ell)
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hNone : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (show 1 ≤ n by omega)
  have hNfour : (4 : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have hDsmall : 3 * d ≤ N ^ 200 := by
    have h199 : (3 : ℝ) ≤ N ^ 199 := by
      calc
        3 ≤ 4 ^ 199 := by norm_num
        _ ≤ N ^ 199 := by gcongr
    calc
      3 * d ≤ 3 * N := mul_le_mul_of_nonneg_left hd (by norm_num)
      _ ≤ N ^ 199 * N := mul_le_mul_of_nonneg_right h199 (Nat.cast_nonneg n)
      _ = N ^ 200 := by ring
  have hfirstFactor : K * N ^ 200 + d ≤ (K + 1 / 3) * N ^ 200 := by
    nlinarith [hDsmall]
  have hfirst : (3 * u / N ^ 200) * (K * N ^ 200 + d) ≤ (3 * K + 1) * u := by
    calc
      (3 * u / N ^ 200) * (K * N ^ 200 + d) ≤
          (3 * u / N ^ 200) * ((K + 1 / 3) * N ^ 200) :=
        mul_le_mul_of_nonneg_left hfirstFactor (by positivity)
      _ = (3 * K + 1) * u := by
        have hNpow : N ^ 200 ≠ 0 := (pow_pos hNpos _).ne'
        field_simp [hNpow]
        <;> ring
  have hNlePow : N ≤ N ^ 200 := by
    calc
      N = N * 1 := by ring
      _ ≤ N * N ^ 199 := mul_le_mul_of_nonneg_left (one_le_pow₀ hNone) hNpos.le
      _ = N ^ 200 := by ring
  have hsecondFactor : K * N ^ 200 + d ≤ (K + 1) * N ^ 200 := by
    have hdleN200 : d ≤ N ^ 200 := hd.trans hNlePow
    calc
      K * N ^ 200 + d ≤ K * N ^ 200 + N ^ 200 :=
        by nlinarith [hdleN200]
      _ = (K + 1) * N ^ 200 := by ring
  have hpowSplit : (2 : ℝ) ^ n = u * (2 : ℝ) ^ ell := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n - ell + ell) :=
        congrArg (fun m : ℕ => (2 : ℝ) ^ m) (Nat.sub_add_cancel hell).symm
      _ = u * (2 : ℝ) ^ ell := by simp [u, pow_add]
  have hcapacityBase : 2 * (K + 1) * N ^ 201 * E ≤ u * N := by
    calc
      2 * (K + 1) * N ^ 201 * E ≤ (2 : ℝ) ^ n := by simpa [N] using hcapacity
      _ = u * (2 : ℝ) ^ ell := hpowSplit
      _ ≤ u * N := mul_le_mul_of_nonneg_left hpowEll (by positivity)
  have hden : 0 < 2 * N := by positivity
  have hcapacityDiv :
      (2 * (K + 1) * N ^ 201 * E) / (2 * N) ≤ (u * N) / (2 * N) :=
    div_le_div_of_nonneg_right hcapacityBase (by positivity)
  have hsecond : E * (K * N ^ 200 + d) ≤ u / 2 := by
    calc
      E * (K * N ^ 200 + d) ≤ E * ((K + 1) * N ^ 200) :=
        mul_le_mul_of_nonneg_left hsecondFactor hE
      _ = (2 * (K + 1) * N ^ 201 * E) / (2 * N) := by
        have hNne : N ≠ 0 := ne_of_gt hNpos
        field_simp [hNne]
        <;> ring
      _ ≤ (u * N) / (2 * N) := hcapacityDiv
      _ = u / 2 := by field_simp [ne_of_gt hNpos]
  have hfinal : (3 * K + 1) * u + u / 2 ≤ (6 * K + 2) * u := by
    have hu : 0 ≤ u := by dsimp [u]; positivity
    nlinarith [hK, hu]
  calc
    (3 * (2 : ℝ) ^ (n - ell) / (n : ℝ) ^ 200 + E) *
        (K * (n : ℝ) ^ 200 + d) =
        (3 * u / N ^ 200) * (K * N ^ 200 + d) + E * (K * N ^ 200 + d) := by
          simp [u, N]
          <;> ring
    _ ≤ (3 * K + 1) * u + u / 2 := add_le_add hfirst hsecond
    _ ≤ (6 * K + 2) * (2 : ℝ) ^ (n - ell) := by simpa [u] using hfinal

end HypercubeRamsey.Lane_q_s16_geom
