import HypercubeRamsey.S07.AnchorStage_q_s07_anchor
import HypercubeRamsey.S07.AnchorStage_q_s07_anchor_moments

namespace HypercubeRamsey.S07

open Classical
open scoped BigOperators

theorem cellRow_nonneg_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (c : Γ.Cell) (y : Fin N) :
    0 ≤ cellRow Γ M σ W c y := by
  classical
  dsimp [cellRow]
  split_ifs with hv
  · by_cases hm : 0 < filterMass E G (M.ν (σ c.1)) (cellLabels Γ W c)
    · exact (filt_probability_and_support E G (M.ν (σ c.1))
        (cellLabels Γ W c) hm).1 y
    · simp [filt, hm]
  · exact le_rfl

theorem inv_one_sub_pow_le_two_pow_q_s07_anchor
    {x : ℝ} {r m K : ℕ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hxK : x * (K : ℝ) ≤ 1 / 2) (hr : r ≤ m * K) :
    ((1 - x) ^ r)⁻¹ ≤ (2 : ℝ) ^ m := by
  have hbase0 : 0 ≤ 1 - x := sub_nonneg.mpr (le_of_lt hx1)
  have hbase1 : 1 - x ≤ 1 := sub_le_self 1 hx0
  have hpowK : (1 / 2 : ℝ) ≤ (1 - x) ^ K := by
    have h := one_sub_pow_lower hx0 (le_of_lt hx1) K
    have hxK' : (K : ℝ) * x ≤ 1 / 2 := by nlinarith [hxK]
    linarith
  have hpowKm : (1 / 2 : ℝ) ^ m ≤ (1 - x) ^ (m * K) := by
    calc
      (1 / 2 : ℝ) ^ m ≤ ((1 - x) ^ K) ^ m :=
        pow_le_pow_left₀ (by norm_num) hpowK m
      _ = (1 - x) ^ (K * m) := by rw [pow_mul]
      _ = (1 - x) ^ (m * K) := by rw [Nat.mul_comm]
  have hpowR : (1 - x) ^ (m * K) ≤ (1 - x) ^ r :=
    pow_le_pow_of_le_one hbase0 hbase1 hr
  have hlow : (1 / 2 : ℝ) ^ m ≤ (1 - x) ^ r := hpowKm.trans hpowR
  have hInv := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ m) hlow
  calc
    ((1 - x) ^ r)⁻¹ = 1 / (1 - x) ^ r := by rw [one_div]
    _ ≤ 1 / (1 / 2 : ℝ) ^ m := by simpa only [one_div] using hInv
    _ = (2 : ℝ) ^ m := by
      have hhalf : (1 / 2 : ℝ) ^ m = ((2 : ℝ) ^ m)⁻¹ := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
      rw [hhalf]
      simp

theorem anchor_moment_factor_small_q_s07_anchor
    {x : ℝ} {m K r : ℕ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hxK : x * (K : ℝ) ≤ 1 / 2) (hr : r ≤ m * K) :
    ((1 - x) ^ r)⁻¹ ≤ (2 : ℝ) ^ m :=
  inv_one_sub_pow_le_two_pow_q_s07_anchor hx0 hx1 hxK hr

theorem pi_expect_prod_disjoint_q_s07_anchor
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (f : κ → (∀ i, Ω i) → ℝ) (sc : κ → Finset ι)
    (S : Finset κ)
    (hdep : ∀ k ∈ S, FinProb.DependsOn (f k) (sc k))
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (sc i) (sc j)) :
    (FinProb.pi P).expect (fun ω => ∏ k ∈ S, f k ω) =
      ∏ k ∈ S, (FinProb.pi P).expect (f k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      simpa [FinProb.expect] using (FinProb.pi P).sum_eq_one
  | @insert a S ha ih =>
      have hdepA : FinProb.DependsOn (f a) (sc a) := hdep a (by simp)
      have hdepS : ∀ k ∈ S, FinProb.DependsOn (f k) (sc k) := by
        intro k hk
        exact hdep k (by simp [hk])
      have hdisjS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (sc i) (sc j) := by
        intro i hi j hj hne
        exact hdisj i (by simp [hi]) j (by simp [hj]) hne
      let U : Finset ι := S.biUnion sc
      have hdepProd : FinProb.DependsOn (fun ω => ∏ k ∈ S, f k ω) U := by
        intro ω ω' hω
        apply Finset.prod_congr rfl
        intro k hk
        apply hdepS k hk
        intro v hv
        exact hω v (Finset.mem_biUnion.mpr ⟨k, hk, hv⟩)
      have hdisjAU : Disjoint (sc a) U := by
        apply Finset.disjoint_left.mpr
        intro v hva hvU
        rcases Finset.mem_biUnion.mp hvU with ⟨k, hk, hkv⟩
        have hne : a ≠ k := by
          intro hEq
          subst k
          exact ha hk
        have h := Finset.disjoint_left.mp
          (hdisj a (by simp) k (by simp [hk]) hne) hva
        exact h hkv
      have hmul := FinProb.pi_expect_mul_of_disjoint P (f a)
        (fun ω => ∏ k ∈ S, f k ω) (sc a) U hdepA hdepProd hdisjAU
      calc
        (FinProb.pi P).expect (fun ω => ∏ k ∈ insert a S, f k ω) =
            (FinProb.pi P).expect (fun ω => f a ω * ∏ k ∈ S, f k ω) := by
              congr 1
              funext ω
              rw [Finset.prod_insert ha]
        _ = (FinProb.pi P).expect (f a) *
            (FinProb.pi P).expect (fun ω => ∏ k ∈ S, f k ω) := hmul
        _ = (FinProb.pi P).expect (f a) * ∏ k ∈ S, (FinProb.pi P).expect (f k) := by
              rw [ih hdepS hdisjS]
        _ = ∏ k ∈ insert a S, (FinProb.pi P).expect (f k) := by
              rw [Finset.prod_insert ha]

theorem pi_glue_expect_eq_q_s07_anchor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (U : Finset ι) (Φ : (∀ i, Ω i) → ℝ)
    (ω₀ : ∀ i, Ω i) (hΦ : FinProb.DependsOn Φ U) (ω : ∀ i, Ω i) :
    (FinProb.pi (fun i : {i // i ∈ U} => P i.1)).expect
        (fun a => Φ (glue U ω a)) = (FinProb.pi P).expect Φ := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ U) Ω
  let b₀ : ∀ i : {i // i ∉ U}, Ω i.1 := fun i => ω₀ i.1
  have hdep := FinProb.pi_expect_depends P U Φ ω₀ hΦ
  have hEval (a : ∀ i : {i // i ∈ U}, Ω i.1) :
      Φ (glue U ω a) = Φ (e.symm (a, b₀)) := by
    apply hΦ
    intro i hi
    simp [e, b₀, glue, hi]
  calc
    (FinProb.pi (fun i : {i // i ∈ U} => P i.1)).expect
        (fun a => Φ (glue U ω a)) =
      (FinProb.pi (fun i : {i // i ∈ U} => P i.1)).expect
        (fun a => Φ (e.symm (a, b₀))) := by
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro a ha
          change (FinProb.pi (fun i : {i // i ∈ U} => P i.1)).w a * Φ (glue U ω a) =
            (FinProb.pi (fun i : {i // i ∈ U} => P i.1)).w a * Φ (e.symm (a, b₀))
          rw [hEval a]
    _ = (FinProb.pi P).expect Φ := by simpa [e, b₀] using hdep.symm

theorem fullNames_disjoint_of_keyDist_q_s07_anchor
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) (c c' : Γ.Cell)
    (hsep : 3 ≤ Γ.keyDist c.1 c'.1) :
    Disjoint (Γ.fullNames c).toFinset (Γ.fullNames c').toFinset := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  have hwc : w ∈ Γ.fullNames c := List.mem_toFinset.mp hw
  have hwc' : w ∈ Γ.fullNames c' := List.mem_toFinset.mp hw'
  have hcw : Γ.cellDist c w ≤ 1 := fullNames_cellDist_le_one Γ c w hwc
  have hc'w : Γ.cellDist c' w ≤ 1 := fullNames_cellDist_le_one Γ c' w hwc'
  have hsymm : Γ.cellDist w c' = Γ.cellDist c' w := by
    simp [GridGeom.cellDist, GridGeom.keyDist, GridGeom.auxDist,
      Nat.dist_comm, ne_comm]
  have htri := cellDist_triangle Γ c w c'
  have hcell : Γ.cellDist c c' ≤ 2 := by omega
  have hkey : Γ.keyDist c.1 c'.1 ≤ Γ.cellDist c c' := by
    simp [GridGeom.cellDist]
  omega

theorem cellRow_depends_on_fullNames_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (c : Γ.Cell) (y : Fin N) :
    FinProb.DependsOn (fun W => cellRow Γ M σ W c y) (Γ.fullNames c).toFinset := by
  intro W W' hW
  exact cellRow_eq_of_fullNames Γ M σ W W' c
    (fun w hw => hW w (List.mem_toFinset.mpr hw)) y

private theorem finprob_nonempty_q_s07_anchor {α : Type*} [Fintype α]
    (P : FinProb α) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := ⟨fun a => h ⟨a⟩⟩
  have hsum := P.sum_eq_one
  simp at hsum

noncomputable def rawAnchorRowMean_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (c : Γ.Cell) (y : Fin N) : ℝ :=
  (rawAnchors Γ M σ).expect (fun W => cellRow Γ M σ W c y)

theorem rawAnchorRowMean_nonneg_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (c : Γ.Cell) (y : Fin N) :
    0 ≤ rawAnchorRowMean_q_s07_anchor Γ M σ c y := by
  classical
  unfold rawAnchorRowMean_q_s07_anchor FinProb.expect
  apply Finset.sum_nonneg
  intro W hW
  exact mul_nonneg ((rawAnchors Γ M σ).nonneg W)
    (cellRow_nonneg_q_s07_anchor Γ M σ W c y)

theorem rawAnchorRowMean_eq_of_keyBall_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ σ' : Γ.Key → M.ι) (c : Γ.Cell) (y : Fin N)
    (hσ : ∀ g ∈ Γ.keyBall c.1 1, σ g = σ' g) :
    rawAnchorRowMean_q_s07_anchor Γ M σ c y =
      rawAnchorRowMean_q_s07_anchor Γ M σ' c y := by
  classical
  let S : Finset (Γ.Cell) := (Γ.fullNames c).toFinset
  let Pσ : Γ.Cell → FinProb (Fin N) := fun w => M.μ (σ w.1)
  let Pσ' : Γ.Cell → FinProb (Fin N) := fun w => M.μ (σ' w.1)
  let Fσ : (Γ.Cell → Fin N) → ℝ := fun W => cellRow Γ M σ W c y
  let Fσ' : (Γ.Cell → Fin N) → ℝ := fun W => cellRow Γ M σ' W c y
  let W₀ : Γ.Cell → Fin N := Classical.choice (finprob_nonempty_q_s07_anchor
    (rawAnchors Γ M σ))
  have hdepσ : FinProb.DependsOn Fσ S := by
    intro W W' hW
    exact cellRow_eq_of_fullNames Γ M σ W W' c
      (fun w hw => hW w (List.mem_toFinset.mpr hw)) y
  have hdepσ' : FinProb.DependsOn Fσ' S := by
    intro W W' hW
    exact cellRow_eq_of_fullNames Γ M σ' W W' c
      (fun w hw => hW w (List.mem_toFinset.mpr hw)) y
  let e := Equiv.piEquivPiSubtypeProd (fun w : Γ.Cell => w ∈ S) (fun _ => Fin N)
  let b₀ : ∀ w : {w : Γ.Cell // w ∉ S}, Fin N := fun w => W₀ w.1
  have hcenter : σ c.1 = σ' c.1 := by
    apply hσ c.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [GridGeom.keyDist]
  have hnameKey (w : Γ.Cell) (hw : w ∈ Γ.fullNames c) :
      w.1 ∈ Γ.keyBall c.1 1 := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hdist := fullNames_cellDist_le_one Γ c w hw
    have hkey : Γ.keyDist c.1 w.1 ≤ Γ.cellDist c w := by
      simp [GridGeom.cellDist]
    have hkey' : Γ.keyDist c.1 w.1 ≤ 1 := hkey.trans hdist
    simpa [GridGeom.keyBall] using hkey'
  have hweights (a : ∀ w : {w : Γ.Cell // w ∈ S}, Fin N) :
      (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pσ w.1)).w a =
        (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pσ' w.1)).w a := by
    simp only [FinProb.pi]
    apply Finset.prod_congr rfl
    intro w hw
    have htag := hσ (w.1).1 (hnameKey w.1 (List.mem_toFinset.mp w.2))
    change (M.μ (σ (w.1).1)).w (a w) = (M.μ (σ' (w.1).1)).w (a w)
    exact congrArg (fun τ => (M.μ τ).w (a w)) htag
  have hfun (a : ∀ w : {w : Γ.Cell // w ∈ S}, Fin N) :
      Fσ (e.symm (a, b₀)) = Fσ' (e.symm (a, b₀)) := by
    have hvalid : CellValid Γ M σ (e.symm (a, b₀)) c =
        CellValid Γ M σ' (e.symm (a, b₀)) c := by
      simp [CellValid, hcenter]
    simp [Fσ, Fσ', cellRow, hvalid, hcenter]
  have hleft := FinProb.pi_expect_depends Pσ S Fσ W₀ hdepσ
  have hright := FinProb.pi_expect_depends Pσ' S Fσ' W₀ hdepσ'
  change (FinProb.pi Pσ).expect Fσ = (FinProb.pi Pσ').expect Fσ'
  rw [hleft, hright]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro a ha
  rw [hweights a]
  change (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pσ' w.1)).w a *
      Fσ (e.symm (a, b₀)) =
    (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pσ' w.1)).w a *
      Fσ' (e.symm (a, b₀))
  rw [hfun a]

theorem keyBall_disjoint_of_keyDist_q_s07_anchor
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) (g h : Γ.Key)
    (hsep : 3 ≤ Γ.keyDist g h) :
    Disjoint (Γ.keyBall g 1) (Γ.keyBall h 1) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hk hk'
  have hgk : Γ.keyDist g k ≤ 1 := (Finset.mem_filter.mp hk).2
  have hhk : Γ.keyDist h k ≤ 1 := (Finset.mem_filter.mp hk').2
  have hkh : Γ.keyDist k h ≤ 1 := by
    unfold GridGeom.keyDist at *
    simpa [Nat.dist_comm] using hhk
  have htri : Γ.keyDist g h ≤ Γ.keyDist g k + Γ.keyDist k h := by
    unfold GridGeom.keyDist
    calc
      (∑ r, Nat.dist (g r) (h r)) ≤
          ∑ r, (Nat.dist (g r) (k r) + Nat.dist (k r) (h r)) := by
        apply Finset.sum_le_sum
        intro r hr
        exact Nat.dist.triangle_inequality (g r) (k r) (h r)
      _ = (∑ r, Nat.dist (g r) (k r)) + ∑ r, Nat.dist (k r) (h r) :=
        Finset.sum_add_distrib
  omega

theorem keyDist_triangle_q_s07_anchor
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (g h k : Γ.Key) : Γ.keyDist g k ≤ Γ.keyDist g h + Γ.keyDist h k := by
  unfold GridGeom.keyDist
  calc
    (∑ r, Nat.dist (g r) (k r)) ≤
        ∑ r, (Nat.dist (g r) (h r) + Nat.dist (h r) (k r)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact Nat.dist.triangle_inequality (g r) (h r) (k r)
    _ = (∑ r, Nat.dist (g r) (h r)) + ∑ r, Nat.dist (h r) (k r) :=
      Finset.sum_add_distrib

set_option maxHeartbeats 1000000 in
theorem odd_moment_at_n_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (Q : Γ.Key → FinProb M.ι) (D₀ : ℝ)
    (hCPB : CondProductBound) (hGeom : GeomFacts Γ) (hTag : TagLLL Γ M Q D₀)
    (hAnchor : ∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) → AnchorLLL Γ M D₀ σ)
    (hx0 : 0 ≤ xL D₀ n) (hx1 : xL D₀ n < 1)
    (hcharge : xL D₀ n * ((2 * s + q + 1 : ℕ) : ℝ) ^ 4 ≤ 1 / 2) :
    OddMoment Γ M Q D₀ := by
  classical
  intro y m hm u hsep
  let c : Fin m → Γ.Cell := fun i => Γ.key (u i).1
  let scopeA : Fin m → Finset Γ.Cell := fun i => (Γ.fullNames (c i)).toFinset
  let UA : Finset Γ.Cell := Finset.univ.biUnion scopeA
  let scopeT : Fin m → Finset Γ.Key := fun i => Γ.keyBall (c i).1 1
  let UT : Finset Γ.Key := Finset.univ.biUnion scopeT
  let Pcell : (Γ.Key → M.ι) → Γ.Cell → FinProb (Fin N) := fun τ a => M.μ (τ a.1)
  let badA : (Γ.Key → M.ι) → Γ.Cell → (Γ.Cell → Fin N) → Prop :=
    fun τ a W => CellBad Γ M τ W a
  let ballA : Γ.Cell → Finset Γ.Cell := fun a => Γ.cellBall a 2
  let badT : Γ.Key → (Γ.Key → M.ι) → Prop := fun g τ => TagBad Γ M D₀ τ g
  let ballT : Γ.Key → Finset Γ.Key := fun g => Γ.keyBall g 1
  let FA : (Γ.Key → M.ι) → Fin m → (Γ.Cell → Fin N) → ℝ := fun τ i W =>
    (N : ℝ) * cellRow Γ M τ W (c i) y
  let PhiA : (Γ.Key → M.ι) → (Γ.Cell → Fin N) → ℝ := fun τ W =>
    ∏ i, FA τ i W
  let BA : (Γ.Key → M.ι) → ℝ := fun τ =>
    ∏ i, (FinProb.pi (fun a : Γ.Cell => M.μ (τ a.1))).expect (FA τ i)
  let FT : Fin m → (Γ.Key → M.ι) → ℝ := fun i τ =>
    (N : ℝ) * rawAnchorRowMean_q_s07_anchor Γ M τ (c i) y
  let PhiT : (Γ.Key → M.ι) → ℝ := fun τ => ∏ i, FT i τ
  let BT : ℝ := ∏ i, (FinProb.pi Q).expect (FT i)
  let cellBase : ℕ := 2 * s + q + 1
  let cellTouch : ℕ := cellBase ^ 3
  let keyTouch : ℕ := (2 * s + 1) ^ 2
  let GoodTag : (Γ.Key → M.ι) → Prop := fun τ => ∀ g, ¬ TagBad Γ M D₀ τ g
  have hcellBase : 1 ≤ cellBase := by dsimp [cellBase]; omega
  have hcellPow : (cellBase : ℝ) ^ 3 ≤ (cellBase : ℝ) ^ 4 :=
    pow_le_pow_right₀ (by exact_mod_cast hcellBase) (by omega)
  have hcellCharge : xL D₀ n * (cellTouch : ℝ) ≤ 1 / 2 := by
    dsimp [cellTouch]
    calc
      xL D₀ n * ((cellBase ^ 3 : ℕ) : ℝ) ≤
          xL D₀ n * (cellBase : ℝ) ^ 3 := by norm_num
      _ ≤ xL D₀ n * (cellBase : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hcellPow hx0
      _ ≤ 1 / 2 := hcharge
  have hkeyBase : (2 * s + 1 : ℕ) ≤ cellBase := by dsimp [cellBase]; omega
  have hkeyTouchLE : keyTouch ≤ cellBase ^ 4 := by
    dsimp [keyTouch]
    calc
      (2 * s + 1) ^ 2 ≤ cellBase ^ 2 := Nat.pow_le_pow_left hkeyBase 2
      _ ≤ cellBase ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hxKey : xL D₀ n * ((cellBase ^ 4 : ℕ) : ℝ) ≤ 1 / 2 := by
    simpa [cellBase, Nat.cast_pow] using hcharge
  have hkeyCharge : xL D₀ n * (keyTouch : ℝ) ≤ 1 / 2 := by
    have hcastLE : (keyTouch : ℝ) ≤ ((cellBase ^ 4 : ℕ) : ℝ) := by exact_mod_cast hkeyTouchLE
    calc
      xL D₀ n * (keyTouch : ℝ) ≤ xL D₀ n * ((cellBase ^ 4 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hcastLE hx0
      _ ≤ 1 / 2 := hxKey
  have hscopeADisj : ∀ i j, i ≠ j → Disjoint (scopeA i) (scopeA j) := by
    intro i j hne
    exact fullNames_disjoint_of_keyDist_q_s07_anchor Γ (c i) (c j) (hsep i j hne)
  have hscopeTDisj : ∀ i j, i ≠ j → Disjoint (scopeT i) (scopeT j) := by
    intro i j hne
    exact keyBall_disjoint_of_keyDist_q_s07_anchor Γ (c i).1 (c j).1 (hsep i j hne)
  have hdepFA : ∀ τ i, FinProb.DependsOn (FA τ i) (scopeA i) := by
    intro τ i W W' hW
    dsimp [FA, scopeA, c]
    apply congrArg (fun z => (N : ℝ) * z)
    exact cellRow_depends_on_fullNames_q_s07_anchor Γ M τ (c i) y W W' hW
  have hdepPhiA (τ : Γ.Key → M.ι) : FinProb.DependsOn (PhiA τ) UA := by
    intro W W' hW
    dsimp [PhiA]
    apply Finset.prod_congr rfl
    intro i hi
    exact hdepFA τ i W W' (fun w hw => hW w
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hw⟩))
  have hdepFT : ∀ i, FinProb.DependsOn (FT i) (scopeT i) := by
    intro i τ τ' hτ
    dsimp [FT]
    apply congrArg (fun z => (N : ℝ) * z)
    exact rawAnchorRowMean_eq_of_keyBall_q_s07_anchor Γ M τ τ' (c i) y
      hτ
  have hdepPhiT : FinProb.DependsOn PhiT UT := by
    intro τ τ' hAgree
    dsimp [PhiT]
    apply Finset.prod_congr rfl
    intro i hi
    exact hdepFT i τ τ' (fun g hg => hAgree g
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hg⟩))
  have hFA0 (τ : Γ.Key → M.ι) (i : Fin m) (W : Γ.Cell → Fin N) : 0 ≤ FA τ i W := by
    dsimp [FA]
    exact mul_nonneg (Nat.cast_nonneg N) (cellRow_nonneg_q_s07_anchor Γ M τ W (c i) y)
  have hPhiA0 (τ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) : 0 ≤ PhiA τ W := by
    dsimp [PhiA]
    exact Finset.prod_nonneg fun i hi => hFA0 τ i W
  have hFT0 (i : Fin m) (τ : Γ.Key → M.ι) : 0 ≤ FT i τ := by
    dsimp [FT]
    exact mul_nonneg (show 0 ≤ (N : ℝ) by positivity)
      (rawAnchorRowMean_nonneg_q_s07_anchor Γ M τ (c i) y)
  have hPhiT0 (τ : Γ.Key → M.ι) : 0 ≤ PhiT τ := by
    dsimp [PhiT]
    exact Finset.prod_nonneg fun i hi => hFT0 i τ
  have hBT0 : 0 ≤ BT := by
    dsimp [BT]
    apply Finset.prod_nonneg
    intro i hi
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro τ hτ
    exact mul_nonneg ((FinProb.pi Q).nonneg τ) (hFT0 i τ)
  have hMeanFT (i : Fin m) : (FinProb.pi Q).expect (FT i) =
      (N : ℝ) * rawRowMean Γ M Q (c i) y := by
    dsimp [FT, rawRowMean, rawAnchorRowMean_q_s07_anchor]
    rw [FinProb.expect_smul]
  have hFullT : (FinProb.pi Q).expect PhiT = BT := by
    have h := pi_expect_prod_disjoint_q_s07_anchor Q FT scopeT Finset.univ
      (by intro i hi; exact hdepFT i) (by intro i hi j hj hne; exact hscopeTDisj i j hne)
    simpa [PhiT, BT] using h
  have hBTrow : BT = ∏ i, (N : ℝ) * rawRowMean Γ M Q (c i) y := by
    dsimp [BT]
    apply Finset.prod_congr rfl
    intro i hi
    exact hMeanFT i
  have hDmean : ∀ i, 0 ≤ (N : ℝ) * rawRowMean Γ M Q (c i) y := by
    intro i
    exact mul_nonneg (Nat.cast_nonneg N)
      (odd_raw_row_mean_nonneg_q_s07_anchor Γ M Q (c i) y)
  have hkeyTriangle : ∀ a b k : Γ.Key,
      Γ.keyDist a b ≤ Γ.keyDist a k + Γ.keyDist k b := fun a b k =>
    keyDist_triangle_q_s07_anchor Γ a k b
  let touchA : Finset Γ.Cell := Finset.univ.filter fun a => ¬ Disjoint (ballA a) UA
  have htouchASub : touchA ⊆
      Finset.univ.biUnion fun i : Fin m => Γ.cellBall (c i) 3 := by
    intro a ha
    have hnot := (Finset.mem_filter.mp ha).2
    rcases Finset.not_disjoint_iff.mp hnot with ⟨w, hwA, hwU⟩
    rcases Finset.mem_biUnion.mp hwU with ⟨i, hi, hwi⟩
    have hrow : Γ.cellDist (c i) w ≤ 1 :=
      fullNames_cellDist_le_one Γ (c i) w (List.mem_toFinset.mp hwi)
    have hball : Γ.cellDist a w ≤ 2 := (Finset.mem_filter.mp hwA).2
    have hsymm : Γ.cellDist w a = Γ.cellDist a w := by
      simp [GridGeom.cellDist, GridGeom.keyDist, GridGeom.auxDist, Nat.dist_comm, ne_comm]
    have htri := cellDist_triangle Γ (c i) w a
    have hcenter : Γ.cellDist (c i) a ≤ 3 := by omega
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcenter⟩⟩
  have htouchACard : touchA.card ≤ m * cellTouch := by
    calc
      touchA.card ≤ (Finset.univ.biUnion fun i : Fin m => Γ.cellBall (c i) 3).card :=
        Finset.card_le_card htouchASub
      _ ≤ ∑ i ∈ Finset.univ, (Γ.cellBall (c i) 3).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Finset.univ, cellTouch := by
        apply Finset.sum_le_sum
        intro i hi
        have hball : (Γ.cellBall (c i) 3).card ≤ cellTouch := by
          have h := hGeom.balls.cellBall_card (c i) 3
          dsimp [cellTouch, cellBase]
          exact_mod_cast h
        exact hball
      _ = m * cellTouch := by simp [cellTouch]
  let touchT : Finset Γ.Key := Finset.univ.filter fun g => ¬ Disjoint (ballT g) UT
  have htouchTSub : touchT ⊆
      Finset.univ.biUnion fun i : Fin m => Γ.keyBall (c i).1 2 := by
    intro g hg
    have hnot := (Finset.mem_filter.mp hg).2
    rcases Finset.not_disjoint_iff.mp hnot with ⟨k, hkg, hkU⟩
    rcases Finset.mem_biUnion.mp hkU with ⟨i, hi, hki⟩
    have hgk : Γ.keyDist g k ≤ 1 := (Finset.mem_filter.mp hkg).2
    have hik : Γ.keyDist (c i).1 k ≤ 1 := (Finset.mem_filter.mp hki).2
    have hki' : Γ.keyDist k (c i).1 ≤ 1 := by
      simpa [GridGeom.keyDist, Nat.dist_comm] using hik
    have hgi : Γ.keyDist g (c i).1 ≤ 2 := by
      have htri := hkeyTriangle g (c i).1 k
      omega
    have hig : Γ.keyDist (c i).1 g ≤ 2 := by
      simpa [GridGeom.keyDist, Nat.dist_comm] using hgi
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hig⟩⟩
  have htouchTCard : touchT.card ≤ m * keyTouch := by
    calc
      touchT.card ≤ (Finset.univ.biUnion fun i : Fin m => Γ.keyBall (c i).1 2).card :=
        Finset.card_le_card htouchTSub
      _ ≤ ∑ i ∈ Finset.univ, (Γ.keyBall (c i).1 2).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Finset.univ, keyTouch := by
        apply Finset.sum_le_sum
        intro i hi
        have hball : (Γ.keyBall (c i).1 2).card ≤ keyTouch := by
          have h := hGeom.balls.keyBall_card (c i).1 2
          dsimp [keyTouch]
          exact_mod_cast h
        exact hball
      _ = m * keyTouch := by simp [keyTouch]
  have hxCell : xL D₀ n * (cellTouch : ℝ) ≤ 1 / 2 := hcellCharge
  have hTagInput : LLLInput Q badT ballT (xL D₀ n) ((2 * s + 1) ^ 2) := by
    simpa [TagLLL, badT, ballT] using hTag
  have hTagCP := hCPB Q badT ballT (xL D₀ n) ((2 * s + 1) ^ 2) hTagInput
  have hTagGoodMass : 0 < (FinProb.pi Q).pr GoodTag := by
    simpa [GoodTag, badT] using hTagCP.1
  have hTagWeightZero (τ : Γ.Key → M.ι) (hbad : ¬ GoodTag τ) :
      (tagLaw Γ M Q D₀).w τ = 0 := by
    simp [tagLaw, condOr, FinProb.cond, GoodTag, hTagGoodMass, hbad]
  let τ₀ : Γ.Key → M.ι := Classical.choice
    (finprob_nonempty_q_s07_anchor (FinProb.pi Q))
  have hLocalT : ∀ τ₀, ∑ a : (∀ g : {g : Γ.Key // g ∈ UT}, M.ι),
      (FinProb.pi (fun g : {g : Γ.Key // g ∈ UT} => Q g.1)).w a * PhiT (glue UT τ₀ a) ≤ BT := by
    intro τout
    change (FinProb.pi (fun g : {g : Γ.Key // g ∈ UT} => Q g.1)).expect
      (fun a => PhiT (glue UT τout a)) ≤ BT
    calc
      _ = (FinProb.pi Q).expect PhiT :=
        pi_glue_expect_eq_q_s07_anchor Q UT PhiT τ₀ hdepPhiT τout
      _ = BT := hFullT
      _ ≤ BT := le_rfl
  have hFullA (τ : Γ.Key → M.ι) :
      (FinProb.pi (Pcell τ)).expect (PhiA τ) = BA τ := by
    have h := pi_expect_prod_disjoint_q_s07_anchor (Pcell τ) (FA τ) scopeA Finset.univ
      (by intro i hi; exact hdepFA τ i)
      (by intro i hi j hj hne; exact hscopeADisj i j hne)
    simpa [PhiA, BA] using h
  have hBA0 (τ : Γ.Key → M.ι) : 0 ≤ BA τ := by
    dsimp [BA]
    apply Finset.prod_nonneg
    intro i hi
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro W hW
    exact mul_nonneg ((FinProb.pi (Pcell τ)).nonneg W) (hFA0 τ i W)
  have hBAEq (τ : Γ.Key → M.ι) : BA τ = PhiT τ := by
    dsimp [BA, PhiT, FA, FT]
    apply Finset.prod_congr rfl
    intro i hi
    change (FinProb.pi (Pcell τ)).expect
        (fun W => (N : ℝ) * cellRow Γ M τ W (c i) y) =
      (N : ℝ) * rawAnchorRowMean_q_s07_anchor Γ M τ (c i) y
    calc
      (FinProb.pi (Pcell τ)).expect
          (fun W => (N : ℝ) * cellRow Γ M τ W (c i) y) =
        (N : ℝ) * (FinProb.pi (Pcell τ)).expect
          (fun W => cellRow Γ M τ W (c i) y) := FinProb.expect_smul _ _ _
      _ = (N : ℝ) * rawAnchorRowMean_q_s07_anchor Γ M τ (c i) y := by
        dsimp [rawAnchorRowMean_q_s07_anchor, rawAnchors, Pcell]
  have hLocalA : ∀ τ τ₀,
      ∑ a : (∀ a : {a : Γ.Cell // a ∈ UA}, Fin N),
        (FinProb.pi (fun a : {a : Γ.Cell // a ∈ UA} => (Pcell τ) a.1)).w a *
          PhiA τ (glue UA τ₀ a) ≤ BA τ := by
    intro τ τ₀
    change (FinProb.pi (fun a : {a : Γ.Cell // a ∈ UA} => (Pcell τ) a.1)).expect
      (fun a => PhiA τ (glue UA τ₀ a)) ≤ BA τ
    let W₀ : Γ.Cell → Fin N := Classical.choice
      (finprob_nonempty_q_s07_anchor (rawAnchors Γ M τ))
    calc
      _ = (FinProb.pi (Pcell τ)).expect (PhiA τ) :=
        pi_glue_expect_eq_q_s07_anchor (Pcell τ) UA (PhiA τ) W₀
          (hdepPhiA τ) τ₀
      _ = BA τ := hFullA τ
      _ ≤ BA τ := le_rfl
  have hAInput (τ : Γ.Key → M.ι) (hgood : ∀ g, ¬ TagBad Γ M D₀ τ g) :
      LLLInput (Pcell τ) (badA τ) ballA (xL D₀ n) ((2 * s + q + 1) ^ 4) := by
    simpa [AnchorLLL, Pcell, badA, ballA] using hAnchor τ hgood
  have hTagInput : LLLInput Q badT ballT (xL D₀ n) ((2 * s + 1) ^ 2) := by
    simpa [TagLLL, badT, ballT] using hTag
  have htouchABase :
      (Finset.univ.filter fun a : Γ.Cell => ¬ Disjoint (ballA a) UA).card ≤ m * cellTouch := by
    let touch : Finset Γ.Cell := Finset.univ.filter fun a => ¬ Disjoint (ballA a) UA
    have hsub : touch ⊆ Finset.univ.biUnion fun i : Fin m => Γ.cellBall (c i) 3 := by
      intro a ha
      have hnot := (Finset.mem_filter.mp ha).2
      rcases Finset.not_disjoint_iff.mp hnot with ⟨w, hwA, hwU⟩
      rcases Finset.mem_biUnion.mp hwU with ⟨i, hi, hwi⟩
      have hrow := fullNames_cellDist_le_one Γ (c i) w (List.mem_toFinset.mp hwi)
      have hball : Γ.cellDist a w ≤ 2 := (Finset.mem_filter.mp hwA).2
      have hsymm : Γ.cellDist w a = Γ.cellDist a w := by
        simp [GridGeom.cellDist, GridGeom.keyDist, GridGeom.auxDist,
          Nat.dist_comm, ne_comm]
      have htri := cellDist_triangle Γ (c i) w a
      have hcenter : Γ.cellDist (c i) a ≤ 3 := by omega
      exact Finset.mem_biUnion.mpr ⟨i, hi,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcenter⟩⟩
    calc
      (Finset.univ.filter fun a : Γ.Cell => ¬ Disjoint (ballA a) UA).card ≤
          (Finset.univ.biUnion fun i : Fin m => Γ.cellBall (c i) 3).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ i ∈ Finset.univ, (Γ.cellBall (c i) 3).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Finset.univ, cellTouch := by
        apply Finset.sum_le_sum
        intro i hi
        have hball : (Γ.cellBall (c i) 3).card ≤ cellTouch := by
          have h := hGeom.balls.cellBall_card (c i) 3
          dsimp [cellTouch, cellBase]
          exact_mod_cast h
        exact hball
      _ = m * cellTouch := by simp [cellTouch]
  have htouchTBase :
      (Finset.univ.filter fun g : Γ.Key => ¬ Disjoint (ballT g) UT).card ≤ m * keyTouch := by
    let touch : Finset Γ.Key := Finset.univ.filter fun g => ¬ Disjoint (ballT g) UT
    have hsub : touch ⊆ Finset.univ.biUnion fun i : Fin m => Γ.keyBall (c i).1 2 := by
      intro g hg
      have hnot := (Finset.mem_filter.mp hg).2
      rcases Finset.not_disjoint_iff.mp hnot with ⟨k, hkg, hkU⟩
      rcases Finset.mem_biUnion.mp hkU with ⟨i, hi, hki⟩
      have hgk : Γ.keyDist g k ≤ 1 := (Finset.mem_filter.mp hkg).2
      have hik : Γ.keyDist (c i).1 k ≤ 1 := (Finset.mem_filter.mp hki).2
      have hki' : Γ.keyDist k (c i).1 ≤ 1 := by
        simpa [GridGeom.keyDist, Nat.dist_comm] using hik
      have hgi : Γ.keyDist g (c i).1 ≤ 2 := by
        have htri := hkeyTriangle g (c i).1 k
        omega
      have hig : Γ.keyDist (c i).1 g ≤ 2 := by
        simpa [GridGeom.keyDist, Nat.dist_comm] using hgi
      exact Finset.mem_biUnion.mpr ⟨i, hi,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hig⟩⟩
    calc
      touch.card ≤ (Finset.univ.biUnion fun i : Fin m => Γ.keyBall (c i).1 2).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ i ∈ Finset.univ, (Γ.keyBall (c i).1 2).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Finset.univ, keyTouch := by
        apply Finset.sum_le_sum
        intro i hi
        have hball : (Γ.keyBall (c i).1 2).card ≤ keyTouch := by
          have h := hGeom.balls.keyBall_card (c i).1 2
          dsimp [keyTouch]
          exact_mod_cast h
        exact hball
      _ = m * keyTouch := by simp [keyTouch]
  have hTagCondEstimate : (tagLaw Γ M Q D₀).expect PhiT ≤
      (((1 - xL D₀ n) ^ touchT.card)⁻¹) * BT := by
    simpa [tagLaw, condOr, badT, ballT] using
      hTagCP.2 UT PhiT hPhiT0 BT hLocalT
  have htouchTCard4 : touchT.card ≤ m * cellBase ^ 4 := by
    calc
      touchT.card ≤ m * keyTouch := htouchTCard
      _ ≤ m * cellBase ^ 4 := Nat.mul_le_mul_left m hkeyTouchLE
  have htagFactor : ((1 - xL D₀ n) ^ touchT.card)⁻¹ ≤ (2 : ℝ) ^ m :=
    anchor_moment_factor_small_q_s07_anchor hx0 hx1 hxKey htouchTCard4
  have hTagEstimate : (tagLaw Γ M Q D₀).expect PhiT ≤ (2 : ℝ) ^ m * BT := by
    calc
      (tagLaw Γ M Q D₀).expect PhiT ≤
          (((1 - xL D₀ n) ^ touchT.card)⁻¹) * BT := hTagCondEstimate
      _ ≤ (2 : ℝ) ^ m * BT := mul_le_mul_of_nonneg_right htagFactor hBT0
  have hAnchorBound (τ : Γ.Key → M.ι) (hgood : ∀ g, ¬ TagBad Γ M D₀ τ g) :
      (anchorLaw Γ M τ).expect (PhiA τ) ≤ (2 : ℝ) ^ m * PhiT τ := by
    let LL := hAInput τ hgood
    let CP := hCPB (Pcell τ) (badA τ) ballA (xL D₀ n)
      ((2 * s + q + 1) ^ 4) LL
    have hest := CP.2 UA (PhiA τ) (hPhiA0 τ) (BA τ) (hLocalA τ)
    have hcount :
        (Finset.univ.filter fun a : Γ.Cell => ¬ Disjoint (ballA a) UA).card ≤ m * cellTouch :=
      htouchABase
    have hfactor := anchor_moment_factor_small_q_s07_anchor hx0 hx1 hcellCharge hcount
    have hcond : (anchorLaw Γ M τ).expect (PhiA τ) ≤
        (((1 - xL D₀ n) ^
          (Finset.univ.filter fun a : Γ.Cell => ¬ Disjoint (ballA a) UA).card)⁻¹) * BA τ := by
      simpa [anchorLaw, rawAnchors, Pcell, badA] using hest
    calc
      (anchorLaw Γ M τ).expect (PhiA τ) ≤
          (((1 - xL D₀ n) ^
            (Finset.univ.filter fun a : Γ.Cell => ¬ Disjoint (ballA a) UA).card)⁻¹) * BA τ := hcond
      _ ≤ (2 : ℝ) ^ m * BA τ := mul_le_mul_of_nonneg_right hfactor (hBA0 τ)
      _ = (2 : ℝ) ^ m * PhiT τ := by rw [hBAEq τ]
  let masked : (Γ.Key → M.ι) → ℝ := fun τ =>
    if GoodTag τ then (anchorLaw Γ M τ).expect (PhiA τ) else 0
  have hmaskEq : (tagLaw Γ M Q D₀).expect
      (fun τ => (anchorLaw Γ M τ).expect (PhiA τ)) =
        (tagLaw Γ M Q D₀).expect masked := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro τ hτ
    by_cases hg : GoodTag τ
    · simp [masked, hg, FinProb.expect]
    · simp [masked, hg, FinProb.expect, hTagWeightZero τ hg]
  have hmaskedBound (τ : Γ.Key → M.ι) :
      masked τ ≤ (2 : ℝ) ^ m * PhiT τ := by
    by_cases hg : GoodTag τ
    · simpa [masked, hg] using hAnchorBound τ hg
    · simpa [masked, hg] using
        (mul_nonneg (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) m) (hPhiT0 τ))
  have hTagFinal : (tagLaw Γ M Q D₀).expect
      (fun τ => (anchorLaw Γ M τ).expect (PhiA τ)) ≤
        (4 : ℝ) ^ m * ∏ i, (N : ℝ) * rawRowMean Γ M Q (c i) y := by
    calc
      (tagLaw Γ M Q D₀).expect
          (fun τ => (anchorLaw Γ M τ).expect (PhiA τ)) =
        (tagLaw Γ M Q D₀).expect masked := hmaskEq
      _ ≤ (tagLaw Γ M Q D₀).expect (fun τ => (2 : ℝ) ^ m * PhiT τ) :=
        FinProb.expect_mono _ hmaskedBound
      _ = (2 : ℝ) ^ m * (tagLaw Γ M Q D₀).expect PhiT := by
        rw [FinProb.expect_smul]
      _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ m * BT) :=
        mul_le_mul_of_nonneg_left hTagEstimate (pow_nonneg (by norm_num) _)
      _ = (4 : ℝ) ^ m * BT := by
        have hpow : (2 : ℝ) ^ m * (2 : ℝ) ^ m = (4 : ℝ) ^ m := by
          rw [← mul_pow]
          norm_num
        rw [← hpow]
        ring
      _ = (4 : ℝ) ^ m * ∏ i, (N : ℝ) * rawRowMean Γ M Q (c i) y := by rw [hBTrow]
  have hBind := FinProb.bind_expect (tagLaw Γ M Q D₀) (anchorLaw Γ M)
    (fun τ W => PhiA τ W)
  calc
    (FinProb.bind (tagLaw Γ M Q D₀) (anchorLaw Γ M)).expect
        (fun ω => ∏ i, (N : ℝ) * cellRow Γ M ω.1 ω.2 (Γ.key (u i).1) y) =
      (tagLaw Γ M Q D₀).expect
        (fun τ => (anchorLaw Γ M τ).expect (PhiA τ)) := by
          simpa [PhiA, FA, FinProb.expect] using hBind
    _ ≤ (4 : ℝ) ^ m * ∏ i, (N : ℝ) * rawRowMean Γ M Q (Γ.key (u i).1) y := by
      simpa [c] using hTagFinal

end HypercubeRamsey.S07
