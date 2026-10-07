import HypercubeRamsey.S05.Parents

/-!
# D5.3, D5.5, L5.1b, L5.1e0: chunks, keys, even types and states

The cube coordinates are split into 300 coarse chunks, `m` odd fine chunks and residual coordinates
(05:81–109).  Counts, bins, majority signs, the flippable set `F` and the severity `j` are *definitions* from
the layout; `ChunkGeometry5` records the layout and the three probability estimates of L5.1b.  Hidden-column
keys and even types (05:111–149) are definitions from the geometry.  `CubeStates5` is the state quotient with
its one-hot embedding (05:291–329); every role in a state has the same key, sign, severity, parity, type and
residual bits.
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey

/-- Even cube roles (embedded on the first side `X`). -/
abbrev EvenRole5 (n : ℕ) := {v : CubeVertex n // IsEvenRole v}

/-- Odd cube roles (embedded on the second side `Y`). -/
abbrev OddRole5 (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}

/-- Number of coarse chunks, `d_c = 300` (05:81). -/
def coarseChunkCount5 : ℕ := 300

/-- A vector of coarse bins, one per coarse chunk. -/
abbrev BinVector5 (n : ℕ) := Fin coarseChunkCount5 → Fin (n + 1)

/-- A coarse key `i(P)`: the bin vector and the boundary flag (`true` = boundary) (05:84–90). -/
abbrev CoarseKey5 (n : ℕ) := BinVector5 n × Bool

/-- Flip one coordinate of a cube vertex. -/
def flipVertex5 {n : ℕ} (x : CubeVertex n) (a : Fin n) : CubeVertex n :=
  Function.update x a (!x a)

/-- Grid neighbours of bin vectors: exactly one coordinate differs, by one. -/
def binAdjacent5 {n : ℕ} (w w' : BinVector5 n) : Prop :=
  (Finset.univ.filter (fun i => w i ≠ w' i)).card = 1 ∧ ∀ i, Nat.dist (w i).val (w' i).val ≤ 1

/-- D5.3 layout (05:81–109): disjoint coarse chunks of length `⌊n^{1/5}⌋`, `m` fine chunks of a common odd
length `≍ n^{.3}`, residual coordinates, and consecutive count bins of binomial probability `≤ 2n^{-.04}`.
The fields `sign_uniform`, `severity_tail` and `boundary_fraction` are the probability estimates of L5.1b. -/
structure ChunkGeometry5 (n m : ℕ) where
  fineLength : ℕ
  coarseChunks : Fin coarseChunkCount5 → Finset (Fin n)
  fineChunks : Fin m → Finset (Fin n)
  residual : Finset (Fin n)
  chunks_disjoint : (∀ i j, i ≠ j → Disjoint (coarseChunks i) (coarseChunks j)) ∧
    (∀ i j, Disjoint (coarseChunks i) (fineChunks j)) ∧
    (∀ i j, i ≠ j → Disjoint (fineChunks i) (fineChunks j)) ∧
    (∀ i, Disjoint (coarseChunks i) residual) ∧
    (∀ i, Disjoint (fineChunks i) residual)
  chunks_cover : (Finset.univ.biUnion coarseChunks) ∪ (Finset.univ.biUnion fineChunks) ∪ residual =
    Finset.univ
  occupied_sublinear :
    (((Finset.univ.biUnion coarseChunks) ∪ (Finset.univ.biUnion fineChunks)).card : ℝ) ≤
      (n : ℝ) ^ (1 / 2 : ℝ)
  coarse_length : ∀ i, (coarseChunks i).card = ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊
  bin : Fin coarseChunkCount5 → ℕ → Fin (n + 1)
  bin_monotone : ∀ i a b, a ≤ b → (bin i a).val ≤ (bin i b).val
  bin_consecutive : ∀ i a, (bin i (a + 1)).val ≤ (bin i a).val + 1
  bin_probability_bound : ∀ i j,
    (∑ q ∈ Finset.range ((coarseChunks i).card + 1),
      if bin i q = j then (Nat.choose (coarseChunks i).card q : ℝ) else 0) ≤
        2 * (n : ℝ) ^ (-(4 / 100 : ℝ)) * (2 : ℝ) ^ (coarseChunks i).card
  fine_length_odd : Odd fineLength
  fine_length_lower : (n : ℝ) ^ (3 / 10 : ℝ) ≤ fineLength
  fine_length_upper : (fineLength : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 10 : ℝ)
  fine_chunk_length : ∀ i, (fineChunks i).card = fineLength
  residual_nonempty : residual.Nonempty

namespace ChunkGeometry5

variable {n m : ℕ} (g : ChunkGeometry5 n m)

/-- Count of ones in a coarse chunk. -/
noncomputable def coarseCount (x : CubeVertex n) (i : Fin coarseChunkCount5) : ℕ :=
  ((g.coarseChunks i).filter fun a => x a = true).card

/-- Bin vector `w(P)`. -/
noncomputable def coarseBin (x : CubeVertex n) : BinVector5 n := fun i => g.bin i (g.coarseCount x i)

/-- Boundary flag: some single coarse bit flip changes a bin. -/
def boundary (x : CubeVertex n) : Prop :=
  ∃ i, ∃ a ∈ g.coarseChunks i, g.coarseBin (flipVertex5 x a) ≠ g.coarseBin x

/-- Coarse key `i(P)`. -/
noncomputable def key (x : CubeVertex n) : CoarseKey5 n := (g.coarseBin x, decide (g.boundary x))

/-- Count of ones in a fine chunk. -/
noncomputable def fineCount (x : CubeVertex n) (i : Fin m) : ℕ :=
  ((g.fineChunks i).filter fun a => x a = true).card

/-- Majority signs `t ∈ Q_m`. -/
noncomputable def sign (x : CubeVertex n) : CubeVertex m := fun i => decide (g.fineLength < 2 * g.fineCount x i)

/-- The flippable chunks `F`: count at distance `1/2` from mid-weight. -/
noncomputable def flippable (x : CubeVertex n) : Finset (Fin m) :=
  Finset.univ.filter fun i => Nat.dist (2 * g.fineCount x i) g.fineLength = 1

/-- Severity `j`: the number of fine chunks within `R_f = 5.5` of mid-weight. -/
noncomputable def severity (x : CubeVertex n) : ℕ :=
  (Finset.univ.filter fun i : Fin m => Nat.dist (2 * g.fineCount x i) g.fineLength ≤ 11).card

/-- Coarse coordinates. -/
noncomputable def coarseCoords : Finset (Fin n) := Finset.univ.biUnion g.coarseChunks

/-- Residual Hamming distance between two roles. -/
noncomputable def residualDist (x y : CubeVertex n) : ℕ :=
  (g.residual.filter fun a => x a ≠ y a).card

end ChunkGeometry5

/-- The candidate bin list `C_i` of a coarse key: `{w}` at interior keys, `w` and its grid neighbours at
boundary keys (05:88–91). -/
noncomputable def binList5 {n : ℕ} (i : CoarseKey5 n) : Finset (BinVector5 n) :=
  if i.2 then Finset.univ.filter (fun w => w = i.1 ∨ binAdjacent5 i.1 w) else {i.1}

/-- L5.1b (05:81–109): the layout exists for large `n`, with the three probability estimates: signs uniform on
each parity class, `Pr(j ≥ h) ≤ n^{-.13h}` for `1 ≤ h ≤ m`, and `Pr(boundary) ≤ n^{-.05}`. -/
structure ChunkEstimates5 {n m : ℕ} (g : ChunkGeometry5 n m) : Prop where
  sign_uniform : ∀ (b : Bool) (t : CubeVertex m),
    ((Finset.univ.filter fun x : CubeVertex n => decide (IsEvenRole x) = b ∧ g.sign x = t).card : ℝ) *
        (2 : ℝ) ^ m =
      ((Finset.univ.filter fun x : CubeVertex n => decide (IsEvenRole x) = b).card : ℝ)
  severity_tail : ∀ h : ℕ, 1 ≤ h → h ≤ m →
    ((Finset.univ.filter fun x : CubeVertex n => h ≤ g.severity x).card : ℝ) / (2 : ℝ) ^ n ≤
      (n : ℝ) ^ (-(13 / 100 : ℝ) * h)
  boundary_fraction :
    ((Finset.univ.filter fun x : CubeVertex n => g.boundary x).card : ℝ) / (2 : ℝ) ^ n ≤
      (n : ℝ) ^ (-(5 / 100 : ℝ))

/-- L5.1b (05:81–109): for every fixed `0 < α < 1/50`, the D5.3 layout with `m = ⌈n^α⌉` fine chunks exists
for all large `n` and has the L5.1b estimates. -/
theorem L5_1b (α : ℝ) (hα : 0 < α) (hα' : α < 1 / 50) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ g : ChunkGeometry5 n ⌈(n : ℝ) ^ α⌉₊, ChunkEstimates5 g := by
  sorry

/-! ### Keys and even types (05:111–149) -/

/-- Hidden-column keys: low keys `(i, t, j)` with `j ≤ J`, and high keys `(i, *)`. -/
abbrev HiddenKey5 (n m J : ℕ) := (CoarseKey5 n × CubeVertex m × Fin (J + 1)) ⊕ CoarseKey5 n

/-- Coarse key of a hidden key. -/
def HiddenKey5.coarse {n m J : ℕ} : HiddenKey5 n m J → CoarseKey5 n
  | .inl k => k.1
  | .inr i => i

/-- Severity level read by a key's posterior: `j` at low keys, `J` at high keys (05:127–130). -/
def HiddenKey5.level {n m J : ℕ} : HiddenKey5 n m J → ℕ
  | .inl k => k.2.2.val
  | .inr _ => J

/-- An even type: coarse key, the padded key list `S`, and the severity (`some j`, low) or `none` (high). -/
abbrev EvenType5 (n m J : ℕ) := CoarseKey5 n × Finset (HiddenKey5 n m J) × Option (Fin (J + 1))

/-- The low key at coarse key `i`, signs `t` and severity `j'`, replaced by the high key above `J`. -/
noncomputable def keyAt5 {n m : ℕ} (J : ℕ) (i : CoarseKey5 n) (t : CubeVertex m) (j' : ℕ) :
    HiddenKey5 n m J :=
  if h : j' ≤ J then .inl (i, t, ⟨j', Nat.lt_succ_of_le h⟩) else .inr i

namespace ChunkGeometry5

variable {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)

/-- Low/high split at `J`. -/
def low (x : CubeVertex n) : Prop := g.severity x ≤ J

/-- The key of a role (05:118–122). -/
noncomputable def roleKey (x : CubeVertex n) : HiddenKey5 n m J :=
  if h : g.severity x ≤ J then .inl (g.key x, g.sign x, ⟨g.severity x, Nat.lt_succ_of_le h⟩)
  else .inr (g.key x)

/-- Coarse keys of `x` and of its single coarse flips. -/
noncomputable def coarseRange (x : CubeVertex n) : Finset (CoarseKey5 n) :=
  insert (g.key x) (g.coarseCoords.image fun a => g.key (flipVertex5 x a))


/-- The padded key list `S(v)` of an even role (05:133–144). -/
noncomputable def typeKeys (x : CubeVertex n) : Finset (HiddenKey5 n m J) :=
  if g.severity x ≤ J then
    (g.coarseRange x).image (fun i => keyAt5 J i (g.sign x) (g.severity x)) ∪
      (g.flippable x).image (fun h => keyAt5 J (g.key x) (Function.update (g.sign x) h
        (!g.sign x h)) (g.severity x)) ∪
      Finset.image (fun j' => keyAt5 J (g.key x) (g.sign x) j')
        (({g.severity x + 1} : Finset ℕ) ∪ (if 0 < g.severity x then {g.severity x - 1} else ∅))
  else (g.coarseRange x).image (fun i => (.inr i : HiddenKey5 n m J))

/-- The even type `K(v)` (05:138–141). -/
noncomputable def evenType (x : CubeVertex n) : EvenType5 n m J :=
  (g.key x, g.typeKeys J x,
    if h : g.severity x ≤ J then some ⟨g.severity x, Nat.lt_succ_of_le h⟩ else none)

/-- The optional low key `(i(P), t, J)` of a high even role with `j = J + 1` (05:141–144). -/
noncomputable def optionalKey (x : CubeVertex n) : Option (HiddenKey5 n m J) :=
  if g.severity x = J + 1 then some (.inl (g.key x, g.sign x, ⟨J, Nat.lt_succ_self J⟩)) else none

end ChunkGeometry5

/-- L5.1e, coverage part (05:144–147): the padded list and the optional key cover the keys of all actual odd
neighbours of an even role, and every key in a type list has the role's bin in its candidate list. -/
theorem L5_1e_cover {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ) :
    (∀ x y : CubeVertex n, (cube n).Adj x y →
      g.roleKey J y ∈ g.typeKeys J x ∨ g.optionalKey J x = some (g.roleKey J y)) ∧
    (∀ x : CubeVertex n, ∀ ℓ ∈ g.typeKeys J x, (g.key x).1 ∈ binList5 ℓ.coarse) := by
  classical
  constructor
  · intro x y hadj
    have hadj_card : (Finset.univ.filter (fun a : Fin n => x a ≠ y a)).card = 1 := by
      change _root_.hammingDist x y = 1 at hadj
      simpa [_root_.hammingDist] using hadj
    obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hadj_card
    have hneq : x a ≠ y a := by
      have ha : a ∈ Finset.univ.filter (fun i : Fin n => x i ≠ y i) := by
        rw [ha_eq]
        simp
      exact (Finset.mem_filter.mp ha).2
    have hbits : ∀ b, b ≠ a → x b = y b := by
      intro b hba
      by_contra hne
      have hb : b ∈ Finset.univ.filter (fun i : Fin n => x i ≠ y i) := by
        simp [hne]
      rw [ha_eq] at hb
      exact hba (Finset.mem_singleton.mp hb)
    have hyflip : y = flipVertex5 x a := by
      funext b
      by_cases hba : b = a
      · subst b
        cases hx : x a <;> cases hy : y a <;> simp_all [flipVertex5]
      · simp only [flipVertex5, Function.update_of_ne hba]
        exact (hbits b hba).symm
    have hcategory (b : Fin n) :
        (∃ i, b ∈ g.coarseChunks i) ∨ (∃ i, b ∈ g.fineChunks i) ∨ b ∈ g.residual := by
      have hb : b ∈ Finset.univ := Finset.mem_univ _
      rw [← g.chunks_cover] at hb
      simpa [Finset.mem_biUnion] using hb
    have hfilter_eq {C : Finset (Fin n)} {u v : CubeVertex n}
        (h : ∀ b ∈ C, u b = v b) :
        C.filter (fun b => u b = true) = C.filter (fun b => v b = true) := by
      ext b
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hb, hu⟩
        exact ⟨hb, (h b hb).symm ▸ hu⟩
      · rintro ⟨hb, hv⟩
        exact ⟨hb, (h b hb) ▸ hv⟩
    have hchunk_mem_coarseCoords (i : Fin coarseChunkCount5) (b : Fin n)
        (hb : b ∈ g.coarseChunks i) : b ∈ g.coarseCoords := by
      change b ∈ Finset.univ.biUnion g.coarseChunks
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩
    have hcoarseBin_eq_of_agree {u v : CubeVertex n}
        (h : ∀ b ∈ g.coarseCoords, u b = v b) :
        g.coarseBin u = g.coarseBin v := by
      funext i
      simp only [ChunkGeometry5.coarseBin]
      have hc : g.coarseCount u i = g.coarseCount v i := by
        unfold ChunkGeometry5.coarseCount
        congr 1
        apply hfilter_eq
        intro b hb
        exact h b (hchunk_mem_coarseCoords i b hb)
      rw [hc]
    have hkey_eq_of_agree {u v : CubeVertex n}
        (h : ∀ b ∈ g.coarseCoords, u b = v b) : g.key u = g.key v := by
      have hbin := hcoarseBin_eq_of_agree h
      have hboundary : g.boundary u ↔ g.boundary v := by
        unfold ChunkGeometry5.boundary
        constructor
        · rintro ⟨i, b, hb, hne'⟩
          have hbcoarse : b ∈ g.coarseCoords := by
            exact hchunk_mem_coarseCoords i b hb
          have hflipbits : ∀ c ∈ g.coarseCoords,
              flipVertex5 u b c = flipVertex5 v b c := by
            intro c hc
            by_cases hcb : c = b
            · subst c
              simp [flipVertex5, h b hbcoarse]
            · simp [flipVertex5, hcb, h c hc]
          have hflipbin := hcoarseBin_eq_of_agree hflipbits
          refine ⟨i, b, hb, ?_⟩
          intro heq
          apply hne'
          calc
            g.coarseBin (flipVertex5 u b) = g.coarseBin (flipVertex5 v b) := hflipbin
            _ = g.coarseBin v := heq
            _ = g.coarseBin u := hbin.symm
        · rintro ⟨i, b, hb, hne'⟩
          have hbcoarse : b ∈ g.coarseCoords := by
            exact hchunk_mem_coarseCoords i b hb
          have hflipbits : ∀ c ∈ g.coarseCoords,
              flipVertex5 u b c = flipVertex5 v b c := by
            intro c hc
            by_cases hcb : c = b
            · subst c
              simp [flipVertex5, h b hbcoarse]
            · simp [flipVertex5, hcb, h c hc]
          have hflipbin := hcoarseBin_eq_of_agree hflipbits
          refine ⟨i, b, hb, ?_⟩
          intro heq
          apply hne'
          calc
            g.coarseBin (flipVertex5 v b) = g.coarseBin (flipVertex5 u b) := hflipbin.symm
            _ = g.coarseBin u := heq
            _ = g.coarseBin v := hbin
      change (g.coarseBin u, decide (g.boundary u)) =
        (g.coarseBin v, decide (g.boundary v))
      have hprop : g.boundary u = g.boundary v := propext hboundary
      have hdec : decide (g.boundary u) = decide (g.boundary v) := by rw [hprop]
      exact Prod.ext hbin hdec
    have hrole_eq_keyAt (z : CubeVertex n) :
        g.roleKey J z = keyAt5 J (g.key z) (g.sign z) (g.severity z) := by
      by_cases hz : g.severity z ≤ J <;>
        simp [ChunkGeometry5.roleKey, keyAt5, hz]
    have hcount_eq_of_notMem (C : Finset (Fin n)) (hnot : a ∉ C) :
        ((C.filter fun b => x b = true).card =
          (C.filter fun b => y b = true).card) := by
      have hset : C.filter (fun b => x b = true) = C.filter (fun b => y b = true) :=
        hfilter_eq (by
          intro b hb
          have hba : b ≠ a := by
            intro h
            subst b
            exact hnot hb
          exact hbits b hba)
      exact congrArg Finset.card hset
    have hcount_step (C : Finset (Fin n)) (haC : a ∈ C) :
        (C.filter (fun b => x b = true)).card + 1 =
            (C.filter (fun b => y b = true)).card ∨
        (C.filter (fun b => y b = true)).card + 1 =
            (C.filter (fun b => x b = true)).card := by
      have hcases : (x a = false ∧ y a = true) ∨ (x a = true ∧ y a = false) := by
        cases hx : x a <;> cases hy : y a <;> simp_all
      rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hset : C.filter (fun b => y b = true) =
            insert a (C.filter (fun b => x b = true)) := by
          ext b
          by_cases hba : b = a
          · subst b
            simp [haC, hx, hy]
          · simp only [Finset.mem_filter, Finset.mem_insert]
            simp [hba, hbits b hba]
        have hnot : a ∉ C.filter (fun b => x b = true) := by
          simp [Finset.mem_filter, haC, hx]
        left
        have hc := congrArg Finset.card hset
        rw [Finset.card_insert_of_notMem hnot] at hc
        omega
      · have hset : C.filter (fun b => x b = true) =
            insert a (C.filter (fun b => y b = true)) := by
          ext b
          by_cases hba : b = a
          · subst b
            simp [haC, hx, hy]
          · simp only [Finset.mem_filter, Finset.mem_insert]
            simp [hba, hbits b hba]
        have hnot : a ∉ C.filter (fun b => y b = true) := by
          simp [Finset.mem_filter, haC, hy]
        right
        have hc := congrArg Finset.card hset
        rw [Finset.card_insert_of_notMem hnot] at hc
        omega
    have hstep_center (c d L : ℕ) (hL : Odd L)
        (hstep : c + 1 = d ∨ d + 1 = c) :
        (L < 2 * c ↔ L < 2 * d) ∨
          ((Nat.dist (2 * c) L = 1 ∧ Nat.dist (2 * d) L = 1) ∧
            ((¬ L < 2 * c ∧ L < 2 * d) ∨ (L < 2 * c ∧ ¬ L < 2 * d))) := by
      obtain ⟨k, hk⟩ := hL
      rcases hstep with hstep | hstep
      · by_cases hc : L < 2 * c <;> by_cases hd : L < 2 * d
        · exact Or.inl ⟨fun _ => hd, fun _ => hc⟩
        · exfalso
          omega
        · right
          have hdist : Nat.dist (2 * c) L = 1 ∧ Nat.dist (2 * d) L = 1 := by
            constructor <;> simp [Nat.dist, hk] <;> omega
          exact ⟨hdist, Or.inl ⟨hc, hd⟩⟩
        · exact Or.inl ⟨fun h => (hc h).elim, fun h => (hd h).elim⟩
      · by_cases hd : L < 2 * d <;> by_cases hc : L < 2 * c
        · exact Or.inl ⟨fun _ => hd, fun _ => hc⟩
        · exfalso
          omega
        · right
          have hdist : Nat.dist (2 * c) L = 1 ∧ Nat.dist (2 * d) L = 1 := by
            constructor <;> simp [Nat.dist, hk] <;> omega
          exact ⟨hdist, Or.inr ⟨hc, hd⟩⟩
        · exact Or.inl ⟨fun h => (hc h).elim, fun h => (hd h).elim⟩
    have hseverity_relation (i₀ : Fin m)
        (hcounts : ∀ i, i ≠ i₀ → g.fineCount x i = g.fineCount y i) :
        g.severity x = g.severity y ∨
          g.severity y = g.severity x + 1 ∨
          g.severity x = g.severity y + 1 := by
      let FX := Finset.univ.filter (fun i : Fin m =>
        Nat.dist (2 * g.fineCount x i) g.fineLength ≤ 11)
      let FY := Finset.univ.filter (fun i : Fin m =>
        Nat.dist (2 * g.fineCount y i) g.fineLength ≤ 11)
      have hrest : FX.erase i₀ = FY.erase i₀ := by
        ext i
        by_cases hii : i = i₀
        · subst i
          simp
        · simp [FX, FY, hii, hcounts i hii]
      have hrestcard : (FX.erase i₀).card = (FY.erase i₀).card := congrArg Finset.card hrest
      have hcardX : FX.card = (FX.erase i₀).card + if i₀ ∈ FX then 1 else 0 := by
        by_cases hmem : i₀ ∈ FX
        · simpa [hmem] using (Finset.card_erase_add_one hmem).symm
        · simp [hmem, Finset.erase_eq_of_notMem hmem]
      have hcardY : FY.card = (FY.erase i₀).card + if i₀ ∈ FY then 1 else 0 := by
        by_cases hmem : i₀ ∈ FY
        · simpa [hmem] using (Finset.card_erase_add_one hmem).symm
        · simp [hmem, Finset.erase_eq_of_notMem hmem]
      have hseverityX : g.severity x = FX.card := by rfl
      have hseverityY : g.severity y = FY.card := by rfl
      rw [hseverityX, hseverityY, hcardX, hcardY, hrestcard]
      by_cases hx : i₀ ∈ FX <;> by_cases hy : i₀ ∈ FY <;> simp [hx, hy] <;> omega
    have hseverity_eq_of_center (i₀ : Fin m)
        (hcenter : Nat.dist (2 * g.fineCount x i₀) g.fineLength = 1 ∧
          Nat.dist (2 * g.fineCount y i₀) g.fineLength = 1)
        (hcounts : ∀ i, i ≠ i₀ → g.fineCount x i = g.fineCount y i) :
        g.severity x = g.severity y := by
      unfold ChunkGeometry5.severity
      congr 1
      ext i
      by_cases hii : i = i₀
      · subst i
        simp [hcenter]
      · simp [hcounts i hii]
    have hsign_ne_of_center (i₀ : Fin m)
        (horient : ((¬ g.fineLength < 2 * g.fineCount x i₀ ∧
          g.fineLength < 2 * g.fineCount y i₀) ∨
          (g.fineLength < 2 * g.fineCount x i₀ ∧
            ¬ g.fineLength < 2 * g.fineCount y i₀))) :
        g.sign x i₀ ≠ g.sign y i₀ := by
      intro heq
      change decide (g.fineLength < 2 * g.fineCount x i₀) =
        decide (g.fineLength < 2 * g.fineCount y i₀) at heq
      rcases horient with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> simp [hx, hy] at heq
    have hrole_mem_of_coarseRange (z : CubeVertex n)
        (hkeyRange : g.key z ∈ g.coarseRange x)
        (hsign : g.sign z = g.sign x) (hsev : g.severity z = g.severity x) :
        g.roleKey J z ∈ g.typeKeys J x := by
      rw [hrole_eq_keyAt z, hsign, hsev]
      by_cases hlow : g.severity x ≤ J
      · simp [ChunkGeometry5.typeKeys, hlow, keyAt5, hkeyRange]
      · simp [ChunkGeometry5.typeKeys, hlow, keyAt5, hkeyRange]
    have hrole_mem_of_severity (hlow : g.severity x ≤ J)
        (hkey : g.key x = g.key y) (hsign : g.sign x = g.sign y)
        (hsev : g.severity y = g.severity x + 1 ∨
          g.severity x = g.severity y + 1) :
        g.roleKey J y ∈ g.typeKeys J x := by
      rw [hrole_eq_keyAt y, hkey.symm, hsign.symm]
      have hjmem : g.severity y ∈
          ({g.severity x + 1} : Finset ℕ) ∪
            (if 0 < g.severity x then {g.severity x - 1} else ∅) := by
        rcases hsev with h | h
        · simp [h]
        · have hpos : 0 < g.severity x := by omega
          simp [h, hpos]
      unfold ChunkGeometry5.typeKeys
      rw [if_pos hlow]
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨g.severity y, hjmem, rfl⟩
    have hrole_mem_high (hkeyRange : g.key y ∈ g.coarseRange x)
        (hhighX : ¬ g.severity x ≤ J) (hhighY : ¬ g.severity y ≤ J) :
        g.roleKey J y ∈ g.typeKeys J x := by
      simp only [ChunkGeometry5.roleKey, dif_neg hhighY, ChunkGeometry5.typeKeys,
        if_neg hhighX, Finset.mem_image]
      exact ⟨g.key y, hkeyRange, rfl⟩
    have hrole_eq_optional (hkey : g.key x = g.key y)
        (hsign : g.sign x = g.sign y) (hxsev : g.severity x = J + 1)
        (hysev : g.severity y = J) :
        g.optionalKey J x = some (g.roleKey J y) := by
      simp [ChunkGeometry5.optionalKey, ChunkGeometry5.roleKey, hkey, hsign, hxsev, hysev]
    rcases hcategory a with hcoarse | hrest
    · obtain ⟨ic, haic⟩ := hcoarse
      rcases g.chunks_disjoint with ⟨_, hcf, _, _, _⟩
      have hcounts : ∀ i, g.fineCount x i = g.fineCount y i := by
        intro i
        have hnot : a ∉ g.fineChunks i := by
          intro hi
          exact (Finset.disjoint_left.mp (hcf ic i) haic hi).elim
        unfold ChunkGeometry5.fineCount
        exact hcount_eq_of_notMem (g.fineChunks i) hnot
      have hsign : g.sign y = g.sign x := by
        funext i
        simp [ChunkGeometry5.sign, hcounts i]
      have hsev : g.severity y = g.severity x := by
        simp [ChunkGeometry5.severity, hcounts]
      have hkeyRange : g.key y ∈ g.coarseRange x := by
        rw [hyflip]
        simp only [ChunkGeometry5.coarseRange, Finset.mem_insert]
        right
        exact Finset.mem_image.mpr
          ⟨a, hchunk_mem_coarseCoords ic a haic, rfl⟩
      exact Or.inl (hrole_mem_of_coarseRange y hkeyRange hsign hsev)
    · rcases hrest with hfine | haResidual
      · obtain ⟨i₀, hai₀⟩ := hfine
        rcases g.chunks_disjoint with ⟨_, hcf, hff, _, _⟩
        have haNotCoarse : a ∉ g.coarseCoords := by
          intro haC
          change a ∈ Finset.univ.biUnion g.coarseChunks at haC
          obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp haC
          exact (Finset.disjoint_left.mp (hcf i i₀) hai hai₀).elim
        have hagree : ∀ b ∈ g.coarseCoords, x b = y b := by
          intro b hb
          by_cases hba : b = a
          · subst b
            exact (haNotCoarse hb).elim
          · exact hbits b hba
        have hkey : g.key x = g.key y := hkey_eq_of_agree hagree
        have hkeyRange : g.key y ∈ g.coarseRange x := by
          rw [← hkey]
          simp [ChunkGeometry5.coarseRange]
        have hcounts : ∀ i, i ≠ i₀ → g.fineCount x i = g.fineCount y i := by
          intro i hii
          have hnot : a ∉ g.fineChunks i := by
            intro hai
            exact (Finset.disjoint_left.mp (hff i₀ i hii.symm) hai₀ hai).elim
          unfold ChunkGeometry5.fineCount
          exact hcount_eq_of_notMem (g.fineChunks i) hnot
        have hstep : g.fineCount x i₀ + 1 = g.fineCount y i₀ ∨
            g.fineCount y i₀ + 1 = g.fineCount x i₀ := by
          simpa [ChunkGeometry5.fineCount] using hcount_step (g.fineChunks i₀) hai₀
        have hcenterOrSame := hstep_center (g.fineCount x i₀) (g.fineCount y i₀)
          g.fineLength g.fine_length_odd hstep
        have hsignRel : g.sign x = g.sign y ∨
            (Nat.dist (2 * g.fineCount x i₀) g.fineLength = 1 ∧
              Nat.dist (2 * g.fineCount y i₀) g.fineLength = 1 ∧
              ((¬ g.fineLength < 2 * g.fineCount x i₀ ∧
                  g.fineLength < 2 * g.fineCount y i₀) ∨
                (g.fineLength < 2 * g.fineCount x i₀ ∧
                  ¬ g.fineLength < 2 * g.fineCount y i₀))) := by
          rcases hcenterOrSame with hiff | ⟨hcenter, horient⟩
          · left
            have hdec : decide (g.fineLength < 2 * g.fineCount x i₀) =
                decide (g.fineLength < 2 * g.fineCount y i₀) := by
              by_cases hx : g.fineLength < 2 * g.fineCount x i₀
              · have hy : g.fineLength < 2 * g.fineCount y i₀ := hiff.mp hx
                simp [hx, hy]
              · have hy : ¬ g.fineLength < 2 * g.fineCount y i₀ := by
                  intro hy
                  exact hx (hiff.mpr hy)
                simp [hx, hy]
            have hsignAt : g.sign x i₀ = g.sign y i₀ := by
              change decide (g.fineLength < 2 * g.fineCount x i₀) =
                decide (g.fineLength < 2 * g.fineCount y i₀)
              exact hdec
            funext i
            by_cases hii : i = i₀
            · subst i
              exact hsignAt
            · simp [ChunkGeometry5.sign, hcounts i hii]
          · exact Or.inr ⟨hcenter.1, hcenter.2, horient⟩
        have hsevRel := hseverity_relation i₀ hcounts
        by_cases hlowX : g.severity x ≤ J
        · rcases hsignRel with hsign | ⟨hcenterX, hcenterY, horient⟩
          · rcases hsevRel with hsev | hsevUp | hsevDown
            · exact Or.inl (hrole_mem_of_coarseRange y hkeyRange hsign.symm hsev.symm)
            · exact Or.inl (hrole_mem_of_severity hlowX hkey hsign (Or.inl hsevUp))
            · exact Or.inl (hrole_mem_of_severity hlowX hkey hsign (Or.inr hsevDown))
          · have hcenter :
                Nat.dist (2 * g.fineCount x i₀) g.fineLength = 1 ∧
                  Nat.dist (2 * g.fineCount y i₀) g.fineLength = 1 :=
              ⟨hcenterX, hcenterY⟩
            have hsev : g.severity x = g.severity y :=
              hseverity_eq_of_center i₀ hcenter hcounts
            have hflip : i₀ ∈ g.flippable x := by
              simp [ChunkGeometry5.flippable, hcenterX]
            have hsignNe : g.sign x i₀ ≠ g.sign y i₀ := by
              exact hsign_ne_of_center i₀ horient
            have hsignUpdate : g.sign y =
                Function.update (g.sign x) i₀ (!g.sign x i₀) := by
              funext i
              by_cases hii : i = i₀
              · subst i
                cases hx : g.sign x i₀ <;> cases hy : g.sign y i₀ <;>
                  simp_all [hsignNe, Function.update]
              · have hc := hcounts i hii
                simp [ChunkGeometry5.sign, hc, Function.update_of_ne hii]
            have hmem : g.roleKey J y ∈ g.typeKeys J x := by
              rw [hrole_eq_keyAt y, hkey.symm, hsignUpdate, hsev.symm]
              unfold ChunkGeometry5.typeKeys
              rw [if_pos hlowX]
              apply Finset.mem_union.mpr
              left
              apply Finset.mem_union.mpr
              right
              apply Finset.mem_image.mpr
              exact ⟨i₀, hflip, rfl⟩
            exact Or.inl hmem
        · by_cases hlowY : g.severity y ≤ J
          · rcases hsevRel with hsev | hsevUp | hsevDown
            · omega
            · omega
            · have hxsev : g.severity x = J + 1 := by omega
              have hysev : g.severity y = J := by omega
              have hsign : g.sign x = g.sign y := by
                rcases hsignRel with hsign | ⟨hcenterX, hcenterY, _⟩
                · exact hsign
                · have hsevEq := hseverity_eq_of_center i₀ ⟨hcenterX, hcenterY⟩ hcounts
                  omega
              exact Or.inr (hrole_eq_optional hkey hsign hxsev hysev)
          · exact Or.inl (hrole_mem_high hkeyRange hlowX hlowY)
      · rcases g.chunks_disjoint with ⟨_, _, _, hcr, hfr⟩
        have haNotCoarse : a ∉ g.coarseCoords := by
          intro haC
          change a ∈ Finset.univ.biUnion g.coarseChunks at haC
          obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp haC
          exact (Finset.disjoint_left.mp (hcr i) hai haResidual).elim
        have hagree : ∀ b ∈ g.coarseCoords, x b = y b := by
          intro b hb
          by_cases hba : b = a
          · subst b
            exact (haNotCoarse hb).elim
          · exact hbits b hba
        have hkey : g.key x = g.key y := hkey_eq_of_agree hagree
        have hkeyRange : g.key y ∈ g.coarseRange x := by
          rw [← hkey]
          simp [ChunkGeometry5.coarseRange]
        have hcounts : ∀ i, g.fineCount x i = g.fineCount y i := by
          intro i
          have hnot : a ∉ g.fineChunks i := by
            intro hai
            exact (Finset.disjoint_left.mp (hfr i) hai haResidual).elim
          unfold ChunkGeometry5.fineCount
          exact hcount_eq_of_notMem (g.fineChunks i) hnot
        have hsign : g.sign y = g.sign x := by
          funext i
          simp [ChunkGeometry5.sign, hcounts i]
        have hsev : g.severity y = g.severity x := by
          simp [ChunkGeometry5.severity, hcounts]
        exact Or.inl (hrole_mem_of_coarseRange y hkeyRange hsign hsev)
  · intro x ℓ hℓ
    have hflip_invol (v : CubeVertex n) (a : Fin n) :
        flipVertex5 (flipVertex5 v a) a = v := by
      funext i
      by_cases hia : i = a
      · subst i
        simp [flipVertex5]
      · simp [flipVertex5, hia]
    have hcoarse_flip_step (v : CubeVertex n) (a : Fin n)
        (ha : a ∈ g.coarseCoords) :
        g.coarseBin v = g.coarseBin (flipVertex5 v a) ∨
          binAdjacent5 (g.coarseBin v) (g.coarseBin (flipVertex5 v a)) := by
      obtain ⟨k, hak⟩ := by
        simpa [ChunkGeometry5.coarseCoords, Finset.mem_biUnion] using ha
      rcases g.chunks_disjoint with ⟨hcc, hcf, hff, hcr, hfr⟩
      have hcount_eq (i : Fin coarseChunkCount5) (hik : i ≠ k) :
          g.coarseCount v i = g.coarseCount (flipVertex5 v a) i := by
        have hai : a ∉ g.coarseChunks i := by
          intro hmem
          exact (Finset.disjoint_left.mp (hcc k i hik.symm) hak hmem).elim
        unfold ChunkGeometry5.coarseCount
        have hset :
            (g.coarseChunks i).filter (fun b => v b = true) =
              (g.coarseChunks i).filter (fun b => flipVertex5 v a b = true) := by
          ext b
          by_cases hb : b ∈ g.coarseChunks i
          · have hba : b ≠ a := by
              intro h
              subst b
              exact hai hb
            simp only [Finset.mem_filter]
            simp only [flipVertex5, Function.update_of_ne hba]
          · simp [hb]
        exact congrArg Finset.card hset
      have hcount_step :
          g.coarseCount v k + 1 = g.coarseCount (flipVertex5 v a) k ∨
          g.coarseCount (flipVertex5 v a) k + 1 = g.coarseCount v k := by
        unfold ChunkGeometry5.coarseCount
        by_cases hva : v a = true
        · have hset :
              (g.coarseChunks k).filter (fun b => v b = true) =
                insert a ((g.coarseChunks k).filter
                  (fun b => flipVertex5 v a b = true)) := by
            ext b
            by_cases hba : b = a
            · subst b
              simp [hak, hva, flipVertex5]
            · simp only [Finset.mem_filter, Finset.mem_insert]
              simp only [flipVertex5, Function.update_of_ne hba]
              simp [hba]
          have hnot : a ∉ (g.coarseChunks k).filter (fun b => flipVertex5 v a b = true) := by
            simp [Finset.mem_filter, flipVertex5, hak, hva]
          right
          have hc := congrArg Finset.card hset
          rw [Finset.card_insert_of_notMem hnot] at hc
          omega
        · have hset :
              (g.coarseChunks k).filter (fun b => flipVertex5 v a b = true) =
                insert a ((g.coarseChunks k).filter (fun b => v b = true)) := by
            ext b
            by_cases hba : b = a
            · subst b
              simp [hak, hva, flipVertex5]
            · simp only [Finset.mem_filter, Finset.mem_insert]
              simp only [flipVertex5, Function.update_of_ne hba]
              simp [hba]
          have hnot : a ∉ (g.coarseChunks k).filter (fun b => v b = true) := by
            simp [Finset.mem_filter, hva, hak]
          left
          have hc := congrArg Finset.card hset
          rw [Finset.card_insert_of_notMem hnot] at hc
          omega
      have hval_pair :
          (g.bin k (g.coarseCount v k)).val ≤
              (g.bin k (g.coarseCount (flipVertex5 v a) k)).val + 1 ∧
            (g.bin k (g.coarseCount (flipVertex5 v a) k)).val ≤
              (g.bin k (g.coarseCount v k)).val + 1 := by
        rcases hcount_step with hstep | hstep
        · have hmono := g.bin_monotone k (g.coarseCount v k)
            (g.coarseCount (flipVertex5 v a) k) (by omega)
          have hcon := g.bin_consecutive k (g.coarseCount v k)
          rw [hstep] at hcon
          exact ⟨by omega, by omega⟩
        · have hmono := g.bin_monotone k (g.coarseCount (flipVertex5 v a) k)
            (g.coarseCount v k) (by omega)
          have hcon := g.bin_consecutive k (g.coarseCount (flipVertex5 v a) k)
          rw [hstep] at hcon
          exact ⟨by omega, by omega⟩
      have hdist : Nat.dist (g.bin k (g.coarseCount v k)).val
          (g.bin k (g.coarseCount (flipVertex5 v a) k)).val ≤ 1 := by
        rcases hval_pair with ⟨h1, h2⟩
        simp only [Nat.dist]
        omega
      by_cases heq : g.coarseBin v = g.coarseBin (flipVertex5 v a)
      · exact Or.inl heq
      · right
        have hkdiff :
            g.bin k (g.coarseCount v k) ≠
              g.bin k (g.coarseCount (flipVertex5 v a) k) := by
          intro hk
          apply heq
          funext i
          by_cases hik : i = k
          · subst i
            exact hk
          · simp [ChunkGeometry5.coarseBin, hcount_eq i hik]
        have hdiffSet :
            (Finset.univ.filter (fun i : Fin coarseChunkCount5 =>
              g.coarseBin v i ≠ g.coarseBin (flipVertex5 v a) i)) = {k} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hi
            by_contra hik
            have heq' : g.coarseBin v i = g.coarseBin (flipVertex5 v a) i := by
              simp [ChunkGeometry5.coarseBin, hcount_eq i hik]
            exact hi heq'
          · intro hik
            subst i
            exact hkdiff
        refine ⟨?_, ?_⟩
        · rw [hdiffSet]
          simp
        · intro i
          by_cases hik : i = k
          · subst i
            exact hdist
          · have heq' : g.coarseBin v i = g.coarseBin (flipVertex5 v a) i := by
              simp [ChunkGeometry5.coarseBin, hcount_eq i hik]
            rw [heq']
            simp
    have hcoarseBin_compatible : ∀ v (i : CoarseKey5 n),
        i ∈ g.coarseRange v → (g.key v).1 ∈ binList5 i := by
      intro v i hi
      simp only [ChunkGeometry5.coarseRange, Finset.mem_insert, Finset.mem_image] at hi
      rcases hi with hbase | ⟨a, ha, rfl⟩
      · subst i
        by_cases hb : (g.key v).2 = true <;> simp [binList5, hb]
      · by_cases hb : g.boundary (flipVertex5 v a)
        · have hbin := hcoarse_flip_step v a ha
          have hi2 : (g.key (flipVertex5 v a)).2 = true := by
            simp [ChunkGeometry5.key, hb]
          simp only [binList5, hi2, if_pos, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hbin with heq | hadj
          · left
            exact (by simpa [ChunkGeometry5.key] using heq)
          · right
            have hsymm : binAdjacent5 (g.coarseBin (flipVertex5 v a)) (g.coarseBin v) := by
              unfold binAdjacent5 at hadj ⊢
              refine ⟨?_, ?_⟩
              · simpa [ne_comm] using hadj.1
              · intro i
                simpa [Nat.dist_comm] using hadj.2 i
            exact (by simpa [ChunkGeometry5.key] using hsymm)
        · have haChunks : ∃ k, a ∈ g.coarseChunks k := by
            simpa [ChunkGeometry5.coarseCoords, Finset.mem_biUnion] using ha
          obtain ⟨k, hak⟩ := haChunks
          have hbin : g.coarseBin v = g.coarseBin (flipVertex5 v a) := by
            by_contra hne
            apply hb
            exact ⟨k, a, hak, by simpa [hflip_invol] using hne⟩
          simp [binList5, ChunkGeometry5.key, hb, hbin]
    have hcoarse_keyAt (i : CoarseKey5 n) (t : CubeVertex m) (j : ℕ) :
        (keyAt5 J i t j).coarse = i := by
      by_cases hj : j ≤ J <;> simp [HiddenKey5.coarse, keyAt5, hj]
    have hsource : ℓ.coarse ∈ g.coarseRange x ∨ ℓ.coarse = g.key x := by
      unfold ChunkGeometry5.typeKeys at hℓ
      by_cases hlow : g.severity x ≤ J
      · rw [if_pos hlow] at hℓ
        simp only [Finset.mem_union, Finset.mem_image] at hℓ
        rcases hℓ with (⟨i, hi, heq⟩ | ⟨i, hi, heq⟩) | htail
        · left
          have heq' := congrArg HiddenKey5.coarse heq
          have hci : i = ℓ.coarse := by
            rw [hcoarse_keyAt] at heq'
            exact heq'
          rw [← hci]
          exact hi
        · right
          have heq' := congrArg HiddenKey5.coarse heq
          rw [hcoarse_keyAt] at heq'
          exact heq'.symm
        · right
          obtain ⟨j, hj, heq⟩ := htail
          have heq' := congrArg HiddenKey5.coarse heq
          rw [hcoarse_keyAt] at heq'
          exact heq'.symm
      · rw [if_neg hlow] at hℓ
        simp only [Finset.mem_image] at hℓ
        obtain ⟨i, hi, heq⟩ := hℓ
        left
        have heq' := congrArg HiddenKey5.coarse heq
        have hci : i = ℓ.coarse := by simpa [HiddenKey5.coarse] using heq'
        rw [← hci]
        exact hi
    rcases hsource with hrange | hkey
    · exact hcoarseBin_compatible x ℓ.coarse hrange
    · rw [hkey]
      exact hcoarseBin_compatible x (g.key x) (by simp [ChunkGeometry5.coarseRange])

/-! ### D5.5: states and the one-hot embedding (05:291–313) -/

/-- The outer representative of a fine count: merge distances `5.5` and `6.5` on the same side
of mid-weight (05:291–303). -/
def mergedFineCount5 (L q : ℕ) : ℕ :=
  if Nat.dist (2 * q) L = 11 then (if 2 * q < L then q - 1 else q + 1) else q

/-- The state quotient (05:291–313). Equal residual bits, coarse counts, merged fine counts and severity
determine a state. Roles in one state share key, signs, severity, parity and even type;
the one-hot embedding is injective, reproduces the residual bits, has dimension
`n + O(√n)`, and two even states adjacent to one odd state are at ambient distance at most `8`. -/
structure CubeStates5 {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ) where
  Site : Type
  [siteFintype : Fintype Site]
  [siteDecEq : DecidableEq Site]
  d : ℕ
  stateOf : CubeVertex n → Site
  oneHot : Site → CubeVertex d
  oneHot_injective : Function.Injective oneHot
  /-- The one-hot fine-count coordinates separate different majority signs (05:291–313,
  978–985), so short state tubes consult only nearby low-key signs. -/
  sign_distance : ∀ x y, hammingDist (g.sign x) (g.sign y) ≤
    hammingDist (oneHot (stateOf x)) (oneHot (stateOf y))
  resCoord : g.residual → Fin d
  resCoord_injective : Function.Injective resCoord
  oneHot_residual : ∀ x (a : g.residual), oneHot (stateOf x) (resCoord a) = x a.1
  state_determines : ∀ x y, stateOf x = stateOf y →
    g.key x = g.key y ∧ g.sign x = g.sign y ∧ g.severity x = g.severity y ∧
      (IsEvenRole x ↔ IsEvenRole y) ∧ g.evenType J x = g.evenType J y ∧
        g.optionalKey J x = g.optionalKey J y ∧ g.roleKey J x = g.roleKey J y
  data_determine_state : ∀ x y,
    (∀ a ∈ g.residual, x a = y a) →
    (∀ i, g.coarseCount x i = g.coarseCount y i) →
    (∀ i, mergedFineCount5 g.fineLength (g.fineCount x i) =
      mergedFineCount5 g.fineLength (g.fineCount y i)) →
    g.severity x = g.severity y → stateOf x = stateOf y
  neighbors : Site → Finset Site
  mem_neighbors : ∀ s t, t ∈ neighbors s ↔
    ∃ x y, stateOf x = s ∧ stateOf y = t ∧ (cube n).Adj x y
  degree_bound : ∀ s, (neighbors s).card ≤ 2 * n
  even_distance : ∀ b a a', a ∈ neighbors b → a' ∈ neighbors b →
    (∃ x, stateOf x = a ∧ IsEvenRole x) → (∃ x, stateOf x = a' ∧ IsEvenRole x) →
      hammingDist (oneHot a) (oneHot a') ≤ 8
  dimension_upper : (d : ℝ) ≤ n + 3 * (n : ℝ) ^ (1 / 2 : ℝ) + 301

attribute [instance] CubeStates5.siteFintype CubeStates5.siteDecEq

/-- L5.1e0 (05:291–313), with the constants in the order `∀ ε, ∃ n₀`: the state quotient exists at every
layout, and its dimension is at most `(1 + ε) n` once `n ≥ n₀(ε)`. -/
theorem L5_1e0 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (m J : ℕ) (g : ChunkGeometry5 n m),
    ∃ S : CubeStates5 g J, (S.d : ℝ) ≤ (1 + ε) * n := by
  sorry

end HypercubeRamsey
