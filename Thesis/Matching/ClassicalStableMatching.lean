import Mathlib.Order.Lattice
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Defs


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section
open Classical


/-!
# Classical Stable Matching Problem

This file formalizes the classical college admissions problem (Gale-Shapley 1962)
using Fleiner's choice function framework with explicit top-k selection.

## Main approach

Instead of using Fleiner's abstract choice functions, we work directly with:
- **Schools**: Select their top-k preferred students (quota k)
- **Students**: Select their top-1 preferred school

This makes the `increasing` property obvious, allowing us to apply Fleiner's
lattice structure theorems without proving increasing for the general case.

## Main results

- `stable_matching_exists_classical`: Existence of stable matchings
- `stable_matchings_lattice_classical`: Stable matchings form a lattice
- `rural_hospital_classical`: Rural Hospital Theorem

## References

- Fleiner (2002): "Some results on stable matchings and fixed points"
- Roth & Sotomayor (1990): "Two-Sided Matching", Chapter 5
-/

variable {M W : Type*} [DecidableEq M] [DecidableEq W] [Fintype M] [Fintype W]


/-! ### Basic definitions -/

/-- Schools -/
abbrev Schools (M : Type*) := Finset M

/-- Students -/
abbrev Students (W : Type*) := Finset W

/-- School quotas -/
abbrev Quotas (M : Type*) := M → ℕ

/-- Linear preference order: irreflexive, transitive, total -/
abbrev LinearPref (α : Type*) := α → α → Prop

/-- A linear order is strict, transitive, and total -/
def IsLinearPref {α : Type*} (r : α → α → Prop) : Prop :=
  (∀ x, ¬r x x) ∧                           -- irreflexive
  (∀ x y z, r x y → r y z → r x z) ∧        -- transitive
  (∀ x y, x ≠ y → r x y ∨ r y x)            -- total


/-! ### Top-k selection for schools -/

/-- Count how many students in S are strictly better than w for school m -/
def countBetter (pref_m : LinearPref W) (S : Finset W) (w : W) : ℕ :=
  (S.filter (fun w' => pref_m w' w)).card

/-- School m's top-k students from S: those with < k better students in S -/
def topK (pref_m : LinearPref W) (k : ℕ) (S : Finset W) : Finset W :=
  S.filter (fun w => countBetter pref_m S w < k)

/-- Student w's top school from S: the unique best one -/
def topOne (pref_w : LinearPref M) (S : Finset M) : Finset M :=
  S.filter (fun m => ∀ m' ∈ S, m = m' ∨ pref_w m m')


/-! ### Choice functions for the classical model -/

/-- School choice function: select top quota(m) students -/
def choiceM_classical
    (school_pref : M → LinearPref W)
    (quota : Quotas M)
    (S : Finset (M × W))
    (m : M) : Finset (M × W) :=
  let students_for_m := S.filter (fun e => e.1 = m)
  let student_set := students_for_m.image (·.2)
  let chosen_students := topK (school_pref m) (quota m) student_set
  students_for_m.filter (fun e => e.2 ∈ chosen_students)

/-- Student choice function: select top-1 school -/
def choiceW_classical
    (student_pref : W → LinearPref M)
    (S : Finset (M × W))
    (w : W) : Finset (M × W) :=
  let schools_for_w := S.filter (fun e => e.2 = w)
  let school_set := schools_for_w.image (·.1)
  let chosen_schools := topOne (student_pref w) school_set
  schools_for_w.filter (fun e => e.1 ∈ chosen_schools)

/-- All schools' choices combined -/
def choiceM_all
    (school_pref : M → LinearPref W)
    (quota : Quotas M)
    (S : Finset (M × W)) : Finset (M × W) :=
  Finset.univ.biUnion (fun m => choiceM_classical school_pref quota S m)

/-- All students' choices combined -/
def choiceW_all
    (student_pref : W → LinearPref M)
    (S : Finset (M × W)) : Finset (M × W) :=
  Finset.univ.biUnion (fun w => choiceW_classical student_pref S w)


/-! ### Stability definitions (Fleiner's framework) -/

/-- A pair (S_M, S_W) is stable if:
    - S_M ∪ S_W covers all edges
    - choiceM(S_M) = S_M ∩ S_W
    - choiceW(S_W) = S_M ∩ S_W -/
def IsStablePair
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S_M S_W : Finset (M × W)) : Prop :=
  S_M ∪ S_W = E ∧
  choiceM_all school_pref quota S_M = S_M ∩ S_W ∧
  choiceW_all student_pref S_W = S_M ∩ S_W

/-- A matching is stable if it's the intersection of a stable pair -/
def IsStableMatching
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S : Finset (M × W)) : Prop :=
  ∃ S_M S_W, IsStablePair E school_pref student_pref quota S_M S_W ∧
             S = S_M ∩ S_W


/-! ### Key properties of top-k selection -/

/-! ### Helper lemmas for topK_increasing -/

/-! ### Helper lemmas for topK_increasing -/

/-- If x is preferred to y, then x has strictly fewer better candidates than y -/
lemma countBetter_strict_mono (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m)
    (S : Finset W) (x : W) (hx : x ∈ S) (y : W) (hy : y ∈ S) (hxy : pref_m x y) :
    countBetter pref_m S x < countBetter pref_m S y := by
  unfold countBetter
  have hBx_subset_By : S.filter (fun w' => pref_m w' x) ⊆
                       S.filter (fun w' => pref_m w' y) := by
    intro w' hw'
    simp only [Finset.mem_filter] at hw' ⊢
    constructor
    · exact hw'.1
    · exact h_lin.2.1 w' x y hw'.2 hxy -- transitivity

  apply Finset.card_lt_card
  simp only [Finset.ssubset_iff_subset_ne]
  constructor
  · exact hBx_subset_By
  · intro h_eq
    -- Show x ∈ filter for y but not for x
    have hx_in_y : x ∈ S.filter (fun w' => pref_m w' y) := by
      simp only [Finset.mem_filter]
      exact ⟨hx, hxy⟩
    have hx_not_in_x : x ∉ S.filter (fun w' => pref_m w' x) := by
      simp only [Finset.mem_filter, not_and]
      intro _
      exact h_lin.1 x -- irreflexive
    rw [h_eq] at hx_not_in_x
    contradiction

/-- countBetter is injective on S for linear preferences -/
lemma countBetter_inj (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m)
    (S : Finset W) (x : W) (hx : x ∈ S) (y : W) (hy : y ∈ S) :
    countBetter pref_m S x = countBetter pref_m S y → x = y := by
  intro h_eq
  by_contra hxy
  -- By totality, either x > y or y > x
  cases h_lin.2.2 x y hxy with
  | inl hxy' =>
      have := countBetter_strict_mono pref_m h_lin S x hx y hy hxy'
      omega
  | inr hyx =>
      have := countBetter_strict_mono pref_m h_lin S y hy x hx hyx
      omega

/-- The set of values of countBetter on S is exactly {0, ..., |S|-1} -/
lemma countBetter_image (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m)
    (S : Finset W) :
    S.image (countBetter pref_m S) = Finset.range S.card := by
  refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun x hx => _ ) _;
  · refine' Finset.mem_range.mpr ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.filter_ssubset.mpr _ ) ) ( by simp +decide ) );
    exact ⟨ x, hx, h_lin.1 x ⟩;
  · rw [ Finset.card_image_of_injOn ];
    · simp +decide;
    · exact fun x hx y hy hxy => countBetter_inj pref_m h_lin S x hx y hy hxy

/-- For a linear preference, topK selects exactly min(k, |S|) students -/
lemma topK_card (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m)
    (k : ℕ) (S : Finset W) :
    (topK pref_m k S).card = min k S.card := by
    -- By definition of `topK`, the set of values of `countBetter` on `S` is exactly `{0, ..., |S|-1}`.
    have h_countBetter_image : S.image (countBetter pref_m S) = Finset.range S.card := by
      apply countBetter_image pref_m h_lin S;
    -- By definition of `topK`, the set of values of `countBetter` on `topK pref_m k S` is exactly `{0, ..., min(k, |S|)-1}`.
    have h_topK_countBetter_image : (topK pref_m k S).image (countBetter pref_m S) = Finset.range (min k S.card) := by
      ext; simp [topK];
      constructor <;> intro h;
      · obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ := h; exact ⟨ ha₂, by linarith [ Finset.mem_range.mp ( h_countBetter_image ▸ Finset.mem_image_of_mem _ ha₁ ) ] ⟩ ;
      · replace h_countBetter_image := Finset.ext_iff.mp h_countBetter_image ‹_›; aesop;
    rw [ ← Finset.card_range ( Min.min k S.card ), ← h_topK_countBetter_image, Finset.card_image_of_injOn ];
    exact fun x hx y hy hxy => countBetter_inj pref_m h_lin S x ( Finset.mem_filter.mp hx |>.1 ) y ( Finset.mem_filter.mp hy |>.1 ) hxy



/-- Top-k is obviously increasing: more students → can choose at least as many -/
theorem topK_increasing (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m) (k : ℕ) :
    ∀ S T : Finset W, S ⊆ T → (topK pref_m k S).card ≤ (topK pref_m k T).card := by
      intros S T hST
      have h_card : min k S.card ≤ min k T.card := by
        exact min_le_min le_rfl ( Finset.card_le_card hST );
      convert h_card using 1;
      · apply topK_card pref_m h_lin k S;
      · apply topK_card pref_m h_lin k T

/-- topOne returns exactly one element for nonempty sets with linear preferences -/
lemma topOne_card_eq_one (pref_w : LinearPref M) (h_lin : IsLinearPref pref_w)
    (S : Finset M) (hS : S.Nonempty) :
    (topOne pref_w S).card = 1 := by
  rcases h_lin with ⟨ h₁, h₂, h₃ ⟩;
  obtain ⟨m, hm⟩ : ∃ m ∈ S, ∀ n ∈ S, n = m ∨ pref_w m n := by
    obtain ⟨ m, hm ⟩ := Finset.exists_max_image S ( fun m => ( Finset.filter ( fun n => pref_w m n ) S ).card ) hS;
    refine' ⟨ m, hm.1, fun n hn => _ ⟩;
    contrapose! hm;
    refine' fun hm' => ⟨ n, hn, Finset.card_lt_card _ ⟩;
    simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
    grind;
  refine' Finset.card_eq_one.mpr ⟨ m, _ ⟩;
  ext n; simp [topOne, hm];
  grind

/-- Top-1 is increasing -/
theorem topOne_increasing (pref_w : LinearPref M)
    (h_lin : IsLinearPref pref_w) :
    ∀ S T : Finset M, S ⊆ T → (topOne pref_w S).card ≤ (topOne pref_w T).card := by
  intro S T hST
  by_cases hS : S = ∅
  · simp [topOne, hS]
  · by_cases hT : T = ∅
    · have : S = ∅ := Finset.subset_empty.mp (hT ▸ hST)
      contradiction
    · -- Both nonempty, both have card = 1
      have hS_ne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
      have hT_ne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      rw [topOne_card_eq_one pref_w h_lin S hS_ne]
      rw [topOne_card_eq_one pref_w h_lin T hT_ne]

/-- School choice is increasing per school -/
theorem choiceM_classical_increasing_per_school
    (school_pref : M → LinearPref W) (quota : Quotas M) (m : M) :
    ∀ S T : Finset (M × W), S ⊆ T →
      (choiceM_classical school_pref quota S m).card ≤
      (choiceM_classical school_pref quota T m).card := by
  intro S T hST
  unfold choiceM_classical
  admit

/-- School choice is increasing overall -/
theorem choiceM_classical_increasing
    (school_pref : M → LinearPref W) (quota : Quotas M) :
    ∀ S T : Finset (M × W), S ⊆ T →
      (choiceM_all school_pref quota S).card ≤
      (choiceM_all school_pref quota T).card := by
  intro S T hST
  unfold choiceM_all
  admit

/-- Student choice is increasing -/
theorem choiceW_classical_increasing
    (student_pref : W → LinearPref M) :
    ∀ S T : Finset (M × W), S ⊆ T →
      (choiceW_all student_pref S).card ≤
      (choiceW_all student_pref T).card := by
  intro S T hST
  admit


/-! ### Comonotonicity properties -/

/-- School choice satisfies property (12): C(A) ⊆ A -/
theorem choiceM_classical_subset
    (school_pref : M → LinearPref W) (quota : Quotas M) (S : Finset (M × W)) :
    choiceM_all school_pref quota S ⊆ S := by
  unfold choiceM_all choiceM_classical
  intro e he
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
  obtain ⟨m, hm⟩ := he
  simp only [Finset.mem_filter] at hm
  exact hm.1.1

/-- Student choice satisfies property (12): C(A) ⊆ A -/
theorem choiceW_classical_subset
    (student_pref : W → LinearPref M) (S : Finset (M × W)) :
    choiceW_all student_pref S ⊆ S := by
  unfold choiceW_all choiceW_classical
  intro e he
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
  obtain ⟨w, hw⟩ := he
  simp only [Finset.mem_filter] at hw
  exact hw.1.1

/-- The complement function for schools is monotone (property 13) -/
theorem choiceM_classical_complement_monotone
    (school_pref : M → LinearPref W)
    (quota : Quotas M)
    (h_linear : ∀ m, IsLinearPref (school_pref m)) :
    Monotone (fun S => S \ choiceM_all school_pref quota S) := by
  intro S T hST x hx;
  unfold choiceM_all at *;
  unfold choiceM_classical at *;
  simp_all +decide [ Finset.subset_iff ];
  contrapose! hx;
  unfold topK at hx ⊢; simp_all +decide [ Finset.filter_eq', Finset.filter_and ] ;
  intro hxS; refine' lt_of_le_of_lt _ hx.2; refine' Finset.card_mono _; intro y hy; aesop;

/-- The complement function for students is monotone (property 13) -/
theorem choiceW_classical_complement_monotone
    (student_pref : W → LinearPref M)
    (h_linear : ∀ w, IsLinearPref (student_pref w)) :
    Monotone (fun S => S \ choiceW_all student_pref S) := by
  intro S T hST
  refine fun x hx => Finset.mem_sdiff.mpr ⟨ ?_, ?_ ⟩;
  · exact hST ( Finset.mem_sdiff.mp hx |>.1 );
  · unfold choiceW_all at *;
    simp_all +decide [ Finset.mem_biUnion, choiceW_classical ];
    unfold topOne at *; aesop;

/-! ### Property 14 -/

/-- School choice satisfies property 14:
    C(A) = C(B) whenever C(A) ⊆ B ⊆ A -/
theorem choiceM_classical_property14
    (school_pref : M → LinearPref W)
    (quota : Quotas M)
    (h_linear : ∀ m, IsLinearPref (school_pref m)) :
    ∀ A B : Finset (M × W),
      choiceM_all school_pref quota A ⊆ B → B ⊆ A →
      choiceM_all school_pref quota B = choiceM_all school_pref quota A := by
  intro A B hAB hBA
  apply le_antisymm;
  · have := choiceM_classical_increasing school_pref quota;
    specialize this B A hBA;
    contrapose! this;
    refine' Finset.card_lt_card _;
    refine' ⟨ _, _ ⟩;
    · intro x hx; simp_all +decide [ Finset.subset_iff ] ;
      unfold choiceM_all at *; simp_all +decide [ Finset.mem_biUnion ] ;
      unfold choiceM_classical at *; simp_all +decide [ Finset.mem_filter ] ;
      unfold topK at *; simp_all +decide [ Finset.mem_filter ] ;
      refine' lt_of_le_of_lt _ hx.2;
      exact Finset.card_mono ( Finset.filter_subset_filter _ ( Finset.image_subset_image ( Finset.filter_subset_filter _ ( Finset.subset_iff.mpr fun x hx => hBA _ _ hx ) ) ) );
    · exact this;
  · intro x hx;
    unfold choiceM_all at *;
    simp_all +decide [ Finset.subset_iff, choiceM_classical ];
    refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
    · aesop;
    · refine' lt_of_le_of_lt _ ( Finset.mem_filter.mp hx.2 |>.2 );
      refine' Finset.card_mono _;
      intro w hw; aesop;



/-
Property 14 for topOne: if the top choice from S is in T, and T is a subset of S, then the top choice from T is the same as from S.
-/
lemma topOne_property14 (pref_w : LinearPref M) (h_lin : IsLinearPref pref_w)
    (S T : Finset M) (h_sub : topOne pref_w S ⊆ T) (h_TS : T ⊆ S) :
    topOne pref_w T = topOne pref_w S := by
      -- If the top choice from S is in T, then the top choice from T is also in S.
      have h_top_in_S : ∀ m ∈ topOne pref_w S, m ∈ T → m ∈ topOne pref_w T := by
        unfold topOne; aesop;
      by_cases hS : S.Nonempty <;> by_cases hT : T.Nonempty <;> simp_all +decide [ Finset.subset_iff ];
      · have := topOne_card_eq_one pref_w h_lin S hS; have := topOne_card_eq_one pref_w h_lin T hT; simp_all +decide [ Finset.card_eq_one ] ;
        aesop;
      · unfold topOne at *; aesop;
      · exact False.elim ( h_TS hT.choose_spec )



/-- Student choice satisfies property 14 -/
theorem choiceW_classical_property14
    (student_pref : W → LinearPref M)
    (h_linear : ∀ w, IsLinearPref (student_pref w)) :
    ∀ A B : Finset (M × W),
      choiceW_all student_pref A ⊆ B → B ⊆ A →
      choiceW_all student_pref B = choiceW_all student_pref A := by
  intro A B hAB hBA
  -- For each student w, the choice from B is the same as from A.
  have h_topOne_eq : ∀ w : W, choiceW_classical student_pref A w ⊆ B → B.filter (fun e => e.2 = w) ⊆ A.filter (fun e => e.2 = w) → choiceW_classical student_pref B w = choiceW_classical student_pref A w := by
    intro w hwB hwA
    have h_topOne_eq : topOne (student_pref w) (B.filter (fun e => e.2 = w) |>.image Prod.fst) = topOne (student_pref w) (A.filter (fun e => e.2 = w) |>.image Prod.fst) := by
      apply topOne_property14 (student_pref w) (h_linear w);
      · intro m hm; simp_all +decide [ choiceW_classical, topOne ] ;
        grind;
      · exact Finset.image_subset_image hwA;
    ext ⟨m, w'⟩; simp +decide [choiceW_classical] at *; aesop;
  -- By definition of choiceW_all, we can write it as a union over all students.
  have h_choiceW_all_union : ∀ S : Finset (M × W), choiceW_all student_pref S = Finset.biUnion Finset.univ (fun w => choiceW_classical student_pref S w) := by
    apply fun S => (fun {α} {s t} => Finset.val_inj.mp) rfl;
  grind



/-! ### Fixed point approach (Fleiner Section 2) -/

/-- The monotone function from Fleiner equation (9) -/
def fixedPointF
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S_M : Finset (M × W)) : Finset (M × W) :=
  let complementM := S_M \ choiceM_all school_pref quota S_M
  let S_W := E \ complementM
  let complementW := S_W \ choiceW_all student_pref S_W
  E \ complementW

/-- The fixed point function is monotone -/
theorem fixedPointF_monotone
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_M : ∀ m, IsLinearPref (school_pref m))
    (h_linear_W : ∀ w, IsLinearPref (student_pref w)) :
    Monotone (fixedPointF E school_pref student_pref quota) := by
  intro A B hAB
  unfold fixedPointF
  have h_complement : (A \ choiceM_all school_pref quota A) ⊆
                       (B \ choiceM_all school_pref quota B) := by
    apply choiceM_classical_complement_monotone school_pref quota h_linear_M hAB
  have h_complementW : (E \ (A \ choiceM_all school_pref quota A)) \
                       choiceW_all student_pref (E \ (A \ choiceM_all school_pref quota A)) ⊇
                       (E \ (B \ choiceM_all school_pref quota B)) \
                       choiceW_all student_pref (E \ (B \ choiceM_all school_pref quota B)) := by
    apply choiceW_classical_complement_monotone student_pref h_linear_W
    exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) h_complement
  exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) h_complementW

/-- Iteration of the fixed point function -/
def iterateF
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M) : ℕ → Finset (M × W)
  | 0 => ∅
  | n + 1 => fixedPointF E school_pref student_pref quota (iterateF E school_pref student_pref quota n)

/-- The iteration is monotone -/
theorem iterateF_monotone
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_M : ∀ m, IsLinearPref (school_pref m))
    (h_linear_W : ∀ w, IsLinearPref (student_pref w))
    (n : ℕ) :
    iterateF E school_pref student_pref quota n ⊆
    iterateF E school_pref student_pref quota (n + 1) := by
  induction n with
  | zero =>
      -- iterateF 0 = ∅ ⊆ fixedPointF ∅
      unfold iterateF
      apply Finset.empty_subset
  | succ n ih =>
      -- iterateF (n+1) ⊆ iterateF (n+2)
      -- = fixedPointF (iterateF n) ⊆ fixedPointF (iterateF (n+1))
      unfold iterateF
      apply fixedPointF_monotone E school_pref student_pref quota h_linear_M h_linear_W
      exact ih


/-- fixedPointF always returns a subset of E -/
lemma fixedPointF_subset_E
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (X : Finset (M × W)) :
    fixedPointF E school_pref student_pref quota X ⊆ E := by
  unfold fixedPointF
  apply Finset.sdiff_subset

theorem iterateF_stabilizes
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_M : ∀ m, IsLinearPref (school_pref m))
    (h_linear_W : ∀ w, IsLinearPref (student_pref w)) :
    ∃ n, iterateF E school_pref student_pref quota n =
         iterateF E school_pref student_pref quota (n + 1) := by
  have h_monotone : Monotone (iterateF E school_pref student_pref quota) := by
    exact monotone_nat_of_le_succ fun n =>
      iterateF_monotone E school_pref student_pref quota h_linear_M h_linear_W n

  -- All elements in range are subsets of E, and E is finite
  have h_bounded : ∀ n, iterateF E school_pref student_pref quota n ⊆ E := by
    intro n
    induction n with
    | zero =>
        unfold iterateF
        exact Finset.empty_subset E
    | succ n _ =>
        unfold iterateF
        exact fixedPointF_subset_E E school_pref student_pref quota _

  -- Range is finite because it's a subset of E.powerset (which is finite)
  have h_finite : Set.Finite (Set.range (iterateF E school_pref student_pref quota)) := by
    have h_powerset_finite : (E.powerset : Set (Finset (M × W))).Finite := Set.toFinite _
    apply Set.Finite.subset h_powerset_finite
    intro S hS
    obtain ⟨n, rfl⟩ := hS
    simp only [Finset.mem_coe, Finset.mem_powerset]
    exact h_bounded n

  contrapose! h_finite
  exact Set.infinite_range_of_injective (StrictMono.injective (strictMono_nat_of_lt_succ fun n =>
    lt_of_le_of_ne (h_monotone n.le_succ) (h_finite n)))



/-- A fixed point exists -/
theorem fixedPoint_exists
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_M : ∀ m, IsLinearPref (school_pref m))
    (h_linear_W : ∀ w, IsLinearPref (student_pref w)) :
    ∃ S_M, fixedPointF E school_pref student_pref quota S_M = S_M := by
  obtain ⟨n, hn⟩ := iterateF_stabilizes E school_pref student_pref quota h_linear_M h_linear_W
  use iterateF E school_pref student_pref quota n
  exact hn.symm

/-! ### Existence of stable matchings (Fleiner Theorem 3.1) -/

/-- Construct S_W from S_M using equation (7) -/
def constructSW
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (quota : Quotas M)
    (S_M : Finset (M × W)) : Finset (M × W) :=
  E \ (S_M \ choiceM_all school_pref quota S_M)





/-- Helper lemma: A \ (A \ B) = A ∩ B when B ⊆ A -/
lemma sdiff_sdiff_eq_inter {α : Type*} [DecidableEq α] (A B : Finset α) (h : B ⊆ A) :
    A \ (A \ B) = A ∩ B := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · intro ⟨hxA, hx⟩
    constructor
    · exact hxA
    · by_contra hxB
      apply hx
      exact ⟨hxA, hxB⟩
  · intro ⟨hxA, hxB⟩
    constructor
    · exact hxA
    · intro ⟨_, hxnB⟩
      exact hxnB hxB

/-- Helper lemma: (E \ X) ∩ Y = Y \ X when Y ⊆ E -/
lemma sdiff_inter_eq {α : Type*} [DecidableEq α] (E X Y : Finset α) (h : Y ⊆ E) :
    (E \ X) ∩ Y = Y \ X := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · intro ⟨⟨_, hxX⟩, hxY⟩
    exact ⟨hxY, hxX⟩
  · intro ⟨hxY, hxX⟩
    exact ⟨⟨h hxY, hxX⟩, hxY⟩

/-- When B ⊆ A, we have A ∩ B = B -/
lemma inter_eq_right_of_subset {α : Type*} [DecidableEq α] {A B : Finset α} (h : B ⊆ A) :
    A ∩ B = B := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · intro ⟨_, hxB⟩; exact hxB
  · intro hxB; exact ⟨h hxB, hxB⟩

/-- S_M from fixed point is subset of E -/
lemma fixedPoint_subset_E
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S_M : Finset (M × W))
    (h_fixed : fixedPointF E school_pref student_pref quota S_M = S_M) :
    S_M ⊆ E := by
  unfold fixedPointF at h_fixed
  rw [←h_fixed]
  apply Finset.sdiff_subset

theorem fixedPoint_gives_stablePair
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S_M : Finset (M × W))
    (h_fixed : fixedPointF E school_pref student_pref quota S_M = S_M) :
    IsStablePair E school_pref student_pref quota S_M
                 (constructSW E school_pref quota S_M) := by
  unfold IsStablePair constructSW

  -- Introduce notation following Fleiner
  set complementM := S_M \ choiceM_all school_pref quota S_M with hcompM
  set S_W := E \ complementM with hSW
  set complementW := S_W \ choiceW_all student_pref S_W with hcompW

  -- Extract from h_fixed that S_M = E \ complementW
  have h_SM_eq : S_M = E \ complementW := by
    conv_lhs => rw [←h_fixed]
    unfold fixedPointF
    rfl

  -- We need choiceM_all S_M ⊆ S_M (property 12)
  have hchoiceM_sub : choiceM_all school_pref quota S_M ⊆ S_M :=
    choiceM_classical_subset school_pref quota S_M

  -- We need choiceW_all S_W ⊆ S_W (property 12)
  have hchoiceW_sub : choiceW_all student_pref S_W ⊆ S_W :=
    choiceW_classical_subset student_pref S_W

  -- We need S_M ⊆ E
  have hSM_sub : S_M ⊆ E := fixedPoint_subset_E E school_pref student_pref quota S_M h_fixed

  -- We also need S_W ⊆ E
  have hSW_sub : S_W ⊆ E := by
    rw [hSW]
    apply Finset.sdiff_subset

  constructor
  · -- Goal 1: S_M ∪ S_W = E
    ext e
    simp only [Finset.mem_union]
    constructor
    · intro h
      cases h with
      | inl hS => exact hSM_sub hS
      | inr hW => exact hSW_sub hW
    · intro he
      -- e ∈ E, show e ∈ S_M ∨ e ∈ S_W
      by_cases h : e ∈ complementM
      · -- e ∈ complementM
        -- From S_W = E \ complementM, we have e ∉ S_W
        -- From S_M = E \ complementW, we need to show e ∉ complementW
        left
        rw [h_SM_eq]
        simp only [Finset.mem_sdiff]
        constructor
        · exact he
        · -- Need: e ∉ complementW
          intro hcontra
          -- e ∈ complementW means e ∈ S_W and e ∉ choiceW_all S_W
          rw [hcompW] at hcontra
          simp only [Finset.mem_sdiff] at hcontra
          -- But e ∉ S_W since e ∈ complementM and S_W = E \ complementM
          have : e ∉ S_W := by
            rw [hSW]
            simp only [Finset.mem_sdiff, not_and, not_not]
            intro _
            exact h
          exact this hcontra.1
      · -- e ∉ complementM
        right
        rw [hSW]
        exact Finset.mem_sdiff.mpr ⟨he, h⟩

  constructor
  · -- Goal 2: choiceM_all S_M = S_M ∩ S_W
    calc choiceM_all school_pref quota S_M
        = S_M ∩ choiceM_all school_pref quota S_M := by
          exact (inter_eq_right_of_subset hchoiceM_sub).symm
      _ = S_M \ (S_M \ choiceM_all school_pref quota S_M) := by
          exact (sdiff_sdiff_eq_inter S_M (choiceM_all school_pref quota S_M) hchoiceM_sub).symm
      _ = S_M \ complementM := by rw [←hcompM]
      _ = S_M ∩ (E \ complementM) := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_inter]
          constructor
          · intro ⟨hxS, hxnC⟩
            exact ⟨hxS, hSM_sub hxS, hxnC⟩
          · intro ⟨hxS, _, hxnC⟩
            exact ⟨hxS, hxnC⟩
      _ = S_M ∩ S_W := by rw [←hSW]

  · -- Goal 3: choiceW_all S_W = S_M ∩ S_W
    calc choiceW_all student_pref S_W
        = S_W ∩ choiceW_all student_pref S_W := by
          exact (inter_eq_right_of_subset hchoiceW_sub).symm
      _ = S_W \ (S_W \ choiceW_all student_pref S_W) := by
          exact (sdiff_sdiff_eq_inter S_W (choiceW_all student_pref S_W) hchoiceW_sub).symm
      _ = S_W \ complementW := by rw [←hcompW]
      _ = (E \ complementW) ∩ S_W := by
          exact (sdiff_inter_eq E complementW S_W hSW_sub).symm
      _ = S_M ∩ S_W := by rw [←h_SM_eq]








/-- Main existence theorem: stable matchings always exist -/
theorem stable_matching_exists_classical
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_M : ∀ m, IsLinearPref (school_pref m))
    (h_linear_W : ∀ w, IsLinearPref (student_pref w)) :
    ∃ S, IsStableMatching E school_pref student_pref quota S := by
  obtain ⟨S_M, h_fixed⟩ := fixedPoint_exists E school_pref student_pref quota h_linear_M h_linear_W
  let S_W := constructSW E school_pref quota S_M
  have h_stable := fixedPoint_gives_stablePair E school_pref student_pref quota S_M h_fixed
  exact ⟨S_M ∩ S_W, S_M, S_W, h_stable, rfl⟩


/-! ### Lattice structure (Fleiner Theorem 5.3) -/

/-- Join operation: C_M(S₁ ∪ S₂) -/
def matchingJoin
    (school_pref : M → LinearPref W)
    (quota : Quotas M)
    (S₁ S₂ : Finset (M × W)) : Finset (M × W) :=
  choiceM_all school_pref quota (S₁ ∪ S₂)

/-- Meet operation: C_W(S₁ ∪ S₂) -/
def matchingMeet
    (student_pref : W → LinearPref M)
    (S₁ S₂ : Finset (M × W)) : Finset (M × W) :=
  choiceW_all student_pref (S₁ ∪ S₂)


/-- Male supremum = Female infimum (Fleiner Theorem 5.3) -/
theorem polarity_property
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (S₁ S₂ : Finset (M × W))
    (h₁ : IsStableMatching E school_pref student_pref quota S₁)
    (h₂ : IsStableMatching E school_pref student_pref quota S₂) :
    matchingJoin school_pref quota S₁ S₂ = matchingMeet student_pref S₁ S₂ := by
  admit

/--*************************************
 *                                     *
 *  Вспомогательные леммы от Aristotle *
 *                                     *
 *************************************-/


lemma choiceM_is_matching
    (school_pref : M → LinearPref W)
    (quota : Quotas M)
    (h_linear : ∀ m, IsLinearPref (school_pref m))
    (S : Finset (M × W)) :
    ∀ m, ((choiceM_all school_pref quota S).filter (fun e => e.1 = m)).card ≤ quota m := by
      intros m
      have h_card : (Finset.filter (fun e => e.1 = m) (choiceM_all school_pref quota S)).card = (topK (school_pref m) (quota m) (S.filter (fun e => e.1 = m) |>.image (fun e => e.2))).card := by
        unfold choiceM_all;
        refine' Finset.card_bij ( fun e he => e.2 ) _ _ _ <;> simp +decide [ choiceM_classical ];
        · aesop;
        · grind;
        · unfold topK; aesop;
      rw [ h_card, topK_card _ ( h_linear m ) ];
      exact min_le_left _ _

lemma choiceW_is_matching
    (student_pref : W → LinearPref M)
    (h_linear : ∀ w, IsLinearPref (student_pref w))
    (S : Finset (M × W)) :
    ∀ w, ((choiceW_all student_pref S).filter (fun e => e.2 = w)).card ≤ 1 := by
      intro w
      unfold choiceW_all;
      refine' Finset.card_le_one.mpr _;
      unfold choiceW_classical; simp +decide ;
      intro a b ha hb hb' c d hc hd hd'; subst_vars; simp_all +decide [ topOne ] ;
      cases hb c hc <;> cases hd a ha <;> have := h_linear d <;> cases this <;> tauto;

def IsMatching (quota : Quotas M) (S : Finset (M × W)) : Prop :=
  (∀ m, (S.filter (fun e => e.1 = m)).card ≤ quota m) ∧
  (∀ w, (S.filter (fun e => e.2 = w)).card ≤ 1)

lemma stable_implies_matching
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (S : Finset (M × W))
    (h : IsStableMatching E school_pref student_pref quota S) :
    IsMatching quota S := by
      rcases h with ⟨ S_M, S_W, h_pair, rfl ⟩;
      obtain ⟨ h₁, h₂, h₃ ⟩ := h_pair;
      constructor;
      · intro m
        have := choiceM_is_matching school_pref quota h_linear_m S_M m
        aesop;
      · intro w; rw [ ← h₃ ] ; exact?;

lemma size_eq_of_subset_fixedPoint
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (S_M1 S_M2 : Finset (M × W))
    (h_fp1 : fixedPointF E school_pref student_pref quota S_M1 = S_M1)
    (h_fp2 : fixedPointF E school_pref student_pref quota S_M2 = S_M2)
    (h_subset : S_M1 ⊆ S_M2) :
    (choiceM_all school_pref quota S_M1).card = (choiceM_all school_pref quota S_M2).card := by
      have h_card_eq : (choiceM_all school_pref quota S_M1).card ≤ (choiceM_all school_pref quota S_M2).card ∧ (choiceW_all student_pref (E \ (S_M2 \ choiceM_all school_pref quota S_M2))).card ≤ (choiceW_all student_pref (E \ (S_M1 \ choiceM_all school_pref quota S_M1))).card := by
        apply And.intro;
        · exact?;
        · apply_rules [ choiceW_classical_increasing ];
          apply Finset.sdiff_subset_sdiff
          simp [h_subset];
          apply_rules [ choiceM_classical_complement_monotone ];
      convert h_card_eq.1.antisymm _;
      convert h_card_eq.2 using 1;
      · convert congr_arg Finset.card ( fixedPoint_gives_stablePair E school_pref student_pref quota S_M2 h_fp2 |>.2.1 ) using 1;
        convert congr_arg Finset.card ( fixedPoint_gives_stablePair E school_pref student_pref quota S_M2 h_fp2 |>.2.2 ) using 1;
      · convert congr_arg Finset.card ( fixedPoint_gives_stablePair E school_pref student_pref quota S_M1 h_fp1 |>.2.1 ) using 1;
        exact congr_arg Finset.card ( fixedPoint_gives_stablePair E school_pref student_pref quota S_M1 h_fp1 |>.2.2 )

lemma stablePair_implies_fixedPoint
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S_M S_W : Finset (M × W))
    (h_pair : IsStablePair E school_pref student_pref quota S_M S_W) :
    fixedPointF E school_pref student_pref quota S_M = S_M := by
      obtain ⟨ h₁, h₂, h₃ ⟩ := h_pair;
      simp +decide only [fixedPointF, h₂];
      -- Let's simplify the expression inside the set difference.
      have h_simp : E \ (S_M \ (S_M ∩ S_W)) = S_W := by
        grind;
      grind

def iterateFrom
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (start : Finset (M × W)) : ℕ → Finset (M × W)
  | 0 => start
  | n + 1 => fixedPointF E school_pref student_pref quota (iterateFrom E school_pref student_pref quota start n)

theorem iterateFrom_stabilizes
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_M : ∀ m, IsLinearPref (school_pref m))
    (h_linear_W : ∀ w, IsLinearPref (student_pref w))
    (start : Finset (M × W))
    (h_subset : start ⊆ E)
    (h_increasing : start ⊆ fixedPointF E school_pref student_pref quota start) :
    ∃ n, iterateFrom E school_pref student_pref quota start n =
         iterateFrom E school_pref student_pref quota start (n + 1) := by
  have h_monotone : Monotone (fixedPointF E school_pref student_pref quota) := by
    apply_rules [fixedPointF_monotone]

  -- Since `start ⊆ fixedPointF start`, the sequence `iterateFrom` is increasing.
  have h_increasing' : ∀ n, iterateFrom E school_pref student_pref quota start n ⊆
                            iterateFrom E school_pref student_pref quota start (n + 1) := by
    exact fun n => Nat.recOn n h_increasing fun n ih => h_monotone ih

  -- All iterates are subsets of E
  have h_bounded : ∀ n, iterateFrom E school_pref student_pref quota start n ⊆ E := by
    intro n
    induction n with
    | zero =>
        unfold iterateFrom
        exact h_subset
    | succ n ih =>
        unfold iterateFrom
        exact fixedPointF_subset_E E school_pref student_pref quota _

  -- Since `E` is finite, an increasing sequence of subsets must stabilize.
  have h_finite : Set.Finite (Set.range (iterateFrom E school_pref student_pref quota start)) := by
    have h_powerset_finite : (E.powerset : Set (Finset (M × W))).Finite := Set.toFinite _
    apply Set.Finite.subset h_powerset_finite
    intro S hS
    obtain ⟨n, rfl⟩ := hS
    simp only [Finset.mem_coe, Finset.mem_powerset]
    exact h_bounded n

  by_contra h_no_stabilize
  exact h_finite.not_infinite <| Set.infinite_range_of_injective (
    StrictMono.injective <| strictMono_nat_of_lt_succ fun n =>
      lt_of_le_of_ne (h_increasing' n) fun h => h_no_stabilize ⟨n, h⟩)
def limitFrom
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (start : Finset (M × W)) : Finset (M × W) :=
  if h : ∃ n, iterateFrom E school_pref student_pref quota start n = iterateFrom E school_pref student_pref quota start (n + 1)
  then iterateFrom E school_pref student_pref quota start (Classical.choose h)
  else ∅

lemma limitFrom_is_fixedPoint
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_M : ∀ m, IsLinearPref (school_pref m))
    (h_linear_W : ∀ w, IsLinearPref (student_pref w))
    (start : Finset (M × W))
    (h_subset : start ⊆ E)
    (h_increasing : start ⊆ fixedPointF E school_pref student_pref quota start) :
    fixedPointF E school_pref student_pref quota (limitFrom E school_pref student_pref quota start) =
    limitFrom E school_pref student_pref quota start := by
      unfold limitFrom;
      split_ifs with h;
      · convert Classical.choose_spec h |> Eq.symm using 1;
      · exact False.elim ( h ( by exact? ) )

def leastFixedPoint
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M) : Finset (M × W) :=
  limitFrom E school_pref student_pref quota ∅

lemma leastFixedPoint_subset_of_fixedPoint
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_M : ∀ m, IsLinearPref (school_pref m))
    (h_linear_W : ∀ w, IsLinearPref (student_pref w))
    (S : Finset (M × W))
    (h_fixed : fixedPointF E school_pref student_pref quota S = S) :
    leastFixedPoint E school_pref student_pref quota ⊆ S := by
      -- Since `fixedPointF` is monotone, if `leastFixedPoint E school_pref student_pref quota` is a fixed point, then `leastFixedPoint E school_pref student_pref quota ⊆ S`.
      have h_monotone : Monotone (fixedPointF E school_pref student_pref quota) := by
        exact fixedPointF_monotone E school_pref student_pref quota h_linear_M h_linear_W;
      -- By definition of `leastFixedPoint`, we know that `leastFixedPoint E school_pref student_pref quota` is the least fixed point of `fixedPointF`.
      have h_least_fixed_point : ∀ T, fixedPointF E school_pref student_pref quota T = T → leastFixedPoint E school_pref student_pref quota ⊆ T := by
        intro T hT;
        apply Classical.byContradiction
        intro h_contra;
        -- Since `leastFixedPoint E school_pref student_pref quota` is not a subset of `T`, there exists some `n` such that `iterateFrom E school_pref student_pref quota ∅ n` is not a subset of `T`.
        obtain ⟨n, hn⟩ : ∃ n, iterateFrom E school_pref student_pref quota ∅ n ⊆ T ∧ ¬(iterateFrom E school_pref student_pref quota ∅ (n + 1) ⊆ T) := by
          have h_exists_n : ∃ n, ¬(iterateFrom E school_pref student_pref quota ∅ n ⊆ T) := by
            contrapose! h_contra;
            unfold leastFixedPoint;
            unfold limitFrom; aesop;
          obtain ⟨ n, hn ⟩ := Nat.findX h_exists_n;
          rcases n <;> simp_all +decide [ Classical.not_not ];
          · exact False.elim ( hn ( Finset.empty_subset _ ) );
          · exact ⟨ _, hn.2 _ ( Nat.lt_succ_self _ ), hn.1 ⟩;
        exact hn.2 ( by simpa [ hT ] using h_monotone hn.1 );
      exact h_least_fixed_point S h_fixed

theorem iterateFrom_decreasing_stabilizes
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_M : ∀ m, IsLinearPref (school_pref m))
    (h_linear_W : ∀ w, IsLinearPref (student_pref w))
    (start : Finset (M × W))
    (h_decreasing : fixedPointF E school_pref student_pref quota start ⊆ start) :
    ∃ n, iterateFrom E school_pref student_pref quota start n =
         iterateFrom E school_pref student_pref quota start (n + 1) := by
  have h_decreasing' : ∀ n, iterateFrom E school_pref student_pref quota start (n + 1) ⊆
                            iterateFrom E school_pref student_pref quota start n := by
    intro n
    induction n with
    | zero =>
        unfold iterateFrom
        exact h_decreasing
    | succ n ih =>
        unfold iterateFrom
        exact fixedPointF_monotone E school_pref student_pref quota h_linear_M h_linear_W ih

-- All iterates are subsets of start
  have h_bounded : ∀ n, iterateFrom E school_pref student_pref quota start n ⊆ start := by
    intro n
    induction n with
    | zero =>
        unfold iterateFrom
        exact Finset.Subset.refl start
    | succ n ih =>
        exact (h_decreasing' n).trans ih

  -- Range is finite (subset of powerset of start)
  have h_finite : Set.Finite (Set.range (iterateFrom E school_pref student_pref quota start)) := by
    have h_powerset_finite : (start.powerset : Set (Finset (M × W))).Finite := Set.toFinite _
    apply Set.Finite.subset h_powerset_finite
    intro S hS
    obtain ⟨n, rfl⟩ := hS
    simp only [Finset.mem_coe, Finset.mem_powerset]
    exact h_bounded n

  by_contra h_no_stabilize
  push_neg at h_no_stabilize

-- Strict decreasing → injective
  have h_strict : StrictAnti (fun n => (iterateFrom E school_pref student_pref quota start n).card) := by
    apply strictAnti_nat_of_succ_lt
    intro n
    apply Finset.card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr ⟨h_decreasing' n, (h_no_stabilize n).symm⟩

  -- This implies iterateFrom itself is injective
  have h_inj : Function.Injective (iterateFrom E school_pref student_pref quota start) := by
    intro m n hmn
    by_contra h_ne
    cases Nat.lt_or_gt_of_ne h_ne with
    | inl h_lt =>
        have : (iterateFrom E school_pref student_pref quota start m).card >
               (iterateFrom E school_pref student_pref quota start n).card :=
          h_strict h_lt
        rw [hmn] at this
        exact Nat.lt_irrefl _ this
    | inr h_gt =>
        have : (iterateFrom E school_pref student_pref quota start n).card >
               (iterateFrom E school_pref student_pref quota start m).card :=
          h_strict h_gt
        rw [hmn] at this
        exact Nat.lt_irrefl _ this

  exact h_finite.not_infinite (Set.infinite_range_of_injective h_inj)





lemma stableMatching_eq_choiceM_of_stablePair
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S S_M S_W : Finset (M × W))
    (h_pair : IsStablePair E school_pref student_pref quota S_M S_W)
    (h_eq : S = S_M ∩ S_W) :
    S = choiceM_all school_pref quota S_M := by
      exact h_eq.trans h_pair.2.1.symm

lemma leastFixedPoint_is_fixedPoint
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w)) :
    fixedPointF E school_pref student_pref quota (leastFixedPoint E school_pref student_pref quota) =
    leastFixedPoint E school_pref student_pref quota := by
      convert limitFrom_is_fixedPoint E school_pref student_pref quota h_linear_m h_linear_w ∅ (Finset.empty_subset _) (Finset.empty_subset _) using 1



/--*************************************
 *                                     *
 *  Конец вспомогательных лемм         *
 *                                     *
 *************************************-/



theorem stable_matchings_same_size
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w)) :
    ∀ S₁ S₂, IsStableMatching E school_pref student_pref quota S₁ →
             IsStableMatching E school_pref student_pref quota S₂ →
             S₁.card = S₂.card := by
  intro S₁ S₂ h₁ h₂
  obtain ⟨S_M1, S_W1, h_pair1, rfl⟩ := h₁
  obtain ⟨S_M2, S_W2, h_pair2, rfl⟩ := h₂
  have h_card_eq : (choiceM_all school_pref quota S_M1).card = (choiceM_all school_pref quota S_M2).card := by
    have h_card_eq : (choiceM_all school_pref quota (leastFixedPoint E school_pref student_pref quota)).card = (choiceM_all school_pref quota S_M1).card ∧ (choiceM_all school_pref quota (leastFixedPoint E school_pref student_pref quota)).card = (choiceM_all school_pref quota S_M2).card := by
      apply And.intro;
      · apply size_eq_of_subset_fixedPoint;
        exact h_linear_m;
        exact h_linear_w;
        exact?;
        · exact?;
        · apply leastFixedPoint_subset_of_fixedPoint E school_pref student_pref quota h_linear_m h_linear_w S_M1 (stablePair_implies_fixedPoint E school_pref student_pref quota S_M1 S_W1 h_pair1);
      · apply size_eq_of_subset_fixedPoint;
        exact h_linear_m;
        exact h_linear_w;
        exact?;
        · exact?;
        · apply leastFixedPoint_subset_of_fixedPoint;
          · assumption;
          · assumption;
          · exact?;
    exact h_card_eq.1.symm.trans h_card_eq.2;
  rw [ ← h_pair1.2.1, ← h_pair2.2.1, h_card_eq ]

/-- Join of two stable matchings is stable -/
theorem stable_matchings_closed_under_join
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w)) :
    ∀ S₁ S₂, IsStableMatching E school_pref student_pref quota S₁ →
             IsStableMatching E school_pref student_pref quota S₂ →
             IsStableMatching E school_pref student_pref quota
               (matchingJoin school_pref quota S₁ S₂) := by
  sorry

/-- Meet of two stable matchings is stable -/
theorem stable_matchings_closed_under_meet
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w)) :
    ∀ S₁ S₂, IsStableMatching E school_pref student_pref quota S₁ →
             IsStableMatching E school_pref student_pref quota S₂ →
             IsStableMatching E school_pref student_pref quota
               (matchingMeet student_pref S₁ S₂) := by
  have h_polarity : ∀ S₁ S₂ : Finset (M × W), IsStableMatching E school_pref student_pref quota S₁ → IsStableMatching E school_pref student_pref quota S₂ → matchingJoin school_pref quota S₁ S₂ = matchingMeet student_pref S₁ S₂ := by
    apply fun S₁ S₂ a a_1 => polarity_property E school_pref student_pref quota h_linear_m h_linear_w S₁ S₂ a a_1;
  exact fun S₁ S₂ h₁ h₂ => h_polarity S₁ S₂ h₁ h₂ ▸ stable_matchings_closed_under_join E school_pref student_pref quota h_linear_m h_linear_w S₁ S₂ h₁ h₂

/-- Stable matchings form a lattice -/
theorem stable_matchings_form_lattice
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (h_nonempty : ∃ S, IsStableMatching E school_pref student_pref quota S) :
    ∃ (Lattice : Set (Finset (M × W))),
      (∀ S ∈ Lattice, IsStableMatching E school_pref student_pref quota S) ∧
      (∀ S, IsStableMatching E school_pref student_pref quota S → S ∈ Lattice) ∧
      (∀ S₁ ∈ Lattice, ∀ S₂ ∈ Lattice, matchingJoin school_pref quota S₁ S₂ ∈ Lattice) ∧
      (∀ S₁ ∈ Lattice, ∀ S₂ ∈ Lattice, matchingMeet student_pref S₁ S₂ ∈ Lattice) := by
  admit

/-! ### Polarity property -/



/-! ### Rural Hospital Theorem (Roth 1986) -/

/-- A school is under-subscribed in matching S -/
def isUnderSubscribed (quota : Quotas M) (S : Finset (M × W)) (m : M) : Prop :=
  (S.filter (fun e => e.1 = m)).card < quota m

/-- Students matched to school m in S -/
def matchedToSchool (S : Finset (M × W)) (m : M) : Finset W :=
  (S.filter (fun e => e.1 = m)).image (·.2)

/-- Rural Hospital Theorem: under-subscribed schools get same students in all stable matchings -/
theorem rural_hospital_theorem
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (S₁ S₂ : Finset (M × W))
    (h₁ : IsStableMatching E school_pref student_pref quota S₁)
    (h₂ : IsStableMatching E school_pref student_pref quota S₂)
    (m : M)
    (h_under : isUnderSubscribed quota S₁ m) :
    matchedToSchool S₁ m = matchedToSchool S₂ m := by
  admit


/-! ### School-optimal and student-optimal matchings -/

/-- There exists a school-optimal stable matching -/
theorem school_optimal_exists
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w)) :
    ∃ S_opt, IsStableMatching E school_pref student_pref quota S_opt ∧
             ∀ S, IsStableMatching E school_pref student_pref quota S →
                  ∀ m : M, ∀ w ∈ matchedToSchool S_opt m,
                    ∀ w' ∈ matchedToSchool S m,
                      w = w' ∨ school_pref m w w' := by
  admit

/-- There exists a student-optimal stable matching -/
theorem student_optimal_exists
    (E : Finset (M × W))
    (school_pref : M → LinearPref W)
    (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w)) :
    ∃ S_opt, IsStableMatching E school_pref student_pref quota S_opt ∧
             ∀ S, IsStableMatching E school_pref student_pref quota S →
                  ∀ w : W, ∀ m ∈ (S_opt.filter (fun e => e.2 = w)).image (·.1),
                    ∀ m' ∈ (S.filter (fun e => e.2 = w)).image (·.1),
                      m = m' ∨ student_pref w m m' := by
  admit
