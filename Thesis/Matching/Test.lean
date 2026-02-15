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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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





-- Тогда:


/-- School choice is increasing per school -/
theorem choiceM_classical_increasing_per_school
    (school_pref : M → LinearPref W)
    (h_linear : ∀ m, IsLinearPref (school_pref m))
    (quota : Quotas M)
    (m : M) :
    ∀ S T : Finset (M × W), S ⊆ T →
      (choiceM_classical school_pref quota S m).card ≤
      (choiceM_classical school_pref quota T m).card := by
  intro S T hST
  unfold choiceM_classical
  sorry

theorem choiceM_classical_increasing
    (school_pref : M → LinearPref W)
    (h_linear : ∀ m, IsLinearPref (school_pref m))
    (quota : Quotas M) :
    ∀ S T : Finset (M × W), S ⊆ T →
      (choiceM_all school_pref quota S).card ≤
      (choiceM_all school_pref quota T).card := by
 intros S T hST
 have h_card_le : ∀ m : M, (choiceM_classical school_pref quota S m).card ≤ (choiceM_classical school_pref quota T m).card := by
   intro m;
   have h_card : (topK (school_pref m) (quota m) (S.filter (fun e => e.1 = m) |>.image (·.2))).card ≤ (topK (school_pref m) (quota m) (T.filter (fun e => e.1 = m) |>.image (·.2))).card := by
     apply_rules [ topK_increasing ];
     exact Finset.image_subset_image ( Finset.filter_subset_filter _ hST );
   convert h_card using 1;
   · refine' Finset.card_bij ( fun x hx => x.2 ) _ _ _ <;> simp +contextual [ choiceM_classical ];
     unfold topK; aesop;
   · refine' Finset.card_bij ( fun x hx => x.2 ) _ _ _ <;> simp +decide [ choiceM_classical ];
     · aesop;
     · unfold topK; aesop;
 convert Finset.sum_le_sum fun m _ => h_card_le m using 1;
 any_goals exact Finset.univ;
 · rw [ choiceM_all, Finset.card_biUnion ];
   intro m _ m' _ h; simp_all +decide [ Finset.disjoint_left, choiceM_classical ] ;
 · rw [ choiceM_all, Finset.card_biUnion ];
   intro m hm n hn hmn; simp_all +decide [ Finset.disjoint_left, choiceM_classical ] ;

theorem choiceW_classical_increasing
    (student_pref : W → LinearPref M)
    (h_linear : ∀ w, IsLinearPref (student_pref w)) :
    ∀ S T : Finset (M × W), S ⊆ T →
      (choiceW_all student_pref S).card ≤
      (choiceW_all student_pref T).card := by
-- Since choiceW_all is the union of choiceW_classical over all students, and each choiceW_classical is increasing, the union is also increasing.
have h_choiceW_all_increasing : ∀ S T : Finset (M × W), S ⊆ T → ∀ w : W, (choiceW_classical student_pref S w).card ≤ (choiceW_classical student_pref T w).card := by
  intro S T hST w;
  -- Since the schools_for_w in S is a subset of the schools_for_w in T, the schools_for_w in S is a subset of the schools_for_w in T. Therefore, the topOne of the schools_for_w in S is a subset of the topOne of the schools_for_w in T.
  have h_subset : (S.filter (fun e => e.2 = w)).image (·.1) ⊆ (T.filter (fun e => e.2 = w)).image (·.1) := by
    exact Finset.image_subset_image fun x hx => Finset.mem_filter.mpr ⟨ hST ( Finset.mem_filter.mp hx |>.1 ), Finset.mem_filter.mp hx |>.2 ⟩;
  convert topOne_increasing ( student_pref w ) ( h_linear w ) _ _ h_subset using 1;
  · refine' Finset.card_bij ( fun x hx => x.1 ) _ _ _ <;> simp +decide [ choiceW_classical ];
    · aesop;
    · unfold topOne; aesop;
  · unfold choiceW_classical;
    refine' Finset.card_bij ( fun x hx => x.1 ) _ _ _ <;> simp +decide;
    · aesop;
    · unfold topOne; aesop;
intro S T hST;
unfold choiceW_all;
refine' le_trans ( Finset.card_biUnion_le ) _;
refine' le_trans ( Finset.sum_le_sum fun w _ => h_choiceW_all_increasing S T hST w ) _;
rw [ Finset.card_biUnion ];
intro w hw w' hw' hww'; simp_all +decide [ Finset.disjoint_left ] ;
unfold choiceW_classical; aesop;
