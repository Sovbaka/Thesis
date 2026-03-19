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

variable {M W : Type*} [DecidableEq M] [DecidableEq W] [Fintype M] [Fintype W]

/-! ### Basic type aliases -/

abbrev Quotas (M : Type*) := M → ℕ
abbrev LinearPref (α : Type*) := α → α → Prop

def IsLinearPref {α : Type*} (r : α → α → Prop) : Prop :=
  (∀ x, ¬r x x) ∧
  (∀ x y z, r x y → r y z → r x z) ∧
  (∀ x y, x ≠ y → r x y ∨ r y x)

/-! ### Top-k and top-1 selection -/

def countBetter (pref_m : LinearPref W) (S : Finset W) (w : W) : ℕ :=
  (S.filter (fun w' => pref_m w' w)).card

def topK (pref_m : LinearPref W) (k : ℕ) (S : Finset W) : Finset W :=
  S.filter (fun w => countBetter pref_m S w < k)

def topOne (pref_w : LinearPref M) (S : Finset M) : Finset M :=
  S.filter (fun m => ∀ m' ∈ S, m = m' ∨ pref_w m m')

/-! ### Choice functions -/

def choiceM_classical
    (school_pref : M → LinearPref W) (quota : Quotas M)
    (S : Finset (M × W)) (m : M) : Finset (M × W) :=
  let students_for_m := S.filter (fun e => e.1 = m)
  let student_set := students_for_m.image (·.2)
  let chosen_students := topK (school_pref m) (quota m) student_set
  students_for_m.filter (fun e => e.2 ∈ chosen_students)

def choiceW_classical
    (student_pref : W → LinearPref M)
    (S : Finset (M × W)) (w : W) : Finset (M × W) :=
  let schools_for_w := S.filter (fun e => e.2 = w)
  let school_set := schools_for_w.image (·.1)
  let chosen_schools := topOne (student_pref w) school_set
  schools_for_w.filter (fun e => e.1 ∈ chosen_schools)

def choiceM_all
    (school_pref : M → LinearPref W) (quota : Quotas M)
    (S : Finset (M × W)) : Finset (M × W) :=
  Finset.univ.biUnion (fun m => choiceM_classical school_pref quota S m)

def choiceW_all
    (student_pref : W → LinearPref M)
    (S : Finset (M × W)) : Finset (M × W) :=
  Finset.univ.biUnion (fun w => choiceW_classical student_pref S w)

/-! ### Matching helpers -/

def matchedToSchool (S : Finset (M × W)) (m : M) : Finset W :=
  (S.filter (fun e => e.1 = m)).image (·.2)

def matchedToStudent (S : Finset (M × W)) (w : W) : Finset M :=
  (S.filter (fun e => e.2 = w)).image (·.1)

/-! ### Fleiner stability -/

def IsStablePair
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S_M S_W : Finset (M × W)) : Prop :=
  S_M ∪ S_W = E ∧
  choiceM_all school_pref quota S_M = S_M ∩ S_W ∧
  choiceW_all student_pref S_W = S_M ∩ S_W

def IsStableMatching
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S : Finset (M × W)) : Prop :=
  ∃ S_M S_W, IsStablePair E school_pref student_pref quota S_M S_W ∧ S = S_M ∩ S_W

/-! ### Key lemmas about topK -/

lemma countBetter_strict_mono (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m)
    (S : Finset W) (x : W) (hx : x ∈ S) (y : W) (hy : y ∈ S) (hxy : pref_m x y) :
    countBetter pref_m S x < countBetter pref_m S y := by
  unfold countBetter
  have hBx_subset_By : S.filter (fun w' => pref_m w' x) ⊆ S.filter (fun w' => pref_m w' y) := by
    intro w' hw'; simp only [Finset.mem_filter] at hw' ⊢
    exact ⟨hw'.1, h_lin.2.1 w' x y hw'.2 hxy⟩
  apply Finset.card_lt_card
  simp only [Finset.ssubset_iff_subset_ne]
  refine ⟨hBx_subset_By, fun h_eq => ?_⟩
  have hx_in_y : x ∈ S.filter (fun w' => pref_m w' y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
  have hx_not_in_x : x ∉ S.filter (fun w' => pref_m w' x) :=
    Finset.mem_filter.not.mpr (fun ⟨_, hxx⟩ => h_lin.1 x hxx)
  rw [h_eq] at hx_not_in_x; contradiction

lemma countBetter_inj (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m)
    (S : Finset W) (x : W) (hx : x ∈ S) (y : W) (hy : y ∈ S) :
    countBetter pref_m S x = countBetter pref_m S y → x = y := by
  intro h_eq; by_contra hxy
  cases h_lin.2.2 x y hxy with
  | inl hxy' => exact absurd h_eq (Nat.ne_of_lt (countBetter_strict_mono pref_m h_lin S x hx y hy hxy'))
  | inr hyx  => exact absurd h_eq (Nat.ne_of_gt (countBetter_strict_mono pref_m h_lin S y hy x hx hyx))

lemma countBetter_image (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m) (S : Finset W) :
    S.image (countBetter pref_m S) = Finset.range S.card := by
  refine' Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun x hx => _) _
  · refine' Finset.mem_range.mpr (lt_of_lt_of_le (Finset.card_lt_card (Finset.filter_ssubset.mpr _)) (by simp +decide))
    exact ⟨x, hx, h_lin.1 x⟩
  · rw [Finset.card_image_of_injOn]; · simp +decide
    · exact fun x hx y hy hxy => countBetter_inj pref_m h_lin S x hx y hy hxy

lemma topK_card (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m) (k : ℕ) (S : Finset W) :
    (topK pref_m k S).card = min k S.card := by
  have h1 : S.image (countBetter pref_m S) = Finset.range S.card := countBetter_image pref_m h_lin S
  have h2 : (topK pref_m k S).image (countBetter pref_m S) = Finset.range (min k S.card) := by
    ext; simp [topK]
    constructor <;> intro h
    · obtain ⟨a, ⟨ha₁, ha₂⟩, rfl⟩ := h
      exact ⟨ha₂, by linarith [Finset.mem_range.mp (h1 ▸ Finset.mem_image_of_mem _ ha₁)]⟩
    · replace h1 := Finset.ext_iff.mp h1 ‹_›; aesop
  rw [← Finset.card_range (Min.min k S.card), ← h2, Finset.card_image_of_injOn]
  exact fun x hx y hy hxy => countBetter_inj pref_m h_lin S x (Finset.mem_filter.mp hx |>.1) y (Finset.mem_filter.mp hy |>.1) hxy

theorem topK_increasing (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m) (k : ℕ) :
    ∀ S T : Finset W, S ⊆ T → (topK pref_m k S).card ≤ (topK pref_m k T).card := by
  intros S T hST
  have h_card : min k S.card ≤ min k T.card := min_le_min le_rfl (Finset.card_le_card hST)
  calc (topK pref_m k S).card = min k S.card := topK_card pref_m h_lin k S
    _ ≤ min k T.card := h_card
    _ = (topK pref_m k T).card := (topK_card pref_m h_lin k T).symm

lemma topOne_card_eq_one (pref_w : LinearPref M) (h_lin : IsLinearPref pref_w)
    (S : Finset M) (hS : S.Nonempty) : (topOne pref_w S).card = 1 := by
  rcases h_lin with ⟨h₁, h₂, h₃⟩
  obtain ⟨m, hm⟩ : ∃ m ∈ S, ∀ n ∈ S, n = m ∨ pref_w m n := by
    obtain ⟨m, hm⟩ := Finset.exists_max_image S (fun m => (Finset.filter (fun n => pref_w m n) S).card) hS
    refine' ⟨m, hm.1, fun n hn => _⟩
    contrapose! hm
    refine' fun hm' => ⟨n, hn, Finset.card_lt_card _⟩
    simp_all +decide [Finset.ssubset_def, Finset.subset_iff]; grind
  refine' Finset.card_eq_one.mpr ⟨m, _⟩
  ext n; simp [topOne, hm]; grind

theorem topK_accepted_beats_rejected
    (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m)
    (k : ℕ) (A : Finset W) (v : W) (hv_A : v ∈ A)
    (hv_rej : v ∉ topK pref_m k A)
    (u : W) (hu_acc : u ∈ topK pref_m k A) :
    pref_m u v := by
  simp only [topK, Finset.mem_filter, not_and, not_lt] at hv_rej hu_acc
  have hv_ge := hv_rej hv_A
  have hu_lt := hu_acc.2
  have h_ne : u ≠ v := by intro heq; subst heq; omega
  rcases h_lin.2.2 u v h_ne with h | h
  · exact h
  · have := countBetter_strict_mono pref_m h_lin A v hv_A u hu_acc.1 h; omega

lemma topK_substitutability' (pref_m : LinearPref W) (h_lin : IsLinearPref pref_m)
    (k : ℕ) (T' T : Finset W) (hT'T : T' ⊆ T) (w : W) (hw_T' : w ∈ T')
    (hw_topK_T : w ∈ topK pref_m k T) : w ∈ topK pref_m k T' := by
  simp only [topK, Finset.mem_filter] at hw_topK_T ⊢
  exact ⟨hw_T', lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset_filter _ hT'T)) hw_topK_T.2⟩

/-! ### Choice function properties -/

theorem choiceM_classical_subset
    (school_pref : M → LinearPref W) (quota : Quotas M) (S : Finset (M × W)) :
    choiceM_all school_pref quota S ⊆ S := by
  unfold choiceM_all choiceM_classical
  intro e he
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
  obtain ⟨m, hm⟩ := he
  simp only [Finset.mem_filter] at hm; exact hm.1.1

theorem choiceW_classical_subset
    (student_pref : W → LinearPref M) (S : Finset (M × W)) :
    choiceW_all student_pref S ⊆ S := by
  unfold choiceW_all choiceW_classical
  intro e he
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
  obtain ⟨w, hw⟩ := he
  simp only [Finset.mem_filter] at hw; exact hw.1.1

lemma choiceM_is_matching
    (school_pref : M → LinearPref W) (quota : Quotas M)
    (h_linear : ∀ m, IsLinearPref (school_pref m))
    (S : Finset (M × W)) :
    ∀ m, ((choiceM_all school_pref quota S).filter (fun e => e.1 = m)).card ≤ quota m := by
  intros m
  have h_card : (Finset.filter (fun e => e.1 = m) (choiceM_all school_pref quota S)).card =
      (topK (school_pref m) (quota m) (S.filter (fun e => e.1 = m) |>.image (fun e => e.2))).card := by
    unfold choiceM_all
    refine' Finset.card_bij (fun e he => e.2) _ _ _ <;> simp +decide [choiceM_classical]
    · aesop
    · grind
    · unfold topK; aesop
  rw [h_card, topK_card _ (h_linear m)]
  exact min_le_left _ _

lemma choiceW_is_matching
    (student_pref : W → LinearPref M)
    (h_linear : ∀ w, IsLinearPref (student_pref w))
    (S : Finset (M × W)) :
    ∀ w, ((choiceW_all student_pref S).filter (fun e => e.2 = w)).card ≤ 1 := by
  intro w
  unfold choiceW_all
  refine' Finset.card_le_one.mpr _
  unfold choiceW_classical; simp +decide
  intro a b ha hb hb' c d hc hd hd'; subst_vars; simp_all +decide [topOne]
  cases hb c hc <;> cases hd a ha <;> have := h_linear d <;> cases this <;> tauto





/-! ### Classical stability definitions -/

def IsIndividuallyRationalM (quota : Quotas M) (S : Finset (M × W)) (m : M) : Prop :=
  (S.filter (fun e => e.1 = m)).card ≤ quota m

def IsIndividuallyRationalW (S : Finset (M × W)) (w : W) : Prop :=
  (S.filter (fun e => e.2 = w)).card ≤ 1

def IsIndividuallyRational (quota : Quotas M) (S : Finset (M × W)) : Prop :=
  (∀ m, IsIndividuallyRationalM quota S m) ∧ (∀ w, IsIndividuallyRationalW S w)

def SchoolWantsStudent
    (school_pref : M → LinearPref W) (quota : Quotas M)
    (S : Finset (M × W)) (m : M) (w : W) : Prop :=
  (matchedToSchool S m).card < quota m ∨
  ∃ w' ∈ matchedToSchool S m, school_pref m w w'

def StudentWantsSchool
    (student_pref : W → LinearPref M)
    (S : Finset (M × W)) (w : W) (m : M) : Prop :=
  matchedToStudent S w = ∅ ∨
  ∃ m' ∈ matchedToStudent S w, student_pref w m m'

def IsBlockingPair
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M) (S : Finset (M × W)) (m : M) (w : W) : Prop :=
  (m, w) ∉ S ∧
  SchoolWantsStudent school_pref quota S m w ∧
  StudentWantsSchool student_pref S w m

def IsClassicallyStable
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M) (S : Finset (M × W)) : Prop :=
  S ⊆ E ∧
  IsIndividuallyRational quota S ∧
  ¬ ∃ m w, (m, w) ∈ E ∧ IsBlockingPair school_pref student_pref quota S m w

/-! ### Main equivalence theorem -/



/-
Definitions of student-rejected and school-rejected pairs, and the construction of S_W and S_M for the Classical -> Fleiner direction. Using `open Classical` to ensure decidability of predicates.
-/


variable {M W : Type*} [DecidableEq M] [DecidableEq W] [Fintype M] [Fintype W]

def is_student_rejected
    (student_pref : W → LinearPref M)
    (S : Finset (M × W)) (m : M) (w : W) : Prop :=
  ∃ m' ∈ matchedToStudent S w, student_pref w m' m

def is_school_rejected
    (school_pref : M → LinearPref W) (quota : Quotas M)
    (S : Finset (M × W)) (m : M) (w : W) : Prop :=
  (matchedToSchool S m).card = quota m ∧
  ∀ w' ∈ matchedToSchool S m, school_pref m w' w

def S_W_constructed
    (E : Finset (M × W))
    (student_pref : W → LinearPref M)
    (S : Finset (M × W)) : Finset (M × W) :=
  S ∪ (E \ S).filter (fun e => is_student_rejected student_pref S e.1 e.2)

def S_M_constructed
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S : Finset (M × W)) : Finset (M × W) :=
  S ∪ (E \ S).filter (fun e =>
    is_school_rejected school_pref quota S e.1 e.2 ∧
    ¬ is_student_rejected student_pref S e.1 e.2)

/-
If a matching is Fleiner-stable, it is individually rational.
-/
lemma fleiner_implies_ir
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (S : Finset (M × W))
    (h_stable : IsStableMatching E school_pref student_pref quota S) :
    IsIndividuallyRational quota S := by
      obtain ⟨ S_M, S_W, hS_M_S_W, rfl ⟩ := h_stable;
      obtain ⟨ hS_M, hS_W ⟩ := hS_M_S_W;
      refine' ⟨ fun m => _, fun w => _ ⟩;
      · have h_card : ((choiceM_all school_pref quota S_M).filter (fun e => e.1 = m)).card ≤ quota m := by
          apply_rules [ choiceM_is_matching ];
        aesop;
      · have := choiceW_is_matching student_pref h_linear_w S_W w;
        aesop

/-
If a matching is Fleiner-stable, it has no blocking pairs.
-/


/-
If a matching is Fleiner-stable, it has no blocking pairs.
-/
noncomputable section AristotleLemmas

/-
If a school $m$ rejects a student $w$ from the set of available contracts $S_M$ (meaning $(m, w) \in S_M$ but not in the choice set $S$), then $m$ does not want $w$ given the choice set $S$ (meaning $m$ is full with better students).
-/
open Classical

variable {M W : Type*} [DecidableEq M] [DecidableEq W] [Fintype M] [Fintype W]

lemma school_rejection_implies_not_wants
    (school_pref : M → LinearPref W) (quota : Quotas M)
    (h_linear : ∀ m, IsLinearPref (school_pref m))
    (S_M : Finset (M × W))
    (S : Finset (M × W))
    (h_S : S = choiceM_all school_pref quota S_M)
    (m : M) (w : W)
    (h_in : (m, w) ∈ S_M)
    (h_rej : (m, w) ∉ S) :
    ¬ SchoolWantsStudent school_pref quota S m w := by
      intro h;
      obtain ⟨K, hK⟩ : ∃ K : Finset W, K = (S_M.filter (fun e => e.1 = m)).image (·.2) ∧ w ∈ K ∧ w∉ (topK (school_pref m) (quota m) K) := by
        contrapose! h_rej;
        simp_all +decide [ choiceM_all ];
        unfold choiceM_classical; aesop;
      -- Therefore, `matchedToSchool S m` has size `quota(m)` and contains only students better than $w$.
      have h_match_size : (matchedToSchool S m).card = quota m ∧ ∀ u ∈ matchedToSchool S m, school_pref m u w := by
        have h_match_size : (matchedToSchool S m) = (topK (school_pref m) (quota m) K).image (fun w => w) := by
          simp +decide [ matchedToSchool, h_S, choiceM_all ];
          simp +decide [ Finset.ext_iff, choiceM_classical ];
          simp +decide [ hK.1, topK ];
        simp +zetaDelta at *;
        rw [ h_match_size, topK_card ];
        · refine' ⟨ min_eq_left _, _ ⟩;
          · contrapose! hK;
            intro hK' hwK; rw [ topK ] ; simp +decide [ hwK, hK ] ;
            exact lt_of_le_of_lt ( Finset.card_le_card ( Finset.filter_subset _ _ ) ) ( by simpa using hK );
          · intro u hu; exact (by
            apply topK_accepted_beats_rejected (school_pref m) (h_linear m) (quota m) K w hK.right.left hK.right.right u hu);
        · exact h_linear m;
      cases h <;> simp_all +singlePass [ SchoolWantsStudent ];
      obtain ⟨ u, hu, hu' ⟩ := ‹_›; have := h_match_size.2 u hu; have := h_linear m; cases this; tauto;

/-
If a student $w$ rejects a school $m$ from the set of available contracts $S_W$, then $w$ does not want $m$ given the choice set $S$ (meaning $w$ has a better school).
-/
open Classical

variable {M W : Type*} [DecidableEq M] [DecidableEq W] [Fintype M] [Fintype W]

lemma student_rejection_implies_not_wants
    (student_pref : W → LinearPref M)
    (h_linear : ∀ w, IsLinearPref (student_pref w))
    (S_W : Finset (M × W))
    (S : Finset (M × W))
    (h_S : S = choiceW_all student_pref S_W)
    (m : M) (w : W)
    (h_in : (m, w) ∈ S_W)
    (h_rej : (m, w) ∉ S) :
    ¬ StudentWantsSchool student_pref S w m := by
      contrapose! h_rej;
      rw [ h_S ] at *; simp_all +decide [ StudentWantsSchool, choiceW_all ] ;
      simp_all +decide [ Finset.ext_iff, matchedToStudent ];
      obtain h | ⟨ m', ⟨ a, ha ⟩, h ⟩ := h_rej <;> simp_all +decide [ Finset.ext_iff, choiceW_classical ];
      · -- Since $w$ is unmatched in $S$, the set of schools available to $w$ in $S_W$ is nonempty.
        have h_nonempty : (Finset.image (fun x => x.1) ({e ∈ S_W | e.2 = w})).Nonempty := by
          exact ⟨ m, Finset.mem_image.mpr ⟨ ( m, w ), Finset.mem_filter.mpr ⟨ h_in, rfl ⟩, rfl ⟩ ⟩;
        obtain ⟨ m', hm' ⟩ := Finset.card_pos.mp ( show 0 < Finset.card ( topOne ( student_pref w ) ( Finset.image ( fun x => x.1 ) ( { e ∈ S_W | e.2 = w } ) ) ) from by rw [ topOne_card_eq_one _ ( h_linear w ) _ h_nonempty ] ; simp +decide ) ; simp_all +decide [ topOne ] ;
        grind +ring;
      · simp_all +decide [ topOne ];
        cases ha.2.2 m h_in <;> simp_all +decide [ IsLinearPref ];
        exact absurd ( h_linear a |>.2.1 _ _ _ ‹_› ‹_› ) ( h_linear a |>.1 _ )

end AristotleLemmas

lemma fleiner_implies_no_blocking_pair
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (S : Finset (M × W))
    (h_stable : IsStableMatching E school_pref student_pref quota S) :
    ¬ ∃ m w, (m, w) ∈ E ∧ IsBlockingPair school_pref student_pref quota S m w := by
      obtain ⟨ S_M, S_W, hS_M, hS_W ⟩ := h_stable;
      obtain ⟨ hS_M_union, hS_M_choiceM, hS_W_choiceW ⟩ := hS_M;
      rintro ⟨ m, w, hmx, hm ⟩;
      cases Finset.mem_union.mp ( hS_M_union.symm ▸ hmx ) <;> simp_all +decide [ IsBlockingPair ];
      · have := school_rejection_implies_not_wants school_pref quota h_linear_m S_M ( S_M ∩ S_W ) ?_ m w ?_ ?_ <;> simp_all +decide [ SchoolWantsStudent ];
      · have := student_rejection_implies_not_wants student_pref h_linear_w S_W ( S_M ∩ S_W ) ?_ m w ?_ ?_ <;> simp_all +decide [ StudentWantsSchool ]






/-
The intersection of the constructed S_M and S_W is exactly S.
-/
lemma S_M_inter_S_W_eq_S
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (S : Finset (M × W))
    (hS : S ⊆ E) :
    S_M_constructed E school_pref student_pref quota S ∩ S_W_constructed E student_pref S = S := by
      unfold S_M_constructed S_W_constructed;
      grind +ring

/-
If a matching is classically stable, the constructed S_M and S_W cover E (Property F1).
-/
lemma classical_implies_F1
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (S : Finset (M × W))
    (h_stable : IsClassicallyStable E school_pref student_pref quota S) :
    S_M_constructed E school_pref student_pref quota S ∪ S_W_constructed E student_pref S = E := by
      apply Finset.ext
      intro e
      simp [S_M_constructed, S_W_constructed];
      by_cases he : e ∈ S <;> simp +decide [ he ];
      · exact h_stable.1 he;
      · by_cases he' : e ∈ E <;> simp_all +decide [ IsClassicallyStable ];
        contrapose! h_stable; simp_all +decide [ IsBlockingPair ] ;
        refine' fun h1 h2 => ⟨ e.1, e.2, he', he, _, _ ⟩ <;> simp_all +decide [ SchoolWantsStudent, StudentWantsSchool ];
        · refine' Classical.or_iff_not_imp_left.2 fun h => _;
          contrapose! h_stable; simp_all +decide [ is_school_rejected ] ;
          intro h3; specialize h2; have := h2.1 e.1; simp_all +decide [ matchedToSchool ] ;
          refine' h3 _ _;
          · refine' le_antisymm _ h;
            exact le_trans ( Finset.card_image_le ) ( by simpa using this );
          · intro w' hw'; specialize h_linear_m e.1; have := h_linear_m.2.2 e.2 w'; aesop;
        · by_cases h : matchedToStudent S e.2 = ∅ <;> simp_all +decide [ is_student_rejected ];
          obtain ⟨ m', hm' ⟩ := Finset.nonempty_iff_ne_empty.mpr h; use m'; simp_all +decide [ matchedToStudent ] ;
          have := h_linear_w e.2; exact this.2.2 _ _ ( by aesop ) |> Or.resolve_right <| by aesop;

/-
If a matching is classically stable, the constructed S_M satisfies C_M(S_M) = S (Property F2).
-/
lemma classical_implies_F2
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (S : Finset (M × W))
    (h_stable : IsClassicallyStable E school_pref student_pref quota S) :
    choiceM_all school_pref quota (S_M_constructed E school_pref student_pref quota S) = S := by
      refine' Finset.Subset.antisymm _ _;
      · intro e he
        rw [choiceM_all] at he
        obtain ⟨m, hm⟩ := Finset.mem_biUnion.mp he
        simp [choiceM_classical] at hm
        obtain ⟨hm₁, hm₂⟩ := hm;
        by_cases h : e ∈ S <;> simp_all +decide [ S_M_constructed ];
        obtain ⟨ hm₃, hm₄ ⟩ := hm₁.1.2.1;
        unfold topK at hm₂; simp_all +decide [ Finset.filter_image ] ;
        contrapose! hm₂; simp_all +decide [ matchedToSchool ] ;
        intro h; rw [ ← hm₃ ] ; refine' Finset.card_le_card _ ; intro w hw ; simp_all +decide [ Finset.mem_image ] ;
      · intro e he
        simp [choiceM_all];
        use e.fst; simp [choiceM_classical, he];
        unfold S_M_constructed;
        simp [he, topK];
        have h_count : countBetter (school_pref e.1) (Finset.image (fun x => x.2) (Finset.filter (fun x => x.1 = e.1) S)) e.2 < quota e.1 := by
          have h_count_better : (Finset.image (fun x => x.2) (Finset.filter (fun x => x.1 = e.1) S)).card ≤ quota e.1 := by
            have := h_stable.2.1.1 e.1;
            exact le_trans ( Finset.card_image_le ) this;
          refine' lt_of_lt_of_le ( Finset.card_lt_card ( Finset.filter_ssubset.mpr _ ) ) h_count_better;
          exact ⟨ e.2, Finset.mem_image.mpr ⟨ e, by aesop ⟩, by have := h_linear_m e.1; exact this.1 e.2 ⟩;
        refine' lt_of_le_of_lt _ h_count;
        refine' Finset.card_mono _;
        simp +decide [ Finset.subset_iff ];
        rintro x ( hx | hx ) hx' <;> simp_all +decide [ is_school_rejected, is_student_rejected ];
        contrapose! hx';
        have := hx.2.1.2 e.2 ( by
          exact Finset.mem_image_of_mem _ ( Finset.mem_filter.mpr ⟨ he, rfl ⟩ ) );
        exact fun h => h_linear_m e.1 |>.1 _ ( h_linear_m e.1 |>.2.1 _ _ _ this h )

/-
If a matching is classically stable, the constructed S_W satisfies C_W(S_W) = S (Property F3).
-/
lemma classical_implies_F3
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (S : Finset (M × W))
    (h_stable : IsClassicallyStable E school_pref student_pref quota S) :
    choiceW_all student_pref (S_W_constructed E student_pref S) = S := by
      apply Finset.ext;
      intro e
      simp [choiceW_all, S_W_constructed];
      unfold choiceW_classical;
      by_cases he : e ∈ S <;> simp_all +decide [ topOne ];
      · intro m' hm'
        by_cases hm'' : (m', e.2) ∈ S;
        · have := h_stable.2.1.2 e.2; simp_all +decide [ IsIndividuallyRationalW ] ;
          rw [ Finset.card_le_one_iff ] at this ; aesop;
        · have := h_stable.2.1.2 e.2; simp_all +decide [ IsIndividuallyRationalW ] ;
          cases this.eq_or_lt <;> simp_all +decide [ Finset.card_le_one ];
          · obtain ⟨ m'', hm'' ⟩ := hm'.2; simp_all +decide [ Finset.card_eq_one ] ;
            unfold matchedToStudent at hm''; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
            grind +ring;
          · exact False.elim ( ‹∀ a b, ( a, b ) ∈ S → ¬b = e.2› _ _ he rfl );
      · intro heE heRejected
        obtain ⟨m', hm', hm'_pref⟩ := heRejected
        use m';
        unfold matchedToStudent at hm';
        simp +zetaDelta at *;
        exact ⟨ Or.inl hm', by rintro rfl; exact absurd hm'_pref ( h_linear_w _ |>.1 _ ), by rintro h; exact absurd ( h_linear_w _ |>.2.1 _ _ _ h hm'_pref ) ( h_linear_w _ |>.1 _ ) ⟩


theorem classically_stable_iff_fleiner
    (E : Finset (M × W))
    (school_pref : M → LinearPref W) (student_pref : W → LinearPref M)
    (quota : Quotas M)
    (h_linear_m : ∀ m, IsLinearPref (school_pref m))
    (h_linear_w : ∀ w, IsLinearPref (student_pref w))
    (S : Finset (M × W)) :
    IsClassicallyStable E school_pref student_pref quota S ↔
    IsStableMatching E school_pref student_pref quota S := by
      constructor <;> intro h;
      · use S_M_constructed E school_pref student_pref quota S, S_W_constructed E student_pref S;
        refine' ⟨ ⟨ _, _, _ ⟩, _ ⟩;
        · apply classical_implies_F1 E school_pref student_pref quota h_linear_m h_linear_w S h;
        · rw [ S_M_inter_S_W_eq_S ];
          · apply classical_implies_F2 E school_pref student_pref quota h_linear_m h_linear_w S h;
          · exact h.1;
        · rw [ classical_implies_F3 E school_pref student_pref quota h_linear_m h_linear_w S h, S_M_inter_S_W_eq_S E school_pref student_pref quota S h.1 ];
        · exact Eq.symm ( S_M_inter_S_W_eq_S E school_pref student_pref quota S h.1 );
      · refine' ⟨ _, _, _ ⟩;
        · obtain ⟨ S_M, S_W, h₁, h₂ ⟩ := h;
          exact h₂ ▸ Finset.inter_subset_left.trans ( h₁.1 ▸ Finset.subset_union_left );
        · apply fleiner_implies_ir E school_pref student_pref quota h_linear_m h_linear_w S h;
        · apply fleiner_implies_no_blocking_pair E school_pref student_pref quota h_linear_m h_linear_w S h
