import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Order.FixedPoints
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Defs.LinearOrder
import Init.Data.Nat.Basic


set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

namespace StableMatching
noncomputable section
open Classical

/-! ### Basic definitions -/

/-- Schools (M in Fleiner) -/
abbrev Schools (α : Type*) := Finset α

/-- Students (W in Fleiner) -/
abbrev Students (β : Type*) := Finset β

/-- Edges (E in Fleiner) - acceptable school-student pairs -/
abbrev Edges (α β : Type*) := Finset (α × β)

/-- Quota function for schools -/
abbrev Quota (α : Type*) := α → ℕ

/-- Preference relation: a ranks edge e above edge f -/
abbrev PrefRel (α β : Type*) := α ⊕ β → (α × β) → (α × β) → Prop


/-! ### Validity of preferences ⚠️⚠️⚠️-/

/-- Preference relation is valid (forms a strict linear order on incident edges) -/
def IsValidPref (pref : PrefRel α β) (E : Edges α β) : Prop :=
  -- Irreflexive: no edge prefers itself
  (∀ v e, ¬pref v e e) ∧
  -- Transitive
  (∀ v e f g, pref v e f → pref v f g → pref v e g) ∧
  -- Total on incident edges of the same vertex
  (∀ v e f, e ∈ E → f ∈ E → e ≠ f →
    ((∃ a, v = .inl a ∧ e.1 = a ∧ f.1 = a) ∨
     (∃ b, v = .inr b ∧ e.2 = b ∧ f.2 = b)) →
    (pref v e f ∨ pref v f e))




/-! ### Incident edges -/

/-- Edges incident to school a -/
def schoolEdges (E : Edges α β) (a : α) : Finset (α × β) :=
  E.filter (fun e => e.1 = a)

/-- Edges incident to student b -/
def studentEdges (E : Edges α β) (b : β) : Finset (α × β) :=
  E.filter (fun e => e.2 = b)


/-! ### Domination (Fleiner Section 2) -/

def betterForSchool (pref : PrefRel α β) (S : Edges α β) (a : α) (e : α × β) : Finset (α × β) :=
  S.filter (fun f => f.1 = a ∧ pref (.inl a) f e)

def betterForStudent (pref : PrefRel α β) (S : Edges α β) (b : β) (e : α × β) : Finset (α × β) :=
  S.filter (fun f => f.2 = b ∧ pref (.inr b) f e)

/-- Edge e is M-dominated by S: school e.1 has b(e.1) better edges in S -/
def mDominated (pref : PrefRel α β) (b : Quota α) (S : Edges α β) (e : α × β) : Prop :=
  (betterForSchool pref S e.1 e).card ≥ b e.1

/-- Edge e is W-dominated by S: student e.2 has a better edge in S -/
def wDominated (pref : PrefRel α β) (S : Edges α β) (e : α × β) : Prop :=
  (betterForStudent pref S e.2 e).card ≥ 1

/-- Edge e is dominated by S (M-dominated or W-dominated) -/
def dominated (pref : PrefRel α β) (b : Quota α) (S : Edges α β) (e : α × β) : Prop :=
  mDominated pref b S e ∨ wDominated pref S e

/-! ### Choice functions (Fleiner Section 3) -/

/-- C_M(S): edges not M-dominated by S (equation 6) -/
def choiceM (pref : PrefRel α β) (b : Quota α) (S : Edges α β) : Edges α β :=
  S.filter (fun e => ¬mDominated pref b S e)

/-- C_W(S): edges not W-dominated by S (equation 6) -/
def choiceW (pref : PrefRel α β) (S : Edges α β) : Edges α β :=
  S.filter (fun e => ¬wDominated pref S e)

/-- The complement Ā = A \ C(A) for M-side -/
def complementM (pref : PrefRel α β) (b : Quota α) (S : Edges α β) : Edges α β :=
  S \ choiceM pref b S

/-- The complement Ā = A \ C(A) for W-side -/
def complementW (pref : PrefRel α β) (S : Edges α β) : Edges α β :=
  S \ choiceW pref S

/-! ### Stable pairs and matchings (Fleiner equations 6-9) -/

/-- Stable pair (S_M, S_W): equation (6)
    C_M(S_M) = S_M ∩ S_W = C_W(S_W) -/
def IsStablePair (E : Edges α β) (pref : PrefRel α β) (b : Quota α)
    (S_M S_W : Edges α β) : Prop :=
  S_M ∪ S_W = E ∧
  choiceM pref b S_M = S_M ∩ S_W ∧
  choiceW pref S_W = S_M ∩ S_W

/-- Stable matching: S = S_M ∩ S_W for some stable pair -/
def IsStableMatching (E : Edges α β) (pref : PrefRel α β) (b : Quota α)
    (S : Edges α β) : Prop :=
  ∃ S_M S_W, IsStablePair E pref b S_M S_W ∧ S = S_M ∩ S_W

/-- The monotone function f from equation (9):
    f(S_M) := E \ ((E \ (S_M \ C_M(S_M))) \ C_W(E \ (S_M \ C_M(S_M)))) -/
def fixedPointFunction (E : Edges α β) (pref : PrefRel α β) (b : Quota α)
    (S_M : Edges α β) : Edges α β :=
  let step1 := complementM pref b S_M           -- S_M \ C_M(S_M)
  let step2 := E \ step1                         -- E \ step1
  let step3 := complementW pref step2            -- step2 \ C_W(step2)
  E \ step3

                                      -- E \ step3


/-! ### Lattice operations (Fleiner Theorem 5.3) -/

/-- Join: S₁ ∨ S₂ := C_M(S₁ ∪ S₂) -/
def matchingJoin (pref : PrefRel α β) (b : Quota α) (S₁ S₂ : Edges α β) : Edges α β :=
  choiceM pref b (S₁ ∪ S₂)

/-- Meet: S₁ ∧ S₂ := C_W(S₁ ∪ S₂) -/
def matchingMeet (pref : PrefRel α β) (S₁ S₂ : Edges α β) : Edges α β :=
  choiceW pref (S₁ ∪ S₂)

/-! ### Matching properties -/

/-- A matching respects quotas -/
def respectsQuotas (M : Schools α) (W : Students β) (b : Quota α) (S : Edges α β) : Prop :=
  (∀ a ∈ M, (schoolEdges S a).card ≤ b a) ∧
  (∀ w ∈ W, (studentEdges S w).card ≤ 1)

/-- School a is under-subscribed in S -/
def isUnderSubscribed (b : Quota α) (S : Edges α β) (a : α) : Prop :=
  (schoolEdges S a).card < b a

/-- Students matched to school a -/
def matchedToSchool (S : Edges α β) (a : α) : Finset β :=
  (schoolEdges S a).image (·.2)

/-- School matched to student b (if any) -/
def matchedToStudent (S : Edges α β) (b : β) : Option α :=
  ((studentEdges S b).image (·.1)).toList.head?



/-- If e is in choiceM, then it's not M-dominated -/
lemma mem_choiceM_iff (pref : PrefRel α β) (b : Quota α) (S : Edges α β) (e : α × β) :
    e ∈ choiceM pref b S ↔ e ∈ S ∧ ¬mDominated pref b S e := by
  simp [choiceM]

/-- If e is in choiceW, then it's not W-dominated -/
lemma mem_choiceW_iff (pref : PrefRel α β) (S : Edges α β) (e : α × β) :
    e ∈ choiceW pref S ↔ e ∈ S ∧ ¬wDominated pref S e := by
  simp [choiceW]

/-! ### Optimality -/

/-- M-optimal stable matching: best for all schools -/
def isMOptimal (E : Edges α β) (pref : PrefRel α β) (b : Quota α) (S : Edges α β) : Prop :=
  IsStableMatching E pref b S ∧
  ∀ S' : Edges α β, IsStableMatching E pref b S' →
    ∀ a : α, ∀ e ∈ schoolEdges S a, ∀ e' ∈ schoolEdges S' a,
      pref (.inl a) e e' ∨ e = e'

/-- W-optimal stable matching: best for all students -/
def isWOptimal (E : Edges α β) (pref : PrefRel α β) (b : Quota α) (S : Edges α β) : Prop :=
  IsStableMatching E pref b S ∧
  ∀ S' : Edges α β, IsStableMatching E pref b S' →
    ∀ w : β, ∀ e ∈ studentEdges S w, ∀ e' ∈ studentEdges S' w,
      pref (.inr w) e e' ∨ e = e'

/-! ### Set of all stable matchings -/

/-- The set of all stable matchings -/
def stableMatchings (E : Edges α β) (pref : PrefRel α β) (b : Quota α) : Set (Edges α β) :=
  {S | IsStableMatching E pref b S}

/-! ### Comonotonicity properties (Fleiner Section 3) -/

/-- Property (12): C(A) ⊆ A -/
def hasSubsetProperty {E : Type*} (C : Finset E → Finset E) : Prop :=
  ∀ A, C A ⊆ A

/-- Property (13): Ā = A \ C(A) is monotone -/
def hasComplementMonotone {E : Type*} (C : Finset E → Finset E) : Prop :=
  Monotone (fun A => A \ C A)

/-- Comonotone: properties (12) and (13) -/
def isComonotone {E : Type*} (C : Finset E → Finset E) : Prop :=
  hasSubsetProperty C ∧ hasComplementMonotone C

/-- Property (14): C(A) = C(B) whenever C(A) ⊆ B ⊆ A -/
def hasProperty14 {E : Type*} (C : Finset E → Finset E) : Prop :=
  ∀ A B, C A ⊆ B → B ⊆ A → C B = C A

/-- Path independence (equation 16) -/
def isPathIndependent {E : Type*} (C : Finset E → Finset E) : Prop :=
  ∀ A B, C (A ∪ B) = C (C A ∪ C B)


/-! ### Comonotonicity lemmas (Fleiner Section 3, properties 12-14) -/

/-- choiceM has property (12): C_M(A) ⊆ A -/
theorem choiceM_subset (pref : PrefRel α β) (b : Quota α) (A : Edges α β) :
    choiceM pref b A ⊆ A := by
    exact Finset.filter_subset _ _


/-- choiceW has property (12): C_W(A) ⊆ A -/
theorem choiceW_subset (pref : PrefRel α β) (A : Edges α β) :
    choiceW pref A ⊆ A := by
    exact Finset.filter_subset _ _


/-- betterForSchool is monotone in the second argument -/
lemma betterForSchool_monotone (pref : PrefRel α β) (a : α) (e : α × β) :
    Monotone (fun S => betterForSchool pref S a e) := by
  intro A B hAB
  unfold betterForSchool
  exact Finset.filter_subset_filter _ hAB

/-- The complement function for M is monotone (property 13 for choiceM) -/
theorem complementM_monotone (pref : PrefRel α β) (b : Quota α) :
    Monotone (complementM pref b) := by
  intro A B hAB e he
  simp only [complementM, Finset.mem_sdiff] at he ⊢
  obtain ⟨heA, heNotChoice⟩ := he
  constructor
  · exact hAB heA
  · intro hcontra
    unfold choiceM at heNotChoice hcontra
    simp only [Finset.mem_filter, not_and_or] at heNotChoice
    simp only [Finset.mem_filter] at hcontra
    cases heNotChoice with
    | inl h => exact absurd heA h
    | inr hdom =>
      -- hdom : ¬¬mDominated pref b A e
      -- Убираем двойное отрицание с помощью Classical
      have hdom_clean : mDominated pref b A e := Classical.not_not.mp hdom
      -- hcontra.2 : ¬mDominated pref b B e
      apply hcontra.2
      unfold mDominated at hdom_clean ⊢
      calc (betterForSchool pref B e.1 e).card
          ≥ (betterForSchool pref A e.1 e).card :=
            Finset.card_le_card (betterForSchool_monotone pref e.1 e hAB)
        _ ≥ b e.1 := hdom_clean

/-- betterForStudent is monotone in the second argument -/
lemma betterForStudent_monotone (pref : PrefRel α β) (b : β) (e : α × β) :
    Monotone (fun S => betterForStudent pref S b e) := by
  intro A B hAB
  unfold betterForStudent
  exact Finset.filter_subset_filter _ hAB

/-- The complement function for W is monotone (property 13 for choiceW) -/
theorem complementW_monotone (pref : PrefRel α β) :
    Monotone (complementW pref) := by
  intro A B hAB e he
  simp only [complementW, Finset.mem_sdiff] at he ⊢
  obtain ⟨heA, heNotChoice⟩ := he
  constructor
  · exact hAB heA
  · intro hcontra
    unfold choiceW at heNotChoice hcontra
    simp only [Finset.mem_filter, not_and_or] at heNotChoice
    simp only [Finset.mem_filter] at hcontra
    cases heNotChoice with
    | inl h => exact absurd heA h
    | inr hdom =>
      have hdom_clean : wDominated pref A e := Classical.not_not.mp hdom
      apply hcontra.2
      unfold wDominated at hdom_clean ⊢
      calc (betterForStudent pref B e.2 e).card
          ≥ (betterForStudent pref A e.2 e).card :=
            Finset.card_le_card (betterForStudent_monotone pref e.2 e hAB)
        _ ≥ 1 := hdom_clean


/-- choiceM is comonotone (combines properties 12 and 13) -/
theorem choiceM_comonotone (pref : PrefRel α β) (b : Quota α) :
    isComonotone (choiceM pref b) := by
    constructor;
    · intro A; exact?;
    · intro A B hAB;
      unfold StableMatching.choiceM;
      simp +contextual [ Finset.subset_iff ];
      intro a b ha hma; exact ⟨ hAB ha, fun _ => by
        refine' le_trans hma _;
        exact Finset.card_mono fun x hx => Finset.mem_filter.mpr ⟨ hAB ( Finset.mem_filter.mp hx |>.1 ), Finset.mem_filter.mp hx |>.2 ⟩ ⟩ ;

/-- choiceW is comonotone (combines properties 12 and 13) -/
theorem choiceW_comonotone (pref : PrefRel α β) :
    isComonotone (choiceW pref) := by
  constructor;
  · intro A; simp +decide [ StableMatching.choiceW ] ;
  · intro A B hAB;
    convert Finset.subset_iff.mpr _ using 1;
    simp +contextual [ StableMatching.choiceW ];
    exact fun a b ha hb => ⟨ hAB ha, fun _ => by exact le_trans hb ( Finset.card_mono <| Finset.filter_subset_filter _ hAB ) ⟩


lemma abstract_dominance_property {V : Type*} [DecidableEq V]
    (U B : Finset V) (r : V → V → Prop) (k : ℕ)
    (h_trans : ∀ x y z, r x y → r y z → r x z)
    (h_irr : ∀ x, ¬ r x x)
    (h_inter : (U ∩ B).card < k)
    (h_dom : ∀ d ∈ U, d ∉ B → (U.filter (fun x => r x d)).card ≥ k) :
    U ⊆ B := by
      by_contra h_contra;
      -- Let $m$ be a maximal element in $U \setminus B$ with respect to $r$.
      obtain ⟨m, hm⟩ : ∃ m ∈ U \ B, ∀ x ∈ U \ B, ¬r x m := by
        -- By definition of $U \setminus � B�$, there exists some $x \in U \setminus B$ such that for all $y \in U \setminus B$, $r y � x�$ is false.
        obtain ⟨x, hx⟩ : ∃ x ∈ U \ B, ∀ y ∈ U \ B, ¬r y x := by
          have h_finite : Finset.Nonempty (U \ B) := by
            exact Finset.nonempty_of_ne_empty fun h => h_contra <| Finset.sdiff_eq_empty_iff_subset.mp h
          -- By contradiction, assume there is no maximal element in $U \setminus B$.
          by_contra h_no_max;
          -- Since $U \setminus B$ is finite, � we� can construct a strictly increasing sequence in $U \setminus B$.
          have h_seq : ∃ seq : ℕ → V, (∀ n, seq n ∈ U \ B) ∧ (∀ n, r (seq (n + 1)) (seq n)) := by
            push_neg at h_no_max;
            choose! f hf using h_no_max;
            exact ⟨ fun n => Nat.recOn n ( Classical.choose h_finite ) fun n ih => f ih, fun n => Nat.recOn n ( Classical.choose_spec h_finite ) fun n ih => hf _ ih |>.1, fun n => hf _ ( show Nat.recOn n ( Classical.choose h_finite ) ( fun n ih => f ih ) ∈ U \ B from Nat.recOn n ( Classical.choose_spec h_finite ) fun n ih => hf _ ih |>.1 ) |>.2 ⟩;
          obtain ⟨seq, hseq⟩ := h_seq;
          -- Since $U \setminus B$ is finite, the sequence $seq$ must be injective.
          have h_inj : Function.Injective seq := by
            intros m n hmn;
            have h_inj : ∀ m n, m < n → r (seq n) (seq m) := by
              intro m n mn; induction mn <;> aesop;
            exact le_antisymm ( le_of_not_gt fun hmn' => h_irr _ <| by simpa [ hmn ] using h_inj _ _ hmn' ) ( le_of_not_gt fun hmn' => h_irr _ <| by simpa [ hmn ] using h_inj _ _ hmn' );
          exact absurd ( Finset.finite_toSet ( U \ B ) ) ( Set.infinite_of_injective_forall_mem h_inj fun n => hseq.1 n );
        use x;
      obtain ⟨hm₁, hm₂⟩ := hm;
      -- By $h_{dom}$, $|\{x \in U \mid r(x, m)\}| \ge k$.
      have h_card : (Finset.filter (fun x => r x m) U).card ≥ k := by
        aesop;
      exact Nat.not_lt_of_le h_card ( lt_of_le_of_lt ( Finset.card_le_card ( show Finset.filter ( fun x => r x m ) U ⊆ U ∩ B from fun x hx => Finset.mem_inter.mpr ⟨ Finset.mem_filter.mp hx |>.1, Classical.not_not.1 fun hx' => hm₂ x ( Finset.mem_sdiff.mpr ⟨ Finset.mem_filter.mp hx |>.1, hx' ⟩ ) ( Finset.mem_filter.mp hx |>.2 ) ⟩ ) ) h_inter )

theorem choiceM_property14 (E : Edges α β) (pref : PrefRel α β) (b : Quota α) (h_valid : IsValidPref pref E) :
    hasProperty14 (choiceM pref b) := by
  intro A B hAB hBA;
  -- To show $S \subseteq C_M(B)$, take any $x \in S$. Since $S \subseteq B$, $x \in B$. The set of edges � in� $B$ better than $x$ is a subset of the set of edges in $A$ better than $x$. Since $x$ is not M-dominated in $A$, the number of better edges in $A$ is $< b(x.1)$. Thus, the number of better edges in $B$ is also $< b(x.1)$, so $x$ is not M-dominated in $B$. Hence, $x \in C_M(B)$.
  have h_S_subset_CM_B : choiceM pref b A ⊆ choiceM pref b B := by
    intro e he;
    refine' Finset.mem_filter.mpr ⟨ hAB he, _ ⟩;
    exact fun h => Finset.mem_filter.mp he |>.2 ( le_trans h ( Finset.card_mono <| Finset.filter_subset_filter _ <| hBA ) );
  refine' Finset.Subset.antisymm _ h_S_subset_CM_B;
  intro x hx;
  by_contra h_contra;
  -- Let $U$ be the set of edges in $A$ better than $x$ for school $x.1$. Since $x$ is dominated in $A$, $|U| \ge b(x.1)$.
  set U := betterForSchool pref A x.1 x with hU
  have hU_card : U.card ≥ b x.1 := by
    unfold StableMatching.choiceM at *; aesop;
  -- Apply `abstract_dominance_property` with this $U$, the set $B$, the relation $r � =� \text{pref}(.inl x.1)$, and $k = b(x.1)$.
  have h_abstract : U ⊆ B := by
    apply abstract_dominance_property U B (fun y z => pref (.inl x.1) y z) (b x.1);
    · exact fun a b c hab hbc => h_valid.2.1 _ _ _ _ hab hbc;
    · exact fun y => h_valid.1 _ _;
    · -- Since $x$ is not M-dominated in $B$, the number of edges in $B$ better than $x$ is less than $b(x.1)$.
      have h_not_M_dominated_B : (betterForSchool pref B x.1 x).card < b x.1 := by
        exact lt_of_not_ge fun h => Finset.mem_filter.mp hx |>.2 h;
      refine' lt_of_le_of_lt _ h_not_M_dominated_B;
      refine' Finset.card_le_card _;
      simp +contextual [ Finset.subset_iff, betterForSchool ];
      unfold StableMatching.betterForSchool at *; aesop;
    · intro d hd hdB
      have h_dominated : mDominated pref b A d := by
        exact Classical.not_not.1 fun h => hdB <| hAB <| Finset.mem_filter.2 ⟨ Finset.mem_filter.1 hd |>.1, h ⟩;
      refine' le_trans _ ( Finset.card_mono <| show { x_1 ∈ U | pref ( Sum.inl x.1 ) x_1 d } ⊇ betterForSchool pref A d.1 d from _ );
      · unfold StableMatching.betterForSchool at *; aesop;
      · simp_all +decide [ Finset.subset_iff, StableMatching.betterForSchool ];
        exact fun a b ha ha' hb => h_valid.2.1 _ _ _ _ hb hd.2.2;
  -- Since $U \subseteq B$, we have $U = U \cap B$.
  have hU_eq : U = betterForSchool pref B x.1 x := by
    ext y; simp [U, betterForSchool];
    exact fun _ _ => ⟨ fun hy => h_abstract ( Finset.mem_filter.mpr ⟨ hy, by aesop ⟩ ), fun hy => hBA hy ⟩;
  simp_all +decide [ StableMatching.choiceM ];
  exact hx.2 ( by simpa only [ ← hU ] using hU_card )

/-
For any edge e in S, there exists an edge f in choiceW(S) that is equal to or better than e for the student.
-/
lemma exists_better_in_choiceW {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : StableMatching.Edges α β) (pref : StableMatching.PrefRel α β) (h_valid : StableMatching.IsValidPref pref E)
    (S : StableMatching.Edges α β) (e : α × β) (he : e ∈ S) :
    ∃ f ∈ StableMatching.choiceW pref S, f.2 = e.2 ∧ (f = e ∨ pref (.inr e.2) f e) := by
      by_contra h_no_max_I;
      -- By definition of $choiceW$, since there �'s� no maximal element in $R$, for every $f \in R$ there exists $g \in R$ such that $g$ is better � than� $f$.
      have h_exists_better : ∀ f ∈ (betterForStudent pref S e.2 e ∪ {e}), ∃ g ∈ (betterForStudent pref S e.2 e ∪ {e}), pref (.inr e.2) g f := by
        intro f hf
        by_cases h_f_in_choiceW : f ∈ StableMatching.choiceW pref S;
        · simp_all +decide [ StableMatching.choiceW, StableMatching.betterForStudent ];
          specialize h_no_max_I f.1 ; aesop;
        · unfold StableMatching.choiceW at h_f_in_choiceW; simp_all +decide [ StableMatching.wDominated ] ;
          unfold StableMatching.betterForStudent at *; simp_all +decide [ Finset.ext_iff ] ;
          cases hf <;> simp_all +decide [ StableMatching.IsValidPref ];
          grind +ring;
      -- By definition of $choiceW$, since there is no maximal element in $R$, we can create an infinite sequence of edges in $R$ where � each� edge is better than the previous one.
      have h_infinite_seq : ∃ (seq : ℕ → α × β), (∀ n, seq n ∈ betterForStudent pref S e.2 e ∪ {e}) ∧ (∀ n, pref (.inr e.2) (seq (n + 1)) (seq n)) := by
        choose! seq hseq using h_exists_better;
        exact ⟨ fun n => Nat.recOn n e fun n ih => seq ih, fun n => Nat.recOn n ( by simp +decide ) fun n ih => hseq _ ih |>.1, fun n => hseq _ ( show Nat.rec e ( fun n ih => seq ih ) n ∈ StableMatching.betterForStudent pref S e.2 e ∪ { e } from Nat.recOn n ( by simp +decide ) fun n ih => hseq _ ih |>.1 ) |>.2 ⟩;
      -- Since `seq` is an infinite sequence of edges in ` �R�`, and `R` is finite, this contradicts the fact that `R` is finite.
      obtain ⟨seq, hseq_mem, hseq_better⟩ := h_infinite_seq;
      have h_seq_finite : Set.Finite (Set.range seq) := by
        exact Set.Finite.subset ( Finset.finite_toSet ( betterForStudent pref S e.2 e ∪ { e } ) ) ( Set.range_subset_iff.mpr hseq_mem );
      have h_seq_injective : Function.Injective seq := by
        intros m n hmn;
        -- Since `pref` is a strict partial order, it is irreflexive and transitive.
        have h_irrefl : ∀ x, ¬pref (.inr e.2) x x := by
          exact fun x => h_valid.1 _ _
        have h_trans : ∀ x y z, pref (.inr e.2) x y → pref (.inr e.2) y z → pref (.inr e.2) x z := by
          exact fun x y z hxy hyz => h_valid.2.1 _ _ _ _ hxy hyz;
        -- By induction on $n$, we can show that for any $m < n$, $pref (.inr e.2) (seq n) (seq m)$.
        have h_ind : ∀ m n, m < n → pref (.inr e.2) (seq n) (seq m) := by
          intro m n hmn; induction hmn <;> aesop;
        exact le_antisymm ( le_of_not_gt fun hmn' => h_irrefl _ <| by simpa [ hmn ] using h_ind _ _ hmn' ) ( le_of_not_gt fun hmn' => h_irrefl _ <| by simpa [ hmn.symm ] using h_ind _ _ hmn' );
      exact h_seq_finite.not_infinite <| Set.infinite_range_of_injective h_seq_injective


theorem choiceW_property14 (E : Edges α β) (pref : PrefRel α β) (h_valid : IsValidPref pref E) :
    hasProperty14 (choiceW pref) := by
  intro A B hAB hBA;
  -- Let's show that `choiceW(A) ⊆ choiceW(B)`.
  have h_subset : StableMatching.choiceW pref A ⊆ StableMatching.choiceW pref B := by
    intro e he;
    unfold StableMatching.choiceW at *;
    simp_all +decide [ StableMatching.wDominated ];
    unfold StableMatching.betterForStudent at *; aesop;
  refine' Finset.Subset.antisymm _ h_subset;
  intro e he; simp_all +decide [ StableMatching.choiceW ] ;
  contrapose! he;
  intro heB
  obtain ⟨f, hf⟩ : ∃ f ∈ StableMatching.choiceW pref A, f.2 = e.2 ∧ (f = e ∨ pref (.inr e.2) f e) := by
    apply StableMatching.exists_better_in_choiceW E pref h_valid A e (hBA heB);
  simp_all +decide [ StableMatching.choiceW, StableMatching.wDominated ];
  use f;
  unfold StableMatching.betterForStudent; aesop;

/-- Alternative formulation of comonotonicity (Lemma 4.6):
    C is comonotone iff C(A) ⊆ A and C(B) ∩ A ⊆ C(A) for A ⊆ B -/
theorem comonotone_iff_intersection (C : Finset (α × β) → Finset (α × β)) :
    isComonotone C ↔
    (∀ A, C A ⊆ A) ∧ (∀ A B, A ⊆ B → C B ∩ A ⊆ C A) := by
  constructor;
  · intro h_comonotone;
    refine' ⟨ h_comonotone.1, fun A B hAB => _ ⟩;
    obtain ⟨ h₁, h₂ ⟩ := h_comonotone;
    have := h₂ hAB; simp_all +decide [ Finset.subset_iff ] ;
    exact fun a b hab hba => Classical.not_not.1 fun h => this a b hba h hab;
  · intro hC;
    constructor <;> intro A B hAB <;> simp_all +decide [ Finset.subset_iff];
    grind +ring

/-- choiceM satisfies the intersection property -/
theorem choiceM_intersection (pref : PrefRel α β) (b : Quota α) (A B : Edges α β)
    (h : A ⊆ B) :
    choiceM pref b B ∩ A ⊆ choiceM pref b A := by
    -- Apply the comonotonicity property of choiceM.
    apply (comonotone_iff_intersection (StableMatching.choiceM pref b)).mp (choiceM_comonotone pref b) |>.2 A B h

/-- choiceW satisfies the intersection property -/
theorem choiceW_intersection (pref : PrefRel α β) (A B : Edges α β)
    (h : A ⊆ B) :
    choiceW pref B ∩ A ⊆ choiceW pref A := by
  intro e he
  unfold StableMatching.choiceW at *
  simp only [Finset.mem_inter, Finset.mem_filter] at he ⊢
  obtain ⟨⟨heB, hNotDomB⟩, heA⟩ := he
  constructor
  · exact heA
  · intro hDomA
    apply hNotDomB
    unfold wDominated at hDomA ⊢
    calc (betterForStudent pref B e.2 e).card
        ≥ (betterForStudent pref A e.2 e).card :=
          Finset.card_le_card (betterForStudent_monotone pref e.2 e h)
      _ ≥ 1 := hDomA





theorem pathIndependent_implies_property14
    (C : Edges α β → Edges α β)
    (hP : isPathIndependent C) (hS : hasSubsetProperty C) :
    hasProperty14 C := by
      -- First, show that C is idempotent: C(C(A)) = C(A).
      have h_idempotent : ∀ A : StableMatching.Edges α β, C (C A) = C A := by
        intro A
        have := hP A ∅
        simp at this;
        -- Since $C$ is a choice function, we know that $C(\emptyset) = \emptyset$.
        have hC_empty : C ∅ = ∅ := by
          simpa using hS ∅;
        simpa [ hC_empty ] using this.symm;
      intro A B hCA hAB
      have h_union : C (A ∪ B) = C (B ∪ C A) := by
        have := hP A B; have := hP B ( C A ) ; simp_all +decide [ Finset.union_comm ] ;
        grind;
      simp_all +decide [ Finset.union_eq_left.2 ]

/-
Path independence and the subset property imply that the rejection function (complement) is monotone.
-/

theorem pathIndependent_implies_complementMonotone
    (C : Edges α β → Edges α β)
    (hP : isPathIndependent C) (hS : hasSubsetProperty C) :
    hasComplementMonotone C := by
      intro A B hAB x hx; simp_all +decide [ Finset.subset_iff ] ;
      have h_contra : C B = C (C A ∪ C (B \ A)) := by
        convert hP _ _ using 1;
        convert rfl;
        convert Finset.union_sdiff_of_subset ( show A ⊆ B from fun x hx => hAB _ _ hx ) using 1;
        congr! 1;
        · grind;
        · grind;
      have h_contra : C (C A ∪ C (B \ A)) ⊆ C A ∪ C (B \ A) := by
        exact hS _;
      simp_all +decide [ Finset.subset_iff ];
      exact fun h => hx.2 ( h_contra _ _ h |> Or.resolve_right <| fun h' => by have := hS ( B \ A ) h'; aesop )


theorem pathIndependent_iff_comonotone_and_property14
    (C : Finset (α × β) → Finset (α × β)) :
    isPathIndependent C ∧ hasSubsetProperty C ↔
    isComonotone C ∧ hasProperty14 C := by
  constructor;
  · exact fun h => ⟨ ⟨ h.2, pathIndependent_implies_complementMonotone C h.1 h.2 ⟩, pathIndependent_implies_property14 C h.1 h.2 ⟩;
  · intro h
    obtain ⟨h_comonotone, h_property14⟩ := h;
    refine' ⟨ fun A B => _, h_comonotone.1 ⟩;
    have h_subset : C (A ∪ B) ⊆ C A ∪ C B := by
      have := @comonotone_iff_intersection;
      rw [ this ] at h_comonotone;
      have := h_comonotone.2 A ( A ∪ B ) ( Finset.subset_union_left ) ; have := h_comonotone.2 B ( A ∪ B ) ( Finset.subset_union_right ) ; simp_all +decide [ Finset.subset_iff ] ;
      grind;
    have h_eq : C (C A ∪ C B) = C (A ∪ B) := by
      have h_subset : C A ∪ C B ⊆ A ∪ B := by
        exact Finset.union_subset_union ( h_comonotone.1 A ) ( h_comonotone.1 B )
      have h_superset : C (A ∪ B) ⊆ C A ∪ C B := by
        assumption
      exact?;
    grind


/-- choiceM is path independent -/
theorem choiceM_pathIndependent (E : Edges α β) (pref : PrefRel α β) (b : Quota α) (h_valid : IsValidPref pref E):
    isPathIndependent (choiceM pref b) := by
  -- By definition of choiceM, we know that it is comonotone.
  have h_choiceM_comonotone : isComonotone (choiceM pref b) := by
    exact choiceM_comonotone pref b
  have h_choiceM_property14 : hasProperty14 (choiceM pref b) := by
    exact choiceM_property14 E pref b h_valid
  apply (pathIndependent_iff_comonotone_and_property14 (choiceM pref b)).mpr ⟨h_choiceM_comonotone, h_choiceM_property14⟩ |>.1

/-- choiceW is path independent -/
theorem choiceW_pathIndependent (E : Edges α β) (pref : PrefRel α β) (h_valid : IsValidPref pref E):
    isPathIndependent (choiceW pref) := by
  -- By definition of choiceW, we know that it is comonotone.
  have h_choiceW_comonotone : isComonotone (choiceW pref) := by
    exact?;
  have h_choiceW_property14 : hasProperty14 (choiceW pref) := by
    exact?;
  apply (pathIndependent_iff_comonotone_and_property14 (choiceW pref)).mpr ⟨h_choiceW_comonotone, h_choiceW_property14⟩ |>.1






/- ### Fixed points-/

theorem fixedPointF_monotone (E : Edges α β) (pref : PrefRel α β) (b : Quota α) :
    Monotone (fixedPointFunction E pref b) := by
  intro A B hAB
  unfold fixedPointFunction
  -- Цель: E \ (complementW pref (E \ complementM pref b A)) ⊆
  --       E \ (complementW pref (E \ complementM pref b B))

  -- Шаг 1: complementM монотонен
  have h1 : complementM pref b A ⊆ complementM pref b B :=
    complementM_monotone pref b hAB

  -- Шаг 2: вычитание переворачивает порядок
  have h2 : E \ complementM pref b B ⊆ E \ complementM pref b A :=
    Finset.sdiff_subset_sdiff (le_refl E) h1

  -- Шаг 3: complementW монотонен
  have h3 : complementW pref (E \ complementM pref b B) ⊆
            complementW pref (E \ complementM pref b A) :=
    complementW_monotone pref h2

  -- Шаг 4: снова вычитание переворачивает
  exact Finset.sdiff_subset_sdiff (le_refl E) h3



/-- fixedPointFunction as an OrderHom for applying Tarski's theorem -/
def fixedPointFAsOrderHom (E : Edges α β) (pref : PrefRel α β) (b : Quota α) :
    Finset (α × β) →o Finset (α × β) where
  toFun := fixedPointFunction E pref b
  monotone' := fixedPointF_monotone E pref b

/-- Iteration of fixedPointFunction starting from ∅ -/
def iterateFixedPointF (E : Edges α β) (pref : PrefRel α β) (b : Quota α) : ℕ → Edges α β
  | 0 => ∅
  | n + 1 => fixedPointFunction E pref b (iterateFixedPointF E pref b n)

/-- The iteration is monotone -/
theorem iterateFixedPointF_monotone (E : Edges α β) (pref : PrefRel α β) (b : Quota α) (n : ℕ) :
    iterateFixedPointF E pref b n ⊆ iterateFixedPointF E pref b (n + 1) := by
  induction n with
  | zero =>
    show ∅ ⊆ fixedPointFunction E pref b ∅
    apply Finset.empty_subset
  | succ n ih =>
    show fixedPointFunction E pref b (iterateFixedPointF E pref b n) ⊆
         fixedPointFunction E pref b (fixedPointFunction E pref b (iterateFixedPointF E pref b n))
    apply fixedPointF_monotone
    exact ih

/-- For finite E, the iteration stabilizes -/
theorem iterateFixedPointF_stabilizes (E : Edges α β) (pref : PrefRel α β) (b : Quota α)
    [DecidableEq (α × β)] [Fintype E] :
    ∃ n, iterateFixedPointF E pref b n = iterateFixedPointF E pref b (n + 1) := by
  -- Цепь ∅ ⊆ f(∅) ⊆ f(f(∅)) ⊆ ... ⊆ E
  -- Все подмножества E, цепь монотонна, E конечно → стабилизируется
  by_contra! h_contra;
  have h_seq_finite : Set.Finite (Set.range (iterateFixedPointF E pref b)) := by
    exact Set.Finite.subset ( Set.toFinite ( Finset.powerset E ) ) ( Set.range_subset_iff.mpr fun n => Finset.mem_powerset.mpr <| by
      refine' Nat.recOn n _ _ <;> simp_all +decide [ StableMatching.iterateFixedPointF ];
      unfold StableMatching.fixedPointFunction; aesop; );
  exact h_seq_finite.not_infinite <| Set.infinite_range_of_injective ( StrictMono.injective <| strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne ( iterateFixedPointF_monotone E pref b n ) ( h_contra n ) )

/-- The stabilization point is a fixed point -/
theorem fixedPoint_exists (E : Edges α β) (pref : PrefRel α β) (b : Quota α)
    [DecidableEq (α × β)] [Fintype E] :
    ∃ S_M, fixedPointFunction E pref b S_M = S_M := by
  obtain ⟨n, hn⟩ := iterateFixedPointF_stabilizes E pref b
  use iterateFixedPointF E pref b n
  -- hn: iterateFixedPointF n = iterateFixedPointF (n + 1)
  -- Нужно: fixedPointFunction (iterateFixedPointF n) = iterateFixedPointF n
  calc fixedPointFunction E pref b (iterateFixedPointF E pref b n)
      = iterateFixedPointF E pref b (n + 1) := by rfl
    _ = iterateFixedPointF E pref b n := hn.symm

/-- From a fixed point S_M, construct S_W using equation (7) -/
def stablePairW (E : Edges α β) (pref : PrefRel α β) (b : Quota α) (S_M : Edges α β) :
    Edges α β :=
  E \ (S_M \ choiceM pref b S_M)

/-- A fixed point of fixedPointFunction gives a stable pair -/
theorem fixedPoint_gives_stablePair (E : Edges α β) (pref : PrefRel α β) (b : Quota α)
    (S_M : Edges α β) (hS_M : fixedPointFunction E pref b S_M = S_M):
    IsStablePair E pref b S_M (stablePairW E pref b S_M) := by
  unfold IsStablePair stablePairW
  constructor
  ·
    unfold StableMatching.fixedPointFunction at hS_M;
    simp_all +decide [ Finset.ext_iff];
    intro a b; specialize hS_M a b; by_cases ha : ( a, b ) ∈ S_M <;> simp_all +decide [ StableMatching.choiceM, StableMatching.complementM, StableMatching.complementW ] ;
  constructor
  ·
    unfold StableMatching.fixedPointFunction at hS_M;
    simp_all +decide [ Finset.ext_iff, Finset.mem_sdiff ];
    intro a b; specialize hS_M a b; unfold StableMatching.choiceM at *; aesop;
  ·
    unfold StableMatching.fixedPointFunction at hS_M;
    simp_all +decide [ Finset.ext_iff, StableMatching.choiceM, StableMatching.choiceW, StableMatching.complementM, StableMatching.complementW ];
    grind

/-- Main theorem: stable matchings exist (Theorem 3.1) -/
theorem stable_matching_exists (E : Edges α β) (pref : PrefRel α β) (b : Quota α) (h_valid : IsValidPref pref E)
    [Fintype α] [Fintype β] :
    ∃ S, IsStableMatching E pref b S := by
  haveI : DecidableEq (α × β) := Classical.decEq _
  have ⟨S_M, hS_M⟩ := fixedPoint_exists E pref b
  refine ⟨S_M ∩ stablePairW E pref b S_M, S_M, stablePairW E pref b S_M,
          fixedPoint_gives_stablePair E pref b S_M hS_M, ?_⟩
  convert rfl





/-- choiceM is increasing (equation 20): |C_M(A)| ≤ |C_M(B)| when A ⊆ B

    Intuition: When we add more edges to A, schools have more options,
    so the number of non-dominated edges can only increase.

    This property is crucial for proving that stable matchings form a lattice.
-/



theorem choiceM_increasing (E : Edges α β) (pref : PrefRel α β) (b : Quota α)
    (h_valid : IsValidPref pref E) :
    ∀ A B : Edges α β, A ⊆ B → (choiceM pref b A).card ≤ (choiceM pref b B).card := by
  intro A B hAB
  sorry

/-- choiceW is increasing -/
theorem choiceW_increasing (E : Edges α β) (pref : PrefRel α β)
    (h_valid : IsValidPref pref E) :
    ∀ A B : Edges α β, A ⊆ B → (choiceW pref A).card ≤ (choiceW pref B).card := by
  intro A B hAB
  sorry




end
end StableMatching
