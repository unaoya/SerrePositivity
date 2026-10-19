module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Derived.SpanSuffixReplacementTransport
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-! # cofiber 候補の B・C 側方程式

概要：脚側の零未知成分と後続置換の右辺変化を接続する。
方針：実境界の残差と明示解の合成式を使い、挿入後の方程式を直接検証する。
規約：HA Proposition 1.3.1.10。使われ方：coslice 充填候補の未知方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- A は二番目の固定頂点と後続部分の集合に属さない。 -/
lemma spanFirst_notMem_secondSuffix (n : ℕ) :
    (0 : Fin (n + 4)) ∉ insert (spanSecondPrefix n) (spanSuffixFaces n) := by
  simp only [Finset.mem_insert, not_or]
  exact ⟨ne_of_lt (spanSecondPrefix_pos n), spanPrefix_notMem_suffix 0 (spanApex_pos n)⟩

/-- A を含む挿入集合は二番目の固定頂点側の集合に含まれない。 -/
lemma spanFirst_insert_not_subset_second (n : ℕ) :
    ¬ insert (0 : Fin (n + 4)) (spanSuffixFaces n) ⊆
      insert (spanSecondPrefix n) (spanSuffixFaces n) := by
  intro h
  exact spanFirst_notMem_secondSuffix n (h (Finset.mem_insert_self _ _))

/-- Left 候補の脚側未知集合の右辺は零。 -/
lemma cofiberBoundaryLeftCandidate_second_rhs_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryLeftCandidate f g b hb).spanOnePrefixRhs
      (spanSecondPrefix n) (spanSecondPrefix_lt_apex n) = 0 := by
  unfold cofiberBoundaryLeftCandidate SimplexData.spanInsertUnknowns SimplexData.spanOnePrefixRhs
  rw [SimplexData.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (spanFirst_insert_not_subset_second n)]
  have H := SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
    (cofiberBoundaryLeftBase f g b) (cofiberBoundaryLeftNative f g b hb).1.val
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
    (spanBoundaryLeftZeroData_suffixHom (sliceUnderUncurry b))
    (cofiberCosliceBoundary_left_B f g b hb)
    (cofiberCosliceBoundary_left_apex f g b hb) rfl
    (by dsimp only [cofiberBoundaryDegree]; omega)
    (cofiberBoundaryLiftQ f g b hb) (cofiberBoundaryRhsB f g b hb)
    (Cochain.ofHom (pushoutInclusionB f g))
    (cofiberBoundaryLeftNative f g b hb).1.property
    (cofiberBoundaryRhsB_heq f g b hb).symm
    (cofiberCosliceBoundary_left_inclusion_heq f g b hb)
  rw [Checks.complex_compose, cofiberBoundaryLiftQ_inclusionB,
    ← cofiberBoundaryDegree_negOnePow n] at H
  simp only [smul_smul, Int.units_mul_self, one_smul, sub_self] at H
  exact eq_of_heq (H.trans (gradedHom_zero_heq (A := S)
    (cofiberCosliceBoundary_left_B f g b hb) rfl
    (show -(n : ℤ) - 1 + 1 = cofiberBoundaryDegree n + 1 from rfl)).symm)

/-- Left 候補の脚側未知集合の成分は零。 -/
lemma cofiberBoundaryLeftCandidate_second_hom_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ)
    (hI : 2 ≤ (insert (spanSecondPrefix n) (spanSuffixFaces n)).card)
    (hx : x = (insert (spanSecondPrefix n) (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hy : y = (insert (spanSecondPrefix n) (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert (spanSecondPrefix n) (spanSuffixFaces n)).card : ℤ)) :
    (cofiberBoundaryLeftCandidate f g b hb).hom
      (insert (spanSecondPrefix n) (spanSuffixFaces n)) x y k hI hx hy hk = 0 := by
  have hq : insert (spanSecondPrefix n) (spanSuffixFaces n) ≠ spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n), card_spanSuffixFaces] at hc
    omega
  have ha : insert (spanSecondPrefix n) (spanSuffixFaces n) ≠ insert 0 (spanSuffixFaces n) := by
    intro h
    exact spanFirst_insert_not_subset_second n (h ▸ Finset.Subset.rfl)
  rw [cofiberBoundaryLeftCandidate_hom_of_ne f g b hb _ x y k hI hx hy hk hq ha]
  exact spanBoundaryLeftZeroData_unknownHom (sliceUnderUncurry b) _
    (Finset.subset_insert _ _) x y k hI hx hy hk

/-- Left 候補は脚側未知集合の方程式を満たす。 -/
lemma cofiberBoundaryLeftCandidate_second_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryLeftCandidate f g b hb).Equation
      (insert (spanSecondPrefix n) (spanSuffixFaces n)) := by
  apply SimplexData.equation_of_fixed (cofiberBoundaryLeftCandidate f g b hb)
    (insert (spanSecondPrefix n) (spanSuffixFaces n)) (spanSecondPrefix n) (Fin.last (n + 3))
    (-(n : ℤ) - 1)
    (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]; omega)
    (spanSuffix_insert_min _ (spanSecondPrefix_lt_apex n) _) (spanSuffix_insert_max _ _)
    (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]; push_cast; omega)
  rw [cofiberBoundaryLeftCandidate_second_hom_zero f g b hb]
  change differential S 0 = (cofiberBoundaryLeftCandidate f g b hb).spanOnePrefixRhs
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
  rw [cofiberBoundaryLeftCandidate_second_rhs_zero f g b hb]
  exact map_zero _

/-- Right 候補の脚側未知集合の右辺は零。 -/
lemma cofiberBoundaryRightCandidate_second_rhs_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryRightCandidate f g b hb).spanOnePrefixRhs
      (spanSecondPrefix n) (spanSecondPrefix_lt_apex n) = 0 := by
  unfold cofiberBoundaryRightCandidate SimplexData.spanInsertUnknowns SimplexData.spanOnePrefixRhs
  rw [SimplexData.rhs_replaceFixed_of_not_subset _ _ _ _ _ _ _ _ _ _ _
    (spanFirst_insert_not_subset_second n)]
  have H := SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
    (cofiberBoundaryRightBase f g b) (cofiberBoundaryRightNative f g b hb).1.val
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
    (spanBoundaryRightZeroData_suffixHom (sliceUnderUncurry b))
    (cofiberCosliceBoundary_right_C f g b hb)
    (cofiberCosliceBoundary_right_apex f g b hb) (cofiberBoundaryTarget_right_eq f g b)
    (by dsimp only [cofiberBoundaryDegree]; omega)
    (cofiberBoundaryLiftQ f g b hb) (cofiberBoundaryRhsC f g b hb)
    (Cochain.ofHom (pushoutInclusionC f g))
    (cofiberBoundaryRightNative f g b hb).1.property
    (cofiberBoundaryRhsC_heq f g b hb).symm
    (cofiberCosliceBoundary_right_inclusion_heq f g b hb)
  rw [Checks.complex_compose, cofiberBoundaryLiftQ_inclusionC,
    ← cofiberBoundaryDegree_negOnePow n] at H
  simp only [smul_smul, Int.units_mul_self, one_smul, sub_self] at H
  exact eq_of_heq (H.trans (gradedHom_zero_heq (A := S)
    (cofiberCosliceBoundary_right_C f g b hb) (cofiberBoundaryTarget_right_eq f g b)
    (show -(n : ℤ) - 1 + 1 = cofiberBoundaryDegree n + 1 from rfl)).symm)

/-- Right 候補の脚側未知集合の成分は零。 -/
lemma cofiberBoundaryRightCandidate_second_hom_zero {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g))
    (x y : Fin (n + 4)) (k : ℤ)
    (hI : 2 ≤ (insert (spanSecondPrefix n) (spanSuffixFaces n)).card)
    (hx : x = (insert (spanSecondPrefix n) (spanSuffixFaces n)).min' (Index.nonempty hI))
    (hy : y = (insert (spanSecondPrefix n) (spanSuffixFaces n)).max' (Index.nonempty hI))
    (hk : k = 2 - ((insert (spanSecondPrefix n) (spanSuffixFaces n)).card : ℤ)) :
    (cofiberBoundaryRightCandidate f g b hb).hom
      (insert (spanSecondPrefix n) (spanSuffixFaces n)) x y k hI hx hy hk = 0 := by
  have hq : insert (spanSecondPrefix n) (spanSuffixFaces n) ≠ spanSuffixFaces n := by
    intro h
    have hc := congrArg Finset.card h
    rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n), card_spanSuffixFaces] at hc
    omega
  have ha : insert (spanSecondPrefix n) (spanSuffixFaces n) ≠ insert 0 (spanSuffixFaces n) := by
    intro h
    exact spanFirst_insert_not_subset_second n (h ▸ Finset.Subset.rfl)
  rw [cofiberBoundaryRightCandidate_hom_of_ne f g b hb _ x y k hI hx hy hk hq ha]
  exact spanBoundaryRightZeroData_unknownHom (sliceUnderUncurry b) _
    (Finset.subset_insert _ _) x y k hI hx hy hk

/-- Right 候補は脚側未知集合の方程式を満たす。 -/
lemma cofiberBoundaryRightCandidate_second_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryRightCandidate f g b hb).Equation
      (insert (spanSecondPrefix n) (spanSuffixFaces n)) := by
  apply SimplexData.equation_of_fixed (cofiberBoundaryRightCandidate f g b hb)
    (insert (spanSecondPrefix n) (spanSuffixFaces n)) (spanSecondPrefix n) (Fin.last (n + 3))
    (-(n : ℤ) - 1)
    (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]; omega)
    (spanSuffix_insert_min _ (spanSecondPrefix_lt_apex n) _) (spanSuffix_insert_max _ _)
    (by rw [card_spanSuffix_insert _ (spanSecondPrefix_lt_apex n)]; push_cast; omega)
  rw [cofiberBoundaryRightCandidate_second_hom_zero f g b hb]
  change differential S 0 = (cofiberBoundaryRightCandidate f g b hb).spanOnePrefixRhs
    (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)
  rw [cofiberBoundaryRightCandidate_second_rhs_zero f g b hb]
  exact map_zero _

end SerrePositivity.InfinityCategories
