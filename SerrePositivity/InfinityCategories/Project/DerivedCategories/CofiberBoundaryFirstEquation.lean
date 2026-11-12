module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanSuffixReplacementTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedEquation

/-! # cofiber 候補の A 側方程式

概要：A 側の微分式と後続置換の右辺変化を接続する。
方針：実境界の残差と明示解の合成式を使い、挿入後の方程式を直接検証する。
規約：HA Proposition 1.3.1.10。使われ方：coslice 充填候補の未知方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- Left 候補は A を加えた未知集合の微分方程式を満たす。 -/
lemma cofiberBoundaryLeftCandidate_first_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb).Equation (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate f g b hb)
    (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) 0 (Fin.last (n + 3)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]
        dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; push_cast; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_A f g b hb) rfl rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb - (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow •
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal f g)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb)
        (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1)))
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate_first_heq f g b hb _ _ _ _ _ _ _
  · unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftCandidate _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_rhs_self]
    have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftBase f g b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).1.val
      0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_A f g b hb)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_apex f g b hb) rfl
      (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb)
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal f g))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLeftNative f g b hb).1.property (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA_heq f g b hb).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_left_diagonal_heq f g b hb)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree_negOnePow,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose] using H
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA_differential f g b hb

/-- Right 候補は A を加えた未知集合の微分方程式を満たす。 -/
lemma cofiberBoundaryRightCandidate_first_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone f g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb).Equation (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate f g b hb)
    (insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) 0 (Fin.last (n + 3)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_min 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffix_insert_max 0 _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffix_insert 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)]
        dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; push_cast; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_A f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA f g b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb - (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n).negOnePow •
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal f g)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb)
        (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree n + 1)))
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate_first_heq f g b hb _ _ _ _ _ _ _
  · unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightCandidate _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerve.SimplexData.spanInsertUnknowns
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed_rhs_self]
    have H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightBase f g b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).1.val
      0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_suffixHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_A f g b hb)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_apex f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryTarget_right_eq f g b)
      (by dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree]; omega)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftQ f g b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA f g b hb)
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pushoutDiagonal f g))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRightNative f g b hb).1.property (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryRhsA_heq_right f g b hb).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberCosliceBoundary_right_diagonal_heq f g b hb)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanOnePrefixRhs, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryDegree_negOnePow,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.complex_compose] using H
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberBoundaryLiftA_differential f g b hb

end SerrePositivity.InfinityCategories.Project.DerivedCategories
