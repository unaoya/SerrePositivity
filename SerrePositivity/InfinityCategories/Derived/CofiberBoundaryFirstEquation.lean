module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryCandidateComponents
public import SerrePositivity.InfinityCategories.Derived.SpanSuffixReplacementTransport
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-! # cofiber 候補の A 側方程式

概要：A 側の微分式と後続置換の右辺変化を接続する。
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

/-- Left 候補は A を加えた未知集合の微分方程式を満たす。 -/
lemma cofiberBoundaryLeftCandidate_first_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryLeftCandidate f g b hb).Equation (insert 0 (spanSuffixFaces n)) := by
  apply SimplexData.equation_of_fixed_heq (cofiberBoundaryLeftCandidate f g b hb)
    (insert 0 (spanSuffixFaces n)) 0 (Fin.last (n + 3)) (cofiberBoundaryDegree n)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
    (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]
        dsimp only [cofiberBoundaryDegree]; push_cast; omega)
    (cofiberCosliceBoundary_left_A f g b hb) rfl rfl
    (cofiberBoundaryLiftA f g b hb)
    (cofiberBoundaryRhsA f g b hb - (cofiberBoundaryDegree n).negOnePow •
      (Cochain.ofHom (pushoutDiagonal f g)).comp (cofiberBoundaryLiftQ f g b hb)
        (zero_add (cofiberBoundaryDegree n + 1)))
  · exact cofiberBoundaryLeftCandidate_first_heq f g b hb _ _ _ _ _ _ _
  · unfold cofiberBoundaryLeftCandidate SimplexData.spanInsertUnknowns
    rw [SimplexData.replaceFixed_rhs_self]
    have H := SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
      (cofiberBoundaryLeftBase f g b) (cofiberBoundaryLeftNative f g b hb).1.val
      0 (spanApex_pos n) (spanBoundaryLeftZeroData_suffixHom (sliceUnderUncurry b))
      (cofiberCosliceBoundary_left_A f g b hb)
      (cofiberCosliceBoundary_left_apex f g b hb) rfl
      (by dsimp only [cofiberBoundaryDegree]; omega)
      (cofiberBoundaryLiftQ f g b hb) (cofiberBoundaryRhsA f g b hb)
      (Cochain.ofHom (pushoutDiagonal f g))
      (cofiberBoundaryLeftNative f g b hb).1.property (cofiberBoundaryRhsA_heq f g b hb).symm
      (cofiberCosliceBoundary_left_diagonal_heq f g b hb)
    simpa only [SimplexData.spanOnePrefixRhs, cofiberBoundaryDegree_negOnePow,
      Checks.complex_compose] using H
  · exact cofiberBoundaryLiftA_differential f g b hb

/-- Right 候補は A を加えた未知集合の微分方程式を満たす。 -/
lemma cofiberBoundaryRightCandidate_first_equation {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    (cofiberBoundaryRightCandidate f g b hb).Equation (insert 0 (spanSuffixFaces n)) := by
  apply SimplexData.equation_of_fixed_heq (cofiberBoundaryRightCandidate f g b hb)
    (insert 0 (spanSuffixFaces n)) 0 (Fin.last (n + 3)) (cofiberBoundaryDegree n)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
    (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]
        dsimp only [cofiberBoundaryDegree]; push_cast; omega)
    (cofiberCosliceBoundary_right_A f g b hb) (cofiberBoundaryTarget_right_eq f g b) rfl
    (cofiberBoundaryLiftA f g b hb)
    (cofiberBoundaryRhsA f g b hb - (cofiberBoundaryDegree n).negOnePow •
      (Cochain.ofHom (pushoutDiagonal f g)).comp (cofiberBoundaryLiftQ f g b hb)
        (zero_add (cofiberBoundaryDegree n + 1)))
  · exact cofiberBoundaryRightCandidate_first_heq f g b hb _ _ _ _ _ _ _
  · unfold cofiberBoundaryRightCandidate SimplexData.spanInsertUnknowns
    rw [SimplexData.replaceFixed_rhs_self]
    have H := SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
      (cofiberBoundaryRightBase f g b) (cofiberBoundaryRightNative f g b hb).1.val
      0 (spanApex_pos n) (spanBoundaryRightZeroData_suffixHom (sliceUnderUncurry b))
      (cofiberCosliceBoundary_right_A f g b hb)
      (cofiberCosliceBoundary_right_apex f g b hb) (cofiberBoundaryTarget_right_eq f g b)
      (by dsimp only [cofiberBoundaryDegree]; omega)
      (cofiberBoundaryLiftQ f g b hb) (cofiberBoundaryRhsA f g b hb)
      (Cochain.ofHom (pushoutDiagonal f g))
      (cofiberBoundaryRightNative f g b hb).1.property (cofiberBoundaryRhsA_heq_right f g b hb).symm
      (cofiberCosliceBoundary_right_diagonal_heq f g b hb)
    simpa only [SimplexData.spanOnePrefixRhs, cofiberBoundaryDegree_negOnePow,
      Checks.complex_compose] using H
  · exact cofiberBoundaryLiftA_differential f g b hb

end SerrePositivity.InfinityCategories
