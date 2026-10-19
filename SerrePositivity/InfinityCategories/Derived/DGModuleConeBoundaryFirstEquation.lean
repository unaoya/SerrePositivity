module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryCandidateComponents
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
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- Left 候補は A を加えた未知集合の微分方程式を満たす。 -/
lemma dgModuleConeBoundaryLeftCandidate_first_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryLeftCandidate A D f b hb).Equation (insert 0 (spanSuffixFaces n)) := by
  apply SimplexData.equation_of_fixed_heq (dgModuleConeBoundaryLeftCandidate A D f b hb)
    (insert 0 (spanSuffixFaces n)) 0 (Fin.last (n + 3)) (dgModuleConeBoundaryDegree n)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
    (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]
        dsimp only [dgModuleConeBoundaryDegree]; push_cast; omega)
    (dgModuleConeBoundary_left_A A D f b hb) rfl rfl
    (dgModuleConeBoundaryLiftA A D f b hb)
    (dgModuleConeBoundaryRhsA A D f b hb)
  · exact dgModuleConeBoundaryLeftCandidate_first_heq A D f b hb _ _ _ _ _ _ _
  · unfold dgModuleConeBoundaryLeftCandidate SimplexData.spanInsertUnknowns
    rw [SimplexData.replaceFixed_rhs_self]
    have H := SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
      (dgModuleConeBoundaryLeftBase A D f b) (dgModuleConeBoundaryLeftNative A D f b hb).1.val
      0 (spanApex_pos n) (spanBoundaryLeftZeroData_suffixHom (sliceUnderUncurry b))
      (dgModuleConeBoundary_left_A A D f b hb)
      (dgModuleConeBoundary_left_apex A D f b hb) rfl
      (by dsimp only [dgModuleConeBoundaryDegree]; omega)
      (dgModuleConeBoundaryLiftQ A D f b hb) (dgModuleConeBoundaryRhsA A D f b hb)
      (0 : GradedHom A (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) 0)
      (dgModuleConeBoundaryLeftNative A D f b hb).1.property (dgModuleConeBoundaryRhsA_heq A D
        f b hb).symm
      (dgModuleConeBoundary_left_diagonal_heq A D f b hb)
    simpa only [SimplexData.spanOnePrefixRhs, dgModuleConeBoundaryDegree_negOnePow,
      compose_zero, smul_zero, sub_zero] using H
  · exact dgModuleConeBoundaryLiftA_differential A D f b hb

/-- Right 候補は A を加えた未知集合の微分方程式を満たす。 -/
lemma dgModuleConeBoundaryRightCandidate_first_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f)) :
    (dgModuleConeBoundaryRightCandidate A D f b hb).Equation (insert 0 (spanSuffixFaces n)) := by
  apply SimplexData.equation_of_fixed_heq (dgModuleConeBoundaryRightCandidate A D f b hb)
    (insert 0 (spanSuffixFaces n)) 0 (Fin.last (n + 3)) (dgModuleConeBoundaryDegree n)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]; omega)
    (spanSuffix_insert_min 0 (spanApex_pos n) _) (spanSuffix_insert_max 0 _)
    (by rw [card_spanSuffix_insert 0 (spanApex_pos n)]
        dsimp only [dgModuleConeBoundaryDegree]; push_cast; omega)
    (dgModuleConeBoundary_right_A A D f b hb) (dgModuleConeBoundaryTarget_right_eq A D f b) rfl
    (dgModuleConeBoundaryLiftA A D f b hb)
    (dgModuleConeBoundaryRhsA A D f b hb)
  · exact dgModuleConeBoundaryRightCandidate_first_heq A D f b hb _ _ _ _ _ _ _
  · unfold dgModuleConeBoundaryRightCandidate SimplexData.spanInsertUnknowns
    rw [SimplexData.replaceFixed_rhs_self]
    have H := SimplexData.spanOnePrefixRhs_replaceFixed_suffix_heq
      (dgModuleConeBoundaryRightBase A D f b) (dgModuleConeBoundaryRightNative A D f b hb).1.val
      0 (spanApex_pos n) (spanBoundaryRightZeroData_suffixHom (sliceUnderUncurry b))
      (dgModuleConeBoundary_right_A A D f b hb)
      (dgModuleConeBoundary_right_apex A D f b hb) (dgModuleConeBoundaryTarget_right_eq A D f b)
      (by dsimp only [dgModuleConeBoundaryDegree]; omega)
      (dgModuleConeBoundaryLiftQ A D f b hb) (dgModuleConeBoundaryRhsA A D f b hb)
      (0 : GradedHom A (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f)) 0)
      (dgModuleConeBoundaryRightNative A D f b hb).1.property
        (dgModuleConeBoundaryRhsA_heq_right A D f b hb).symm
      (dgModuleConeBoundary_right_diagonal_heq A D f b hb)
    simpa only [SimplexData.spanOnePrefixRhs, dgModuleConeBoundaryDegree_negOnePow,
      compose_zero, smul_zero, sub_zero] using H
  · exact dgModuleConeBoundaryLiftA_differential A D f b hb

end SerrePositivity.InfinityCategories
