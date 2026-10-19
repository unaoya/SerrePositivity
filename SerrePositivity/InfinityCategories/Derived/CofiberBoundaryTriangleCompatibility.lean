module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryLegCompatibility
public import SerrePositivity.InfinityCategories.Derived.SpanTwoPrefixTransport

/-! # 標準 cofiber 境界の三角形側の微分条件

概要：型付き三角形残差の微分を共通の後続・A 側右辺と各脚の右辺で表す。
方針：生の三角形 Bianchi を Hom 座標へ移し、標準ホモトピーを代入する。
規約：任意の非有界複体。使われ方：D7 の六成分線形系の最後の整合条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 概要：r_AB の微分は標準ホモトピーと二つの脚側右辺の三項の符号付き和。
方針：零未知データの三角形 Bianchi に標準余錐の各成分を代入する。
規約：右側では零ホモトピーの項は消える。使われ方：六成分線形系の整合条件。 -/
lemma cofiberBoundaryRhsAB_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    δ (cofiberBoundaryDegree n) (cofiberBoundaryDegree n + 1)
        (cofiberBoundaryRhsAB f g b hb) =
      ((n : ℤ) + 1).negOnePow •
        ((mappingCone.inl (cofiberDifference f g)).comp (cofiberBoundaryRhs0 f g b hb)
          (by omega) + cofiberBoundaryRhsA f g b hb -
          (Cochain.ofHom f).comp (cofiberBoundaryRhsB f g b hb)
            (zero_add (cofiberBoundaryDegree n + 1))) := by
  have H := SimplexData.span_twoPrefix_differential_of_heq (A := S) (D := Complex S)
    (cofiberBoundaryLeftBase f g b)
    (spanBoundaryLeftData_equation (sliceUnderUncurry b) _)
    (spanBoundaryLeftZeroData_unknownHom (sliceUnderUncurry b))
    (cofiberCosliceBoundary_left_A f g b hb)
    (cofiberCosliceBoundary_left_apex f g b hb)
    (cofiberCosliceBoundary_left_B f g b hb) rfl
    (by dsimp only [cofiberBoundaryDegree]; omega)
    (cofiberBoundaryRhs0 f g b hb) (cofiberBoundaryRhsB f g b hb)
    (cofiberBoundaryRhsA f g b hb) (cofiberBoundaryRhsAB f g b hb)
    (Cochain.ofHom f) (mappingCone.inl (cofiberDifference f g))
    (cofiberBoundaryRhs0_heq f g b hb).symm (cofiberBoundaryRhsB_heq f g b hb).symm
    (((cofiberBoundaryLeftBase f g b).spanTwoPrefixFirstRhs_heq).trans
      (cofiberBoundaryRhsA_heq f g b hb).symm)
    (cofiberBoundaryRhsAB_heq f g b hb).symm
    (cofiberCosliceBoundary_left_span_heq f g b hb)
    (cofiberCosliceBoundary_left_homotopy_heq f g b hb)
  change δ _ _ (cofiberBoundaryRhsAB f g b hb) = _ at H
  simpa only [Checks.complex_compose, Cochain.zero_comp, zero_add] using H

/-- 概要：r_AC の微分は標準ホモトピーと二つの脚側右辺の三項の符号付き和。
方針：零未知データの三角形 Bianchi に標準余錐の各成分を代入する。
規約：右側では零ホモトピーの項は消える。使われ方：六成分線形系の整合条件。 -/
lemma cofiberBoundaryRhsAC_differential {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    δ (cofiberBoundaryDegree n) (cofiberBoundaryDegree n + 1)
        (cofiberBoundaryRhsAC f g b hb) =
      ((n : ℤ) + 1).negOnePow •
        (cofiberBoundaryRhsA f g b hb -
          (Cochain.ofHom g).comp (cofiberBoundaryRhsC f g b hb)
            (zero_add (cofiberBoundaryDegree n + 1))) := by
  have H := SimplexData.span_twoPrefix_differential_of_heq (A := S) (D := Complex S)
    (cofiberBoundaryRightBase f g b)
    (spanBoundaryRightData_equation (sliceUnderUncurry b) _)
    (spanBoundaryRightZeroData_unknownHom (sliceUnderUncurry b))
    (cofiberCosliceBoundary_right_A f g b hb)
    (cofiberCosliceBoundary_right_apex f g b hb)
    (cofiberCosliceBoundary_right_C f g b hb) (cofiberBoundaryTarget_right_eq f g b)
    (by dsimp only [cofiberBoundaryDegree]; omega)
    (cofiberBoundaryRhs0 f g b hb) (cofiberBoundaryRhsC f g b hb)
    (cofiberBoundaryRhsA f g b hb) (cofiberBoundaryRhsAC f g b hb)
    (Cochain.ofHom g) ((0 : Cochain A (pushoutCofiber f g) (-1)))
    (cofiberBoundaryRhs0_heq_right f g b hb).symm (cofiberBoundaryRhsC_heq f g b hb).symm
    (((cofiberBoundaryRightBase f g b).spanTwoPrefixFirstRhs_heq).trans
      (cofiberBoundaryRhsA_heq_right f g b hb).symm)
    (cofiberBoundaryRhsAC_heq f g b hb).symm
    (cofiberCosliceBoundary_right_span_heq f g b hb)
    (cofiberCosliceBoundary_right_homotopy_heq f g b hb)
  change δ _ _ (cofiberBoundaryRhsAC f g b hb) = _ at H
  simpa only [Checks.complex_compose, Cochain.zero_comp, zero_add] using H

end SerrePositivity.InfinityCategories
