module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentReverseCompositionPrismPost
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentReverseCompositionBase
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalPrismPostNaturality
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalPrismBoundaryEquality

/-!
概要：元の反転合成 prism の指定対角比較を、同じ終域射の像の比較へ値まで移す。
方針：同じ底上の後合成自然性と、元の実 prism 全体の厳密自然性を合成する。
規約：元の指定比較・全 Hom を保持。使われ方：二射の指定評価比較の合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ A B : C, KanComplex (SimplicialCategory.sHom A B)] (X Y Z W : C) (g : Z ⟶ W)
local notation "p" => sliceUnderProjection
  (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (coherentNerveVertex Z)))
local notation "q" => sliceUnderProjection
  (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (coherentNerveVertex W)))
local notation "F" => coherentReverseSlicePost g
local notation "hF" => coherentReverseSlicePost_projection g
local notation "s" => fst _ _ ≫ coherentReverseSliceFiberComparison Y Z
local notation "t" => coherentReverseHomComposition X Y Z ≫
  coherentReverseSliceFiberComparison X Z
local notation "H" => coherentCompositionReversePrism X Y Z
local notation "Γ" => coherentReverseCompositionBase X Y Z
local notation "h₀" => coherentReverseCompositionBase_zero X Y Z
local notation "h₁" => coherentReverseCompositionBase_one X Y Z
local notation "H₀" => coherentCompositionReversePrism_zero X Y Z
local notation "H₁" => coherentCompositionReversePrism_one X Y Z
local notation "Hp" => coherentCompositionReversePrism_projection X Y Z
local notation "c" => intervalMappingCurryOfEndpoints Γ h₀ h₁
local notation "k₀" => vertexFiberMap p q F hF (SSet.opObjEquiv.symm (coherentNerveVertex Y))
local notation "k₁" => vertexFiberMap p q F hF (SSet.opObjEquiv.symm (coherentNerveVertex X))
local notation "U" => diagonalUniversalPrism p s c
local notation "R" =>
  (Δ[1] ◁ (CategoryTheory.Functor.map SSet.opFunctor
    (CategoryTheory.Functor.map SSet.uliftFunctor (eHomWhiskerLeft SSet Y g)) ⊗ₘ
      𝟙 (CategoryTheory.Functor.obj SSet.opFunctor
        (CategoryTheory.Functor.obj SSet.uliftFunctor (SimplicialCategory.sHom X Y))))) ≫
        coherentCompositionReversePrism X Y W

/-- 元の全反転合成 prism の指定比較は、後合成の像の元の指定比較へ厳密に貼れる。 -/
lemma coherentCompositionReverseSpecified_post :
    HEq ((leftFibrationPrism_diagonalTransportIso p s t Γ h₀ h₁ H H₀ H₁ Hp).postcomp k₁ ≪≫
      leftFibrationPrism_diagonalTransportIso q (s ≫ k₀)
        (diagonalFiberTransport p s c ≫ k₁) Γ h₀ h₁ (U ≫ F)
        (diagonalPrismPost_start p q F hF U s (diagonalUniversalPrism_start p s c))
        (diagonalPrismPost_finish p q F hF U (diagonalFiberTransport p s c)
          (diagonalUniversalPrism_finish p s c))
        (diagonalPrismPost_projection p q F hF U Γ
          ((diagonalUniversalPrism_projection p s c).trans
            (intervalMappingUncurry_curryOfEndpoints Γ h₀ h₁))))
      (leftFibrationPrism_diagonalTransportIso q (s ≫ k₀) (t ≫ k₁) Γ h₀ h₁ R
        (by rw [← coherentCompositionReversePrism_post g];
            exact diagonalPrismPost_start p q F hF H s H₀)
        (by rw [← coherentCompositionReversePrism_post g];
            exact diagonalPrismPost_finish p q F hF H t H₁)
        (by rw [← coherentCompositionReversePrism_post g];
            exact diagonalPrismPost_projection p q F hF H Γ Hp)) := by
  have h := leftFibrationPrism_diagonalTransportIso_post p q F hF s t Γ h₀ h₁ H H₀ H₁ Hp
  refine (heq_of_eq h).trans ?_
  exact diagonalTransportIso_heq_of_boundary q (s ≫ k₀) (s ≫ k₀) (t ≫ k₁) (t ≫ k₁)
    Γ Γ h₀ h₁ h₀ h₁ (H ≫ F) R
    (diagonalPrismPost_start p q F hF H s H₀) _
    (diagonalPrismPost_finish p q F hF H t H₁) _
    (diagonalPrismPost_projection p q F hF H Γ Hp) _ rfl rfl
    (coherentCompositionReversePrism_post g)

end SerrePositivity.InfinityCategories.F2
