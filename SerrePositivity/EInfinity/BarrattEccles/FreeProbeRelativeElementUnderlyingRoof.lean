module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementSourceRoof
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantColumnUnderlyingHom
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeElementDerivedUnitTriangle
/-! 概要：同じ相対自由列の忘却後の全屋根を元の複体屋根へ回収する。
方針：元の全 augmentation・評価の回収を逆と合成へ拡張する。
規約：元の全要素圏と同じ複体射を保持する。
使われ方：実 U の全屋根と元の導来単位三角形の接合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalClosed _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：相対列の全 augmentation の忘却像は元の複体 augmentation。
方針：元の cofibrant 列の全 Hom 回収を使う。
規約：全パラメータを保持。使われ方：同じ全屋根の左脚。 -/
lemma freeProbeRelativeElementUnderlyingAugmentation_arrow :
    let T := (hoFunctor.map ((pre (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj))).app
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor
    Arrow.mk (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso (cofibrantAlgebraUnderlyingDerivedSource A)
      (freeProbeRelativeElementColumn A X B) (freeProbeRelativeElementAugmentation A X B)
      (freeProbeRelativeElementAugmentation_underlying_invertible A X B)).hom =
    Arrow.mk (T.map (freeProbeElementUnderlyingAugmentationIso A X B.obj).hom) := by
  dsimp only
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso_hom]
  exact cofibrantColumnUnderlyingHom_arrow A (freeProbeElementCofibrantAugmentation A X B)

/-- 概要：相対列の全評価の忘却像は元の複体評価。
方針：元の cofibrant 列の全 Hom 回収を使う。
規約：全パラメータを保持。使われ方：同じ全屋根の右脚。 -/
lemma freeProbeRelativeElementUnderlyingEvaluation_arrow :
    let T := (hoFunctor.map ((pre (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj))).app
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor
    Arrow.mk (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom (cofibrantAlgebraUnderlyingDerivedSource A)
      (freeProbeRelativeElementEvaluation A X B)) =
    Arrow.mk (T.map (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHom A
      (Functor.whiskerRight (freeProbeElementColumnEvaluation A X B.obj)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A))))) := by
  dsimp only
  exact cofibrantColumnUnderlyingHom_arrow A (freeProbeElementCofibrantEvaluation A X B)

/-- 概要：同じ相対列の全忘却屋根は元の複体屋根の全制限。
方針：全左脚の逆と全右脚の Arrow 比較を合成する。
規約：元の同じ全 K と両端表示を保持。使われ方：元の単位三角形への接合。 -/
lemma freeProbeRelativeElementUnderlyingRoof_arrow :
    let T := (hoFunctor.map ((pre (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj))).app
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor
    Arrow.mk ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso (cofibrantAlgebraUnderlyingDerivedSource A)
      (freeProbeRelativeElementColumn A X B) (freeProbeRelativeElementAugmentation A X B)
      (freeProbeRelativeElementAugmentation_underlying_invertible A X B)).inv ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom (cofibrantAlgebraUnderlyingDerivedSource A)
        (freeProbeRelativeElementEvaluation A X B)) =
    Arrow.mk (T.map (freeProbeElementUnderlyingRoof A X B.obj)) := by
  dsimp only
  let T := (hoFunctor.map ((pre (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj))).app
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor
  have hp := freeProbeRelativeElementUnderlyingAugmentation_arrow A X B
  have hi := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.inv_arrow_eq _ _ hp
  have hi' : Arrow.mk (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso (cofibrantAlgebraUnderlyingDerivedSource A)
      (freeProbeRelativeElementColumn A X B) (freeProbeRelativeElementAugmentation A X B)
      (freeProbeRelativeElementAugmentation_underlying_invertible A X B)).inv =
      Arrow.mk (T.map (freeProbeElementUnderlyingAugmentationIso A X B.obj).inv) := by
    simpa only [← Functor.map_inv, IsIso.Iso.inv_hom] using hi
  change _ = Arrow.mk (T.map ((freeProbeElementUnderlyingAugmentationIso A X B.obj).inv ≫ _))
  rw [Functor.map_comp]
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.comp_arrow_eq _ _ _ _ hi'
    (freeProbeRelativeElementUnderlyingEvaluation_arrow A X B)

end SerrePositivity.EInfinity.BarrattEccles
