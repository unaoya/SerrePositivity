module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementUnderlyingRoof
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeElementUnderlyingRoofFamily
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantUnderlyingConstantRestriction
/-!
概要：元の CAlg_R 全族の実 U 像を同じ複体屋根の定値族に比較する。
方針：元の全源比較の定値制限と Hom 宇宙回収を全 Arrow として合成する。
規約：同じ U・全パラメータ・元の両端同型の二射を保持する。
使われ方：元の単位成分の全屋根三角形を標準単位比較へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalClosed SimplicialLocalization
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.FrameHom
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：実 U の元の全 pinched 族は同じ複体屋根の全定値端点輸送。
方針：元の全屋根回収と全源同型の二つの定値制限を合成する。
規約：全族と元の端点比較を保持。使われ方：標準単位の全族三角形の出口。 -/
lemma freeProbeRelativeElementPinched_forget_family_arrow :
    let K := nerve (freeProbeRelativeElementIndex A X B)
    let d := MixedNerve.down (freeProbeElementIndex A X B.obj)
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (freeProbeRelativeElementPinchedMap A X B ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (cAlgForgetDerived A) _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K
      (cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp d (freeProbeElementUnderlyingRoofFamily A X B.obj) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (cofibrantForgetOrdinaryVertexIso A B).inv) := by
  dsimp only
  let J := freeProbeRelativeElementIndex A X B
  let T := (hoFunctor.map ((pre (MixedNerve.down (freeProbeElementIndex A X B.obj))).app
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A))).toFunctor
  let eS := (cAlgForgetDerived_sourceIso A).precomp
    (nerveMap ((Functor.const J).obj (freeProbeRelativeElementSource A X)))
  let eB := (cAlgForgetDerived_sourceIso A).precomp
    (nerveMap ((Functor.const J).obj (ULiftHom.objUp.{u + 1, u + 1} B)))
  let r := (NerveColumn.augmentationIso (cofibrantAlgebraUnderlyingDerivedSource A)
    (freeProbeRelativeElementColumn A X B) (freeProbeRelativeElementAugmentation A X B)
    (freeProbeRelativeElementAugmentation_underlying_invertible A X B)).inv ≫
      NerveColumn.hom (cofibrantAlgebraUnderlyingDerivedSource A)
        (freeProbeRelativeElementEvaluation A X B)
  have hs := cofibrantForgetOrdinaryRestriction_hom_arrow A
    (freeProbeElementCofibrantSource A X) J
  have hr : Arrow.mk r = Arrow.mk (T.map (freeProbeElementUnderlyingRoofFamily A X B.obj)) :=
    (freeProbeRelativeElementUnderlyingRoof_arrow A X B).trans
      (congrArg T.mapArrow.obj (freeProbeElementUnderlyingRoofFamily_arrow A X B.obj)).symm
  let eB' := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantVertexIso (nerve J) (cofibrantForgetOrdinaryVertexIso A B)
  have hb : Arrow.mk eB.hom = Arrow.mk eB'.hom :=
    cofibrantForgetOrdinaryRestriction_hom_arrow A B J
  have hb' : Arrow.mk eB.inv = Arrow.mk eB'.inv := by
    simpa only [IsIso.Iso.inv_hom] using RoofPrefix.inv_arrow_eq eB.hom eB'.hom hb
  have h := RoofPrefix.comp_arrow_eq _ _ _ _
    (RoofPrefix.comp_arrow_eq eS.hom r _ _ hs hr) hb'
  exact (freeProbeRelativeElementPinched_forget_underlying_arrow A X B).trans
    (by simpa only [r, eS, eB, eB', _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantVertexIso, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp,
      Category.assoc] using h)

end SerrePositivity.EInfinity.BarrattEccles
