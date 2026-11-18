module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FibrantSourceReducedFirst
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameIndexAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ArrowMapComposition

/-!
概要：固定 source frame の実二列 roof 比較を全標的で自然な一つの族にする。
方針：元の要素圏の作用と元の hammock の後合成を関手に束ねる。
規約：同じ augmentation・全単体・全標的射を保持する。
使われ方：right frame との混合比較から全局所化 Hom 族への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.SerrePositivity.Reedy
open _root_.SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X : C)

/-- 概要：同じ元の hammock Hom の全標的関手。
方針：元の射の一定単体による後合成を使う。
規約：余極限の元の豊穣合成。使われ方：全標的の同じ実 roof 族。 -/
def hammockHomFamily : C ⥤ SSet.{max u v} where
  obj Y := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f)
  map_id Y := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap_identity, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap_unit]
  map_comp f g := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composeUnitMaps_arrowMap]

variable [ModelCategory C] {X} (q : CofibrantResolution (C := C) simplex X)

/-- 概要：元の source Hom の全要素 nerve の全標的関手。
方針：同じ元の後合成を全要素圏へ送る。
規約：Hom の宇宙だけを揃える。使われ方：実二列 roof 比較の始域。 -/
def sourceFrameElementsFamily : C ⥤ SSet.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj ⋙
    { obj := fun K => nerve (ULiftHom.{max u v} K.Elementsᵒᵖ)
      map := fun f => nerveMap
        (ULiftHom.down.{0, v, max u v} ⋙ f.mapElements.op ⋙ ULiftHom.up) }

/-- 概要：同じ元の全 roof 比較は全標的の一つの自然変換。
方針：二列 roof の元の後合成照合を自然性に使う。
規約：同じ実比較射。使われ方：全図式の自然性の保持。 -/
def sourceRoofFamily : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameElementsFamily q ⟶
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.hammockHomFamily (weakEquivalences C) X where
  app Y := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.resolutionLeftRoofColimitMap q Y
  naturality _ _ f := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap_postcompose (weakEquivalences C) q.obj q.augmentation
    q.augmentation_weakEquivalence (fun a => q.homotopicallyConstant a) f

/-- 概要：同じ全要素 nerve の終端 augmentation を全標的で束ねる。
方針：既存の宇宙持ち上げ augmentation の自然性を使う。
規約：元の全単体と終端制限。使われ方：元の Hom との全自然比較。 -/
def sourceFrameElementsAugmentation : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameElementsFamily q ⟶
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj ⋙ SSet.uliftFunctor.{max u v, v} where
  app Y := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation.{v, max u v}
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y)
  naturality _ _ _ := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_naturality _

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
