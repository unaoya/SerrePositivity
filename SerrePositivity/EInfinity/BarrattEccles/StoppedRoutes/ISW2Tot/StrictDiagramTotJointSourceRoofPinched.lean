module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceRoofComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.AsSmallHammockHomFamily
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.KanHomFamilyOpposite
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockPinchedSimplexValue

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の同じroof比較を、同じ全モデル局所化頂点のpinched Homへ送る。
方針：元のAsSmall同型・同じEx∞単位・元の全単体のpinched比較を合成する。
規約：元の制限写像と弱同値のfiber単位を記録し、native比較の同値性はまだ主張しない。
使われ方：同じfiber制限を元の固定始域のroof比較へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.CategoryTheory.Limits
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A]
local instance jointSourceRoofPinchedModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointSourceRoofPinchedFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の同じ基準roof比較の始域を、同じ全モデル相対圏の対象として記録する。 -/
abbrev strictBETotJointRoofSourceObject (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).category :=
  modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A (AsSmall.down.obj P).1.unop)

/-- 元の同じ右置換を、同じ全モデル相対圏の対象として記録する。 -/
abbrev strictBETotJointRoofTargetObject (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).category :=
  modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
    ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2)

/-- 元の同じroof比較を、同じAsSmall同型とEx∞単位で元のKan hammock Homへ送る。 -/
def strictBETotJointSourceRoofKanComparison (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      exInfinity.obj
        (SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
          (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).weakEquivalences
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofSourceObject A P) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetObject A P)) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofComparison A P ≫
    (_root_.SerrePositivity.EInfinity.Hammock.AsSmallComparison.colimitIso (weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A (AsSmall.down.obj P).1.unop)
      ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2)).hom ≫
        exInfinityUnit.app _

/-- 元の同じ実roof比較の弱同値性を、同じAsSmall同型とEx∞単位で移す。 -/
theorem strictBETotJointSourceRoofKanComparison_weak (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofKanComparison A P) := by
  have h₀ := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofComparison_isWeakHomotopyEquivalence A P
  have h₁ := (isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.EInfinity.Hammock.AsSmallComparison.colimitIso (weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A (AsSmall.down.obj P).1.unop)
      ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2))).isWeakHomotopyEquivalence
  exact h₀.comp (h₁.comp (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.kanHomFamilyUnit_isWeakHomotopyEquivalence _))

/-- 元の全標的のAsSmall比較の同じ成分と、元のEx∞単位の厳密な三角形。 -/
theorem strictBETotJointSourceRoofKanComparison_unit (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofComparison A P ≫ exInfinityUnit.app _ ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.asSmallKanHammockHomFamilyMap (weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A (AsSmall.down.obj P).1.unop)).app
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetObject A P) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofKanComparison A P := by
  exact congrArg (fun f => _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofComparison A P ≫ f)
    (exInfinityUnit.naturality
      (_root_.SerrePositivity.EInfinity.Hammock.AsSmallComparison.colimitIso (weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2)).hom).symm

/-- 元の基準roof比較を、同じhammock局所化頂点のpinched Homへ送る実射。 -/
def strictBETotJointSourceRoofPinchedComparison (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).app (Opposite.op ⦋0⦌)
            (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofSourceObject A P)))
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap
          (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).app (Opposite.op ⦋0⦌)
            (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetObject A P))) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofKanComparison A P ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofSourceObject A P) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetObject A P)

/-- 同じ元の基準roofから同じ局所化頂点のpinched Homへの実射は弱同値。 -/
theorem strictBETotJointSourceRoofPinchedComparison_weak (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofPinchedComparison A P) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofKanComparison_weak A P).comp
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap_weak
      (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofSourceObject A P) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetObject A P))

/-- 元の全単体の値は、同じ元のKan hammock Homのcoherent単体そのもの。 -/
theorem strictBETotJointSourceRoofPinchedComparison_app_val (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockPinchedValueFormula
      (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofSourceObject A P) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetObject A P)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofKanComparison A P) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap_value_family
    (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofSourceObject A P) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetObject A P) _
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
