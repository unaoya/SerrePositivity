module
public import SerrePositivity.KST.Fibration.VerdierFullSSquarePrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexStrictification

/-!
概要：指定 Verdier 四角形の下側全二胞体を、元の最大 path による実二胞体へ変形する。
方針：F1 正本の coherent 単体変形を、元の全 S• Kan 像の下側二胞体へ特殊化する。
規約：元の全二胞体と各頂点の恒等縦辺を保持する。共有対角は動くため固定とは主張しない。
使われ方：K-6 c4 の商核の標準合成二胞体との比較。上側との対角整合は別途必要。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 元の指定 Verdier 下側二胞体の、同じ全 S• Kan 像の全単体。 -/
def verdierFullSLowerSimplex : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌ :=
  SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)))

/-- 元の全下側二胞体は Yoneda 表示から厳密に回収される。 -/
theorem verdierFullSLowerSimplex_original :
    SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  SSet.yonedaEquiv.symm_apply_apply _

/-- 元の下側二胞体の Yoneda 表示を、同じ最大 path の二胞体へ送る実三角柱。 -/
def verdierFullSLowerDeformation :
    SSet.Homotopy (SSet.yonedaEquiv.symm (verdierFullSLowerSimplex d))
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexDeformation (verdierFullSLowerSimplex d)

/-- 同じ実三角柱の各縦辺は、元の同じ頂点の恒等全一単体。 -/
theorem verdierFullSLowerDeformation_vertex (x : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierFullSLowerDeformation d) x).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((verdierFullSLowerSimplex d).obj
          ⟨ULift.up (x.down.toOrderHom 0)⟩)) 1 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexDeformation_vertex (verdierFullSLowerSimplex d) x

/-- 同じ下側全二胞体の実変形は、各元の頂点で可逆。 -/
theorem verdierFullSLowerDeformation_pointwise :
    ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (verdierFullSLowerDeformation d) x).toTruncated :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexDeformation_vertex_isInvertible (verdierFullSLowerSimplex d)

/-- 元の下側全二胞体と同じ最大 path 二胞体との、同じ三角柱からの全関手同型。 -/
def verdierFullSLowerDeformationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)))
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d))) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalizationIso (verdierFullSLowerSimplex d)
  exact (congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d))))
      (verdierFullSLowerSimplex_original d)).mp e

end SerrePositivity.KST.Fibration
