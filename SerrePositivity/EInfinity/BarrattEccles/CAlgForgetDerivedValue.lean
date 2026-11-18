module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgForgetDerived
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SemifreeResolutionValue

/-!
# 元の全 E 代数の U の実値と同じ底の複体

概要：既存 CAlg_R の元の頂点の忘却値を同じ半自由複体に比較する。
方針：全源比較と元の頂点同型を使い、元の置換の同じ augmentation を合成する。
規約：元の全代数に cofibrancy を仮定しない。
使われ方：離散入力と G1′ の実忘却界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma cofibrantAlgebraUnderlyingDerivedSource_vertex
    (X : (cofibrantAlgebraRelativeCategory A).category) :
    (cofibrantAlgebraUnderlyingDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A
        ((cofibrantAlgebraDKForget A).obj X)) := by
  have h : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)).app (Opposite.op ⦋0⦌)
      ((nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A)).app (Opposite.op ⦋0⦌)
        ((cofibrantAlgebraForgetNerve A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((cofibrantAlgebraDKForget A).obj X) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := A) (D := Complex A)).injective
    rfl
  change (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)).app (Opposite.op ⦋0⦌)
      ((nerveMap (_root_.SerrePositivity.ComplexLimits.complexToClosed A)).app (Opposite.op ⦋0⦌)
        ((cofibrantAlgebraForgetNerve A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)))) = _
  rw [h, _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity_vertex]

def cAlgForgetDerived_sourceValueVertexIso
    (X : (cofibrantAlgebraRelativeCategory A).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
      ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A
        ((cofibrantAlgebraDKForget A).obj X))) :=
  cAlgForgetDerived_sourceVertexIso A X ≪≫ eqToIso
    (congrArg HomotopyCategory.mk (cofibrantAlgebraUnderlyingDerivedSource_vertex A X))

def cAlgForgetDerivedValue (X : (operad A).Algebra) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A :=
  _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A
    ((cofibrantAlgebraDKForget A).obj ((cofibrantAlgebraDKReplacement A).obj X))

def cAlgForgetDerivedValueAugmentation (X : (operad A).Algebra) :
    (cAlgForgetDerivedValue A X).val ⟶ X.carrier :=
  _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A
    ((cofibrantAlgebraDKForget A).obj ((cofibrantAlgebraDKReplacement A).obj X)) ≫
      (framedLimitProbeComparison A X).hom

lemma cAlgForgetDerivedValueAugmentation_quasiIso (X : (operad A).Algebra) :
    QuasiIso (cAlgForgetDerivedValueAugmentation A X) := by
  have hq : QuasiIso (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A
      ((cofibrantAlgebraDKForget A).obj ((cofibrantAlgebraDKReplacement A).obj X))) :=
    _root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation_quasiIso A _
  have hp := framedLimitProbeComparison_quasiIso A X
  change QuasiIso (_ ≫ (framedLimitProbeComparison A X).hom)
  infer_instance

def cAlgForgetDerived_valueVertexIso (X : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌) (cAlgVertex A X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (cAlgForgetDerivedValue A X)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (cAlgLocalizationSource_vertexIso A ((cofibrantAlgebraDKReplacement A).obj X))
    (cAlgForgetDerived A)).symm ≪≫
      cAlgForgetDerived_sourceValueVertexIso A ((cofibrantAlgebraDKReplacement A).obj X)

end SerrePositivity.EInfinity.BarrattEccles
