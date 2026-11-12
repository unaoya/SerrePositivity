module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaPresheafFamilyComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteFamilyConeUnitComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentTransformationKanCocones

/-!
概要：元の P_Σ の族から供給した同じ評価極限錐の全脚を、元の積脚と頂点比較へ照合する。
方針：元の同じ slice 内の比較を使い、同じ実際の脚を長辺とする全三角形を評価する。
規約：元の族・有限極限錐・全脚・指定単位を保持。底の quasicategory 性は不要。
使われ方：sifted 余極限の元の全脚・全余錐を保つ有限積比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
  {J : Type u} [Finite J] [Nonempty J] {p : nerve (Discrete J) ⟶ C.op}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexEvaluation r (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift c))
local notation "G" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFiniteEvaluationFamily r (p := p)
local notation "d" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFamilyComparisonCone r c
local notation "hd" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFamilyComparisonCone_isLimit r c hc
local notation "hv" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFamilyComparisonCone_vertex r c

/-- 元の同じ slice 比較の代表を全脚と共有する、元の頂点比較変換。 -/
def sigmaPresheafConeApexTransformation :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeApexTransformation G d hd A hv

/-- 元の評価全錐の実際の脚の全一単体を保持する coherent 変換。 -/
def sigmaPresheafConeLegTransformation (j : J) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegTransformation G d A hv j

omit [Finite J] [Nonempty J] in
/-- 元の脚の変換から読み戻した辺は、元の評価全錐の同じ native 脚の全一単体。 -/
lemma sigmaPresheafConeLegTransformation_edge (j : J) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (sigmaPresheafConeLegTransformation r c j)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafEvaluationCone r c)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))).edge := by
  rw [sigmaPresheafConeLegTransformation, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegTransformation,
    show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalConeLeg G d A hv j)) = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalConeLeg G d A hv j from
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _]
  rfl

/-- 元の実際の各評価脚を長辺とする、元の頂点比較と積脚の全変換三角形。 -/
def sigmaPresheafConeLegTriangle (j : J) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeLegTransformationTriangle G d hd A hv j

/-- 元の同じ三角形の長辺は、元の評価全錐の実際の脚。 -/
lemma sigmaPresheafConeLegTriangle_diagonal (j : J) :
    (sigmaPresheafConeLegTriangle r c hc j).diagonal =
      sigmaPresheafConeLegTransformation r c j := rfl

/-- 元の各脚の全空間作用は、指定単位の後で元の頂点比較と元の積脚の合成に同型。 -/
def sigmaPresheafConeLegUnitIso (j : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (G j)
      (sigmaPresheafConeLegTransformation r c j) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit (G j))
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)
        (sigmaPresheafConeApexTransformation r c hc) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G) (G j)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyProductLegTransformation G j) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit (G j)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegUnitIso G d hd A hv j

/-- 元の各評価脚の Kan 像の全余錐作用は、同じ脚と指定単位の三角形の余錐に同型。 -/
def sigmaPresheafConeLegNativeUnitCoconeIso (j : J)
    (T : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitTriangle A (G j)
      (sigmaPresheafConeLegTransformation r c j)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationKanNativeUnitCoconeIso A (G j)
    (sigmaPresheafConeLegTransformation r c j) T

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
