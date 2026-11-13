module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSectionsNativeComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeTransformationEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の小さい coherent 空間値図式の、元の全切断を頂点とする native 極限を証明する。
方針：元の全 Hom 比較を全切断への作用へ移し、同じ二比較の同値性を消去する。
規約：任意の小さい底。新たな極限存在や同値性の instance 仮定を要求しない。
使われ方：F1-4 の前層の小さい極限の各点存在を解消する。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
local instance : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSections_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F)

/-- 任意の小さい図式で、元の全切断の錐の同じ native Hom 比較自体が同値。 -/
lemma coherentSectionsConeHomComparison_isQCatEquivalence (z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.fixedApexConeHomComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone F) z) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coherentSectionsConeHomAction_isQCatEquivalence F z).ofFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneSectionsNativeComparisonIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone F) z).symm
  have h' := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentConstantSourceMap_isQCatEquivalence F z).cancel_right h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationMap_isQCatEquivalence F z).cancel_right h'

/-- 元の小さい全切断を頂点とする同じ native な錐は、任意の形状で極限錐。 -/
lemma coherentDiagramSectionsCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone F) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_iff_fixedApexConeHomComparison_homotopyEquivalence _).mpr
  intro z
  exact (coherentSectionsConeHomComparison_isQCatEquivalence F z).isSimplicialHomotopyEquivalence

/-- 任意の小さい coherent 空間値図式に、小さい全切断で表される極限が存在する。 -/
@[kerodon 02VD, kerodon 05QQ]
lemma hasLimit_coherentSpaceDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit F :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone F, coherentDiagramSectionsCone_isLimit F⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "3.3.3.4" (partial := special) "仮定：任意の小さい K と p:K→SpaceInfinity に対し分類束 X を標準の smallLeftUnstraightening p に固定（Lean が強い特殊形）。結論：全切断の Kan 複体そのものを頂点とする錐が極限であり、原典のこの標準分類束の場合の式と一致。任意の分類束への全切断の輸送比較はこの型には含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit
