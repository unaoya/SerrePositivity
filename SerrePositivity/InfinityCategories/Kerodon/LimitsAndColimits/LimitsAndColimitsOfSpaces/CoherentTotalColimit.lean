module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoconeFiberColimitCriterion
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTotalCoconePre

/-!
概要：小さい底上の任意の coherent 空間値図式の全空間 Kan 模型が元の余錐の native な余極限。
方針：元の単位比較による全 fiber 標的への前合成同値を元の全 Hom の判定へ入力する。
規約：元の図式と構成済みの余錐を保持し、filtered 性を要求しない。
使われ方：一般 coherent filtered 余極限と有限極限の交換、Ind の生成。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {B : SSet.{u}}

/-- 概要：構成済み全空間余錐そのものが元の coherent 図式の native な余極限。
方針：元の単位から証明した全 fiber 前合成同値に、元の全 Hom の余極限判定を適用する。
規約：図式・余錐を選び直さない。使われ方：全空間 Kan 模型の普遍性。 -/
lemma coherentDiagramTotalCocone_isColimit
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isColimitCone_of_coconeFiberMap_pre_homotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalCoconeFiber_pre_homotopyEquivalence F)

/-- 概要：小さい底上の任意の coherent 空間値図式は native な余極限を持つ。
方針：元の全空間余錐とその証明済みの普遍性を供給する。
規約：strict 図式への置換を仮定しない。使われ方：一般 coherent 余極限の存在。 -/
lemma hasColimit_coherentSpaceDiagram
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F :=
  ⟨_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F, coherentDiagramTotalCocone_isColimit F⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "3.3.4.6" (partial := special) "仮定：任意の小さい K と p:K→SpaceInfinity に対し分類束を smallLeftUnstraightening p、余極限を coherentDiagramTotalCocone p の頂点に固定（Lean が強い特殊形）。結論：元の全空間からこの余極限への標準単位が弱ホモトピー同値（一致）。任意に指定された分類束・余極限への比較はこの型には含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramTotalCocone_isColimit
