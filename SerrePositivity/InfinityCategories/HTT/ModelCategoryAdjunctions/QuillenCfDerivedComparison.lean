module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfLeftOrdinaryComparison
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfRightOrdinaryComparison
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfDerivedLimits

/-!
概要：単体的 Quillen 随伴の元の cf nerve 上の ∞ 随伴と右導来関手の極限保存を集約する。
方針：同じ標準単位の随伴に、両側の通常置換比較と任意 coherent 図式の極限保存を結ぶ。
規約：固定 SM7 と豊穣随伴の合成互換を明示入力。使われ方：HTT 5.2.4.6、Sp、E2b。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section

open HomotopicalAlgebra

variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
  {L : C ⥤ D} (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))
  (e : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EnrichedAdjunctionHomComposition R adj)
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor] [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]


variable (cofC : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))
include fibD e SC SD cofC in
/-- 元の cf 対応圏の両側輸送、標準単位を持つ ∞ 随伴、元の通常置換との比較と極限保存。 -/
lemma quillenCfDerivedAdjunctionWithComparisons_exists :
    letI := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SC
    letI := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SD
    ∃ H : SSet.Homotopy (𝟙 (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)))
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC),
      ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD)
        (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC),
        a.unitHom = SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) ∧
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
          (nerveMap (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftReplacementFunctor R adj fibD) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) ≫
            _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD)) ∧
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
          (nerveMap (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightReplacementFunctor R adj cofC) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) ≫
            _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC)) ∧
        ∀ (K : SSet.{max u v}) (p : K ⟶ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D))
          (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c →
            _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC) c) := by
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SC
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SD
  obtain ⟨H, a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfDerivedAdjunction_exists R adj fibD e SC SD cofC
  exact ⟨H, a, ha,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cartesianFibration R adj SC SD cofC,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cocartesianFibration R adj fibD e SC SD,
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived_ordinaryComparison R adj fibD e SC SD,
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived_ordinaryComparison R adj SC SD cofC,
    fun _ _ c hc ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCone_isLimit_of_adjunction a c hc⟩

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.4.26" (partial := stronger-hyp) "仮定：二つの単体モデル圏と豊穣の随伴・pushout-product・関手的置換（Lean が強い：一般の組合せ的モデル圏間の左 Quillen 関手より限定。モデル圏 instance が必要）。結論：cf nerve 間に誘導される左導来関手が左随伴（Lean が弱い：全ての組合せ的模型の局所化との同定は型にない）。"] _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfDerivedAdjunctionWithComparisons_exists
attribute [cite HA "1.3.4.27" (partial := stronger-hyp) "仮定：単体モデル圏間の豊穣 Quillen 随伴に関手的置換を与える（Lean が強い：一般の組合せ的モデル圏を直接扱わず、モデル圏 instance が必要）。結論：右導来関手と随伴の存在、および通常の置換から作った関手との比較（制限した模型で一致）。"] _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfDerivedAdjunctionWithComparisons_exists
attribute [cite HTT "5.2.4.7" (partial := stronger-hyp) "仮定：単体的 Quillen 随伴（Lean が強い：固定 SM7・合成互換と両側の関手的分解を指定し、ModelCategory instance なしの具体例を残す）。結論：同じ cf nerve 間の左右導来関手、標準単位を持つ全 ∞ 随伴、および通常の cf 置換関手の nerve との FunctorIso（置換を用いた本文の導来関手の比較に一致）。本行では SSet の未証明 Kan–Quillen 入力を instance の証拠としない。"] _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfDerivedAdjunctionWithComparisons_exists
