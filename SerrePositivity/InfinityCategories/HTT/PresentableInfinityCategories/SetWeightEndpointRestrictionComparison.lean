module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsLimitNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationMappingNormalizedOverMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeRestrictionTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.NormalizedConeRestrictionComparison
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality

/-!
概要：G8 の正本の比較の後段を、元の選択のまま独立に表示する。
方針：切断錐から指定極限への辺、宇宙変更、表現可能値の比較を同じ順で合成する。
規約：既存の比較の本文・型・選択を変更しない。
使われ方：G8 の四角形②の全族自然性の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 概要：元の錐の Hom 比較は、同じ正規化した形状制限と固定端点模型で全族として可換。
方針：共通 span 上の切断比較を、既存の正規化した slice・固定端点比較の厳密な自然性へ送る。
規約：終点の表示の違いは等式で移送し、選択した比較は変更しない。
使われ方：G8 の切断制限の全族同型を極限の一意性へ渡す。 -/
def limitConeEndpointComparison_restrictIso {K J E : SSet.{u}} [Quasicategory E]
    (p : J ⟶ E) (q : K ⟶ E) (i : K ⟶ J) (hi : i ≫ p = q)
    (c : JoinCone p) (x : E _⦋0⦌) :
    let f := normalizedConeRestriction p i hi
    let hf := normalizedConeRestriction_projection p i hi
    FunctorIso
      (eqToHom (congrArg (fun t : sliceOver p ⟶ E => Basic.pinchedHom x (t.app _ c))
        hf.symm) ≫ SetWeight.limitConeEndpointComparison (f.app _ c) x)
      (SetWeight.limitConeEndpointComparison c x ≫
        normalizedEndpointConeRestriction p q i hi x) := by
  dsimp only
  let f := normalizedConeRestriction p i hi
  let hf := normalizedConeRestriction_projection p i hi
  have h := FunctorIso.postcomp
    (rightFibrationHomComparison_overMapIso_of_eq (sliceOverProjection p)
      (sliceOverProjection q) f hf c x) (sliceEndpointConeComparison q x)
  have hn := normalizedSliceEndpointComparison_restrict p q i hi x
  change vertexFiberMap (sliceOverProjection p) (sliceOverProjection q) f hf x ≫
    sliceEndpointConeComparison q x = _ at hn
  simp only [Category.assoc] at h
  rw [hn] at h
  simpa only [SetWeight.limitConeEndpointComparison, fixedApexConeHomComparison,
    sliceEndpointConeComparison, Category.assoc] using h.symm

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
