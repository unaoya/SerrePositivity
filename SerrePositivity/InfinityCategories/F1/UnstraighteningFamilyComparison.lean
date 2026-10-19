module

public import SerrePositivity.InfinityCategories.F1.SmallCoherentFamilyRecovery
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningMappingChoice
public import SerrePositivity.InfinityCategories.F1.TransportPrismLiftSpace
public import SerrePositivity.InfinityCategories.F1.FunctorParameterizedPrismNaturality
public import SerrePositivity.InfinityCategories.F1.UnstraighteningSourceFamilyComparison

/-!
概要：任意のパラメーター族の pointed な prism を実際の写像空間比較と結ぶ。
方針：普遍的な持ち上げを制限し共通の始点と底を保つ延長空間で比較する。
規約：全パラメーターでの関手同型を与える。
使われ方：復元した族が比較射の右逆を与えることの検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：pointed な prism の終点の族は写像空間比較の像と関手同型。
方針：普遍的な lift の制限と指定した prism を同じ始点・底の延長空間で比較する。
規約：底・パラメーターの小ささを要求しない。
使われ方：coherent な族の復元と既存の比較射の全体での整合性。 -/
def unstraighteningFamilyComparisonIso {B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (t : K ⟶ leftUnstraighteningTransformationSpace F G)
    (f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G =
      fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ leftUnstraightening F) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hw₀ : (prismEndpoint 0 (leftUnstraightening F) ▷ K) ≫ W =
      fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F)
    (hw₁ : (prismEndpoint 1 (leftUnstraightening F) ▷ K) ≫ W =
      f ≫ pullback.fst pointedSpaceProjection G)
    (hwp : W ≫ pointedSpaceProjection = ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K) ≫
      functorParameterizedPrism (intervalMappingUncurry t)) :
    FunctorIso (t ≫ leftUnstraighteningMappingSpaceMap F G) (relativeFunctorCurry f hf) := by
  have e := unstraighteningSourceFamilyComparisonIso F G (leftUnstraighteningProjection F)
    (𝟙 (leftUnstraightening F)) (Category.id_comp _) t f hf W hw₀ hw₁ hwp
  change FunctorIso ((t ≫ leftUnstraighteningMappingSpaceMap F G) ≫
    relativeFunctorOverPre (leftUnstraighteningProjection G)
      (𝟙 (Over.mk (leftUnstraighteningProjection F)))) (relativeFunctorCurry f hf) at e
  rw [relativeFunctorOverPre_id] at e
  change FunctorIso ((t ≫ leftUnstraighteningMappingSpaceMap F G) ≫
    𝟙 (relativeFunctorSpace (leftUnstraighteningProjection G) (leftUnstraighteningProjection F)))
    (relativeFunctorCurry f hf) at e
  simpa only [Category.comp_id] using e

end SerrePositivity.InfinityCategories
