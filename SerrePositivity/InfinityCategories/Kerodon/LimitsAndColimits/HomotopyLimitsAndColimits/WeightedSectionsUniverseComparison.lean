module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedDiagramUniverse

/-!
概要：元の重み付き切断空間のULiftを、宇宙変更した同じ図式の切断へ送る。
方針：元の普遍評価を同じテンソルの指定同型で移し、nativeな転置を取る。
規約：IS-W2 R02〜R03の係数移送の法則。比較射を別の全単射で置き換えない。
使われ方：同じBK切断空間の宇宙変更と全標準脚の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory Limits SSet MonoidalCategory
variable (I : Type u) [SmallCategory I] (W H : I ⥤ SSet.{u})

/-- 元の普遍評価を同じテンソルの指定同型で宇宙変更した自然変換。 -/
def weightedSectionsUniverseEvaluation :
    (weightedDiagramUniverse.{u,v} I).obj W ⊗
      (Functor.const (AsSmall.{v} I)).obj
        ((SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H)) ⟶
          (weightedDiagramUniverse.{u,v} I).obj H :=
  (weightedDiagramUniverseTensorIso I W (weightedSections W H)).inv ≫
    (weightedDiagramUniverse I).map (weightedSectionsUncurry (𝟙 (weightedSections W H)))

/-- 同じ重み付き切断空間を宇宙変更する、普遍評価による指定比較射。 -/
def weightedSectionsUniverseComparison :
    (SSet.uliftFunctor.{max u v,u}).obj (weightedSections W H) ⟶
      weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
        ((weightedDiagramUniverse.{u,v} I).obj H) :=
  weightedSectionsLift (weightedSectionsUniverseEvaluation I W H)

/-- 同じ比較射へのパラメーターの射のULiftを転置すると、元の転置の宇宙変更。 -/
theorem weightedSectionsUniverseComparison_map_uncurry {A : SSet.{u}}
    (f : A ⟶ weightedSections W H) :
    weightedSectionsUncurry ((SSet.uliftFunctor.{max u v,u}).map f ≫
      weightedSectionsUniverseComparison I W H) =
        (weightedDiagramUniverseTensorIso I W A).inv ≫
          (weightedDiagramUniverse I).map (weightedSectionsUncurry f) := by
  rw [weightedSectionsUncurry_precomp, weightedSectionsUniverseComparison,
    weightedSectionsUncurry_lift, weightedSectionsUniverseEvaluation,
    ← Category.assoc, weightedDiagramUniverseTensorIso_inv_parameter,
    Category.assoc, ← CategoryTheory.Functor.map_comp]
  congr 1

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
