module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionsUniverseComparison

/-!
概要：元の小さいパラメーターの切断と、同じパラメーターのULiftからの切断を全単射で合わせる。
方針：同じ指定比較を順写像とし、展開した族を図式の全忠実性で降ろして逆を作る。
規約：IS-W2 R02〜R03の係数移送の法則。Kan性は不要。
使われ方：標準単体による同じ切断空間の宇宙比較の同型性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory Limits SSet MonoidalCategory
variable (I : Type u) [SmallCategory I] (W H : I ⥤ SSet.{u})

/-- 同じ指定比較への後合成は、小さい全パラメーターについて全単射。 -/
def weightedSectionsUniverseHomEquiv (A : SSet.{u}) :
    (A ⟶ weightedSections W H) ≃
      ((SSet.uliftFunctor.{max u v,u}).obj A ⟶
        weightedSections ((weightedDiagramUniverse.{u,v} I).obj W)
          ((weightedDiagramUniverse.{u,v} I).obj H)) where
  toFun f := (SSet.uliftFunctor.{max u v,u}).map f ≫ weightedSectionsUniverseComparison I W H
  invFun g := weightedSectionsLift ((weightedDiagramUniverse.{u,v} I).preimage
    ((weightedDiagramUniverseTensorIso I W A).hom ≫ weightedSectionsUncurry g))
  left_inv f := by
    apply (weightedSectionsHomEquiv W H A).injective
    change weightedSectionsUncurry (weightedSectionsLift _) = weightedSectionsUncurry f
    rw [weightedSectionsUncurry_lift]
    apply (weightedDiagramUniverse.{u,v} I).map_injective
    rw [CategoryTheory.Functor.map_preimage, weightedSectionsUniverseComparison_map_uncurry,
      Iso.hom_inv_id_assoc]
  right_inv g := by
    apply (weightedSectionsHomEquiv ((weightedDiagramUniverse.{u,v} I).obj W)
      ((weightedDiagramUniverse.{u,v} I).obj H) ((SSet.uliftFunctor.{max u v,u}).obj A)).injective
    change weightedSectionsUncurry ((SSet.uliftFunctor.{max u v,u}).map (weightedSectionsLift _) ≫
      weightedSectionsUniverseComparison I W H) = weightedSectionsUncurry g
    rw [weightedSectionsUniverseComparison_map_uncurry, weightedSectionsUncurry_lift,
      CategoryTheory.Functor.map_preimage, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
