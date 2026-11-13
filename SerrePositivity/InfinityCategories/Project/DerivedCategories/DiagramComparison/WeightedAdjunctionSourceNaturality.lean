module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductSectionsTargetNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction
/-!
概要：元の重み付き切断随伴の重み変数の自然性。
方針：同じuncurryの前合成則を随伴Hom同値へ戻し、自由鎖随伴と合成する。
規約：A11の前提計算2/3。既存随伴の自然性の二段への証明分割。
使われ方：HA 1.2.4、指定自由積Hom同型の重み自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type u} [SmallCategory J]
/-- 重み付き切断の同じ随伴Hom同値は重みの前合成と可換。 -/
theorem weightedSectionsAdjunction_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (K : SSet.{u}) (H : J ⥤ SSet.{u}) (s : W ⊗ (Functor.const J).obj K ⟶ H) :
    (weightedSectionsAdjunction W').homEquiv K H ((w ▷ (Functor.const J).obj K) ≫ s) =
      (weightedSectionsAdjunction W).homEquiv K H s ≫ weightedSectionsPre w H := by
  simp only [weightedSectionsAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change weightedSectionsLift ((w ▷ (Functor.const J).obj K) ≫ s) =
    weightedSectionsLift s ≫ weightedSectionsPre w H
  apply (weightedSectionsHomEquiv W' H K).injective
  change weightedSectionsUncurry (weightedSectionsLift _) =
    weightedSectionsUncurry (weightedSectionsLift s ≫ weightedSectionsPre w H)
  rw [weightedSectionsUncurry_lift, weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_lift]
variable (A : Type u) [CommRing A]
/-- 同じ自由鎖随伴との合成Hom同値も元の重み射で可換。 -/
theorem freeWeightedAdjunction_weight_naturality {W W' : J ⥤ SSet.{u}}
    (w : W' ⟶ W) (K : SSet.{u}) (Q : J ⥤ CochainComplex (ModuleCat A) ℤ)
    (s : (freeNegativeChainsDiagramFunctor A J).obj (W ⊗ (Functor.const J).obj K) ⟶ Q) :
    ((weightedSectionsAdjunction W').comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv K Q
      ((freeNegativeChainsDiagramFunctor A J).map (w ▷ (Functor.const J).obj K) ≫ s) =
    ((weightedSectionsAdjunction W).comp (freeNegativeChainsDiagramAdjunction A J)).homEquiv K Q s ≫
      weightedSectionsPre w (Q ⋙ SerrePositivity.EInfinity.ComplexLimits.truncatedDoldKanFunctor A) := by
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  change (weightedSectionsAdjunction W').homEquiv K _
    ((freeNegativeChainsDiagramAdjunction A J).homEquiv _ Q
      ((freeNegativeChainsDiagramFunctor A J).map (w ▷ (Functor.const J).obj K) ≫ s)) =
    (weightedSectionsAdjunction W).homEquiv K _
      ((freeNegativeChainsDiagramAdjunction A J).homEquiv _ Q s) ≫ weightedSectionsPre w _
  rw [Adjunction.homEquiv_naturality_left]
  exact weightedSectionsAdjunction_weight_naturality w K _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
