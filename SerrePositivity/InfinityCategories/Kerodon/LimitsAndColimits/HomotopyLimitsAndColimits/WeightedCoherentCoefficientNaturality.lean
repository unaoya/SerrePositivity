module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCoherentCoefficients

/-!
概要：同じweighted coneの混合Hom係数は係数図式射の全作用を保つ。
方針：既存の反転標準単体の後合成則を、同じ最小点の写像に後合成する。
規約：IS-W2 D01の既存構成の自然性・貼り合わせ則。
使われ方：Kerodon 7.5.4、指定BK錐の全HA成分の厳密自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {I : Type u} [SmallCategory I] {H H' H'' : I ⥤ SSet.{u}}
variable {n : ℕ} {σ : ComposableArrows I n}

/-- 同じ混合Hom係数は、全係数図式射への後合成と可換。 -/
theorem weightedCoherentCoefficient_map (α : H ⟶ H')
    (τ : simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor) (j : Fin (n + 1)) :
    weightedCoherentCoefficient
        (τ ≫ Functor.whiskerLeft σ (Functor.whiskerRight α SSet.opFunctor)) j =
      weightedCoherentCoefficient τ j ≫ α.app (σ.obj j) := by
  unfold weightedCoherentCoefficient
  change _ ≫ reflectedSimplexMap (τ.app j ≫ SSet.opFunctor.map (α.app (σ.obj j))) = _
  rw [reflectedSimplexMap_post, Category.assoc]

/-- 同じ二つの係数の両作用の等式は、全混合Hom係数の等式になる。 -/
theorem weightedCoherentCoefficient_dinaturality (α : H ⟶ H'') (β : H' ⟶ H'')
    (τ : simplexPrefixWeight n ⟶ σ ⋙ H ⋙ SSet.opFunctor)
    (τ' : simplexPrefixWeight n ⟶ σ ⋙ H' ⋙ SSet.opFunctor)
    (h : τ ≫ Functor.whiskerLeft σ (Functor.whiskerRight α SSet.opFunctor) =
      τ' ≫ Functor.whiskerLeft σ (Functor.whiskerRight β SSet.opFunctor))
    (j : Fin (n + 1)) :
    weightedCoherentCoefficient τ j ≫ α.app (σ.obj j) =
      weightedCoherentCoefficient τ' j ≫ β.app (σ.obj j) := by
  rw [← weightedCoherentCoefficient_map, h, weightedCoherentCoefficient_map]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
