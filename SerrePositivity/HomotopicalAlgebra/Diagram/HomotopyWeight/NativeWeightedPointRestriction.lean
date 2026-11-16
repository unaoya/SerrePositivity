module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedSectionPoints
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestriction

/-!
概要：元の指定された重み付き錐の点を、同じ重みの射の前合成で追跡する。
方針：普遍評価の転置の前合成則を零単体に適用する。
規約：IS-W2 R02〜R03の同じ点の照合。π₀だけの等式ではない。
使われ方：元の普遍frame錐から同じBK切断の点を作る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I]

/-- 元の重み付き自然変換の同じnative切断の零単体。 -/
def nativeWeightedPoint {W H : I ⥤ SSet.{u}} (s : W ⟶ H) :
    (weightedSections W H) _⦋0⦌ :=
  SSet.yonedaEquiv (weightedSectionsLift
    (fst W ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s))

/-- 元の重みの射による制限は、同じ指定点の前合成そのもの。 -/
theorem nativeWeightedPoint_pre {V W H : I ⥤ SSet.{u}} (j : V ⟶ W) (s : W ⟶ H) :
    ((weightedSectionsPre j H).app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint I s) =
      _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint I (j ≫ s) := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint, ← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  apply (weightedSectionsHomEquiv V H (Δ[0] : SSet.{u})).injective
  change weightedSectionsUncurry (_ ≫ weightedSectionsPre j H) =
    weightedSectionsUncurry (weightedSectionsLift _)
  rw [weightedSectionsUncurry_comp_pre, weightedSectionsUncurry_lift,
    weightedSectionsUncurry_lift]
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨v, t⟩
  rfl

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
