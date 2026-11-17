module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedPointRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanUniverseSections
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionsUniversePoints

/-!
概要：同じBK重みの宇宙変更同型は、元の指定BK錐の同じ零単体を保つ。
方針：普遍評価による宇宙比較の点の式に、指定downによる重みの前合成則を合わせる。
規約：IS-W2 R02〜R03の既存の移送則。元の錐の自然変換を保持する。
使われ方：BE Totの指定BK点を全Hom∞比較の宇宙へ運ぶ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I] {H : I ⥤ SSet.{u}}

/-- 指定BK錐を同じdownと同じULift係数で宇宙変更する自然変換。 -/
def bousfieldKanUniverseCone (s : bousfieldKanWeight I ⟶ H) :
    bousfieldKanWeight (AsSmall.{v} I) ⟶ (weightedDiagramUniverse.{u,v} I).obj H :=
  bousfieldKanUniverseWeightDown I ≫ (weightedDiagramUniverse I).map s

/-- 元のBK切断の宇宙変更同型は、同じ指定BK錐の零単体を保つ。 -/
theorem bousfieldKanUniverseSectionsIso_point (s : bousfieldKanWeight I ⟶ H) :
    (((bousfieldKanUniverseSectionsIso.{u,v} I H).hom).app (Opposite.op ⦋0⦌))
      (ULift.up (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint I s)) =
        _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint (AsSmall.{v} I) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseCone I s) := by
  change ((weightedSectionsPre (bousfieldKanUniverseWeightDown I)
    ((weightedDiagramUniverse.{u,v} I).obj H)).app (Opposite.op ⦋0⦌))
      (((weightedSectionsUniverseComparison I (bousfieldKanWeight I) H).app (Opposite.op ⦋0⦌))
        (ULift.up (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint I s))) = _
  have h := weightedSectionsUniverseComparison_point.{u,v} I s
  change ((weightedSectionsUniverseComparison I (bousfieldKanWeight I) H).app (Opposite.op ⦋0⦌))
    (ULift.up (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint I s)) = _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint (AsSmall.{v} I)
      ((weightedDiagramUniverse.{u,v} I).map s) at h
  rw [h, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint_pre]
  rfl

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
