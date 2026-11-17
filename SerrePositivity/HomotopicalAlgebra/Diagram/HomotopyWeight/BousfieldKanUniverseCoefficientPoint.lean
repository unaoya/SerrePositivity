module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanNativeFiberPoint
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanUniversePoints
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanExInfinityUnit

/-!
概要：同じBK点のfiber評価を、元の宇宙変更とEx∞係数単位の前まで追跡する。
方針：指定downの恒等射での評価と元の係数単位の合成を計算する。
規約：IS-W2 R02〜R03の既存の宇宙変更・係数移送の評価則。
使われ方：BE Totのnative錐の脚を、同じ元のraw係数で照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I] {H : I ⥤ SSet.{u}}

/-- 同じ指定downと係数の宇宙変更は、恒等射のBK零単体での元の値を保つ。 -/
theorem bousfieldKanUniverseCone_identityVertex (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseCone.{u,v} I s).app (AsSmall.up.obj i)).app (Opposite.op ⦋0⦌)
      (nerveVertex (Over.mk (𝟙 (((AsSmall.up : I ⥤ AsSmall.{v} I).obj i))))) =
        ULift.up ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i)))) := by
  change ULift.up ((s.app i).app (Opposite.op ⦋0⦌)
    ((nerveVertex (Over.mk (𝟙 (((AsSmall.up : I ⥤ AsSmall.{v} I).obj i))))) ⋙
      Over.post (AsSmall.down : AsSmall.{v} I ⥤ I))) = _
  congr 1

/-- 同じEx∞係数単位まで合成したBK錐も、元の恒等射の零単体で厳密に評価できる。 -/
theorem bousfieldKanUniverseExInfinityCone_identityVertex
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseCone.{u,v} I s ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _ _).app
      (AsSmall.up.obj i)).app (Opposite.op ⦋0⦌)
        (nerveVertex (Over.mk (𝟙 (((AsSmall.up : I ⥤ AsSmall.{v} I).obj i))))) =
      (exInfinityUnit.app ((SSet.uliftFunctor.{max u v,u}).obj (H.obj i))).app (Opposite.op ⦋0⦌)
        (ULift.up ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))) := by
  change (exInfinityUnit.app _).app (Opposite.op ⦋0⦌)
    (((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseCone.{u,v} I s).app (AsSmall.up.obj i)).app (Opposite.op ⦋0⦌) _) = _
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseCone_identityVertex]
  rfl

/-- 元の同じBK点を宇宙変更とEx∞係数単位へ運びfiberから戻すと、元の値の指定像になる。 -/
theorem bousfieldKanUniverseExInfinityPoint_fiber
    (s : bousfieldKanWeight I ⟶ H) (i : I) :
    let H' := (weightedDiagramUniverse.{u,v} I).obj H ⋙ exInfinity
    let s' := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseCone.{u,v} I s ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _ _
    ((weightedNerveFiberIso H' (AsSmall.up.obj i)).inv.app (Opposite.op ⦋0⦌))
      ((simplicialSectionsFiberEvaluation (weightedNerveProjection H')
        (nerveVertex (AsSmall.up.obj i))).app (Opposite.op ⦋0⦌)
          (((bousfieldKanSectionsIso H').hom.app (Opposite.op ⦋0⦌))
            (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.nativeWeightedPoint (AsSmall.{v} I) s'))) =
      (exInfinityUnit.app ((SSet.uliftFunctor.{max u v,u}).obj (H.obj i))).app (Opposite.op ⦋0⦌)
        (ULift.up ((s.app i).app (Opposite.op ⦋0⦌) (nerveVertex (Over.mk (𝟙 i))))) := by
  exact (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanSectionsIso_nativeWeightedPoint_fiber (AsSmall.{v} I)
    ((weightedDiagramUniverse.{u,v} I).obj H ⋙ exInfinity)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseCone.{u,v} I s ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanExInfinityCoefficientUnit _ _)
    (AsSmall.up.obj i)).trans (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanUniverseExInfinityCone_identityVertex I s i)

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
