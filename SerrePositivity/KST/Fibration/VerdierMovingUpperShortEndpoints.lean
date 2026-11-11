module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperShortFamilies

/-!
概要：動く上側第二短辺の両端は元の二つの実完全射の全 S• 作用。
方針：元の同じ全 S• 比較区間の両端回収を、同じ標準単体の宇宙持ち上げへ送る。
規約：第二短辺を定値へ置換せず、元の指定完全射を保持する。
使われ方：K-6 c4 の動く上側族の指定有限端点照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 概要：動く実第二短辺の始端は元の上側合成完全射の全 S• 作用。
方針：元の同じ小さい実区間の始端をそのまま持ち上げる。
規約：元の実射そのもの。使われ方：指定上側始端の第二短辺条件。 -/
theorem verdierMovingUpperLastFamily_first :
    (verdierMovingUpperLastFamily d).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject d.left).obj ⟶
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj from
            verdierOriginalFullSCompositeMap d 0)) := by
  have h := verdierOriginalFullSCompositePath_first d 0 1
  rw [SSet.yonedaEquiv_symm_zero] at h
  have hv := congrArg (fun f => f.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) h
  change (verdierOriginalFullSCompositePath d 0 1).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject d.left).obj ⟶
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj from
          verdierOriginalFullSCompositeMap d 0)) 0 at hv
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hv
  change ULift.up ((verdierOriginalFullSCompositePath d 0 1).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _
  exact congrArg ULift.up hv

/-- 概要：動く実第二短辺の終端は元の実包含・商の合成完全射の全 S• 作用。
方針：元の同じ小さい実区間の終端をそのまま持ち上げる。
規約：元の実射を選び直さない。使われ方：指定上側終端の第二短辺条件。 -/
theorem verdierMovingUpperLastFamily_last :
    (verdierMovingUpperLastFamily d).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject d.left).obj ⟶
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj from
            verdierOriginalFullSCompositeMap d 1)) := by
  have h := verdierOriginalFullSCompositePath_last d 0 1
  rw [SSet.yonedaEquiv_symm_zero] at h
  have hv := congrArg (fun f => f.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) h
  change (verdierOriginalFullSCompositePath d 0 1).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject d.left).obj ⟶
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj from
          verdierOriginalFullSCompositeMap d 1)) 0 at hv
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at hv
  change ULift.up ((verdierOriginalFullSCompositePath d 0 1).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
  exact congrArg ULift.up hv

end SerrePositivity.KST.Fibration
