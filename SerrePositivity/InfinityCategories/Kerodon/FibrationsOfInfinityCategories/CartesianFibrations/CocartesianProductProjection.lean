module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinBaseProjection

/-!
概要：直積の第二射影に関する cocartesian 辺と prism の両端の輸送。
方針：第一成分の可逆な辺を持つ外ホーンを充填し、指定された第二成分と組にする。
規約：第二因子の quasicategory 性は不要。
使われ方：相対 join の prism への射影から底への射影への合成。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：定値一単体は可逆な辺を表す。
方針：定値一単体と恒等辺の一致を使う。
規約：元の単体集合の充填性は不要。
使われ方：prism の固定された端点での輸送。 -/
lemma constantEdge_isInvertible {X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one x)).mpr h

/-- 概要：第一成分で可逆な直積の辺は第二射影に関して cocartesian。
方針：第一因子の最初の外ホーンを充填し、底の単体と直積を取る。
規約：第一因子のみ quasicategory。
使われ方：端点を保つ prism の底上の cocartesian 辺。 -/
lemma isCocartesianEdge_productSnd_of_invertible {X Y : SSet.{u}} [Quasicategory X]
    (e : (X ⊗ Y) _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((fst X Y).app (Opposite.op ⦋1⦌) e))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (snd X Y) e := by
  intro n a b ha sq
  have hfixed : (a ≫ fst X Y).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) =
      (fst X Y).app (Opposite.op ⦋1⦌) e := by
    change (fst X Y).app _ (a.app _ _) = _
    rw [ha]
  obtain ⟨l, hl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasInitialHornFillers_of_isInvertibleEdge _ he n (a ≫ fst X Y) hfixed
  refine CommSq.HasLift.mk' { l := lift l b, fac_left := ?_, fac_right := lift_snd _ _ }
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst]
    exact hl
  · rw [Category.assoc, lift_snd]
    exact sq.w.symm

/-- 概要：prism の両端の包含はすべての底の辺を第二射影の cocartesian 辺へ送る。
方針：区間方向の一単体は端点に定値で可逆。
規約：底の単体集合は任意。
使われ方：相対 join の左・右端の輸送を底に合成する。 -/
lemma prismEndpoint_isCocartesianEdge (i : Fin 2) {Y : SSet.{u}} (e : Y _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (snd (Δ[1] : SSet.{u}) Y)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i Y).app (Opposite.op ⦋1⦌) e) := by
  apply isCocartesianEdge_productSnd_of_invertible
  exact constantEdge_isInvertible (stdSimplex.obj₀Equiv.symm i)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
