module

public import SerrePositivity.InfinityCategories.F1.CartesianEdge
public import SerrePositivity.InfinityCategories.F1.RelativeJoinBaseProjection

/-!
概要：直積の第二射影に関する cocartesian 辺と prism の両端の輸送。
方針：第一成分の可逆な辺を持つ外ホーンを充填し、指定された第二成分と組にする。
規約：第二因子の quasicategory 性は不要。
使われ方：相対 join の prism への射影から底への射影への合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：定値一単体は可逆な辺を表す。
方針：定値一単体と恒等辺の一致を使う。
規約：元の単体集合の充填性は不要。
使われ方：prism の固定された端点での輸送。 -/
lemma kanConstantEdge_isInvertible {X : SSet.{u}} (x : X _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex (PinchedHom.constant x 1)) := by
  have h : IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  exact (isInvertibleEdge_congr (pinchedConstant_one x)).mpr h

/-- 概要：第一成分で可逆な直積の辺は第二射影に関して cocartesian。
方針：第一因子の最初の外ホーンを充填し、底の単体と直積を取る。
規約：第一因子のみ quasicategory。
使われ方：端点を保つ prism の底上の cocartesian 辺。 -/
lemma kanIsCocartesianEdge_productSnd_of_invertible {X Y : SSet.{u}} [Quasicategory X]
    (e : (X ⊗ Y) _⦋1⦌)
    (he : IsInvertibleEdge (edgeOfSimplex ((fst X Y).app (Opposite.op ⦋1⦌) e))) :
    IsCocartesianEdge (snd X Y) e := by
  intro n a b ha sq
  have hfixed : (a ≫ fst X Y).app (Opposite.op ⦋1⦌) (initialHornEdge n) =
      (fst X Y).app (Opposite.op ⦋1⦌) e := by
    change (fst X Y).app _ (a.app _ _) = _
    rw [ha]
  obtain ⟨l, hl⟩ := hasInitialHornFillers_of_isInvertibleEdge _ he n (a ≫ fst X Y) hfixed
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
lemma kanPrismEndpoint_isCocartesianEdge (i : Fin 2) {Y : SSet.{u}} (e : Y _⦋1⦌) :
    IsCocartesianEdge (snd (Δ[1] : SSet.{u}) Y)
      ((prismEndpoint i Y).app (Opposite.op ⦋1⦌) e) := by
  apply kanIsCocartesianEdge_productSnd_of_invertible
  exact kanConstantEdge_isInvertible (stdSimplex.obj₀Equiv.symm i)

end SerrePositivity.InfinityCategories.F1B
