module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismReverseTailZero
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismReverseTailOne
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismReverseTailMixed
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismSourceTail
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SimplicialHomDisplayComposition

/-!
概要：同じ元の二つの全 prism の、順方向の正頂点間 Hom を厳密に一致させる。
方針：元の三つの二時刻配置で同じ正規化式を比較し、表示変更を消去する。
規約：全次数・全係数・全 path を保持。使われ方：二つの全単体の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の正頂点間の全 Hom は、順方向では同じ二つの実単体で一致する。 -/
lemma pointedMorphismPrism_tail_of_le {K L : KanObject.{u}} (f : K ⟶ L) {n : ℕ}
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (pointedMorphismReverseSimplex f t p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (pointedMorphismSimplex_obj f t p i.succ)
        (pointedMorphismSimplex_obj f t p j.succ)) =
    (pointedMorphismSourceSimplex f t p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ := by
  have hi : (stdSimplex.objEquiv t).toOrderHom i = 0 ∨
      (stdSimplex.objEquiv t).toOrderHom i = 1 :=
    (by decide : ∀ z : Fin 2, z = 0 ∨ z = 1) _
  have hj : (stdSimplex.objEquiv t).toOrderHom j = 0 ∨
      (stdSimplex.objEquiv t).toOrderHom j = 1 :=
    (by decide : ∀ z : Fin 2, z = 0 ∨ z = 1) _
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · apply simplicialHom_eq_of_display _ _
      (pointedMorphismSimplex_obj f t p i.succ)
      (pointedMorphismSimplex_obj f t p j.succ)
      (pointedMorphismSourceSimplex_obj_zero f t p i hi)
      (pointedMorphismSourceSimplex_obj_zero f t p j hj)
    exact (pointedMorphismReverseSimplex_tail_zero f t p i j hi hj).trans
      (pointedMorphismSourceSimplex_tail_zero f t p i j hij hi hj).symm
  · apply simplicialHom_eq_of_display _ _
      (pointedMorphismSimplex_obj f t p i.succ)
      (pointedMorphismSimplex_obj f t p j.succ)
      (pointedMorphismSourceSimplex_obj_zero f t p i hi)
      (pointedMorphismSourceSimplex_obj_one f t p j hj)
    exact (pointedMorphismReverseSimplex_tail_mixed f t p i j hi hj).trans
      (pointedMorphismSourceSimplex_tail_mixed f t p i j hij hi hj).symm
  · have h := (stdSimplex.objEquiv t).toOrderHom.monotone hij
    rw [hi, hj] at h
    exact False.elim ((by decide : ¬(1 : Fin 2) ≤ 0) h)
  · apply simplicialHom_eq_of_display _ _
      (pointedMorphismSimplex_obj f t p i.succ)
      (pointedMorphismSimplex_obj f t p j.succ)
      (pointedMorphismSourceSimplex_obj_one f t p i hi)
      (pointedMorphismSourceSimplex_obj_one f t p j hj)
    exact (pointedMorphismReverseSimplex_tail_one f t p i j hi hj).trans
      (pointedMorphismSourceSimplex_tail_one f t p i j hij hi hj).symm

end SerrePositivity.InfinityCategories.F2
