module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismReverseHeadZero
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedMorphismReverseHeadOne
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SimplicialHomDisplayComposition

/-!
概要：同じ元の二つの実 prism の初点 Hom 全体を一致させる。
方針：元の二時刻ごとの正規化した head を比較し、同じ端点移送を消去する。
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
open HomotopyLimits

/-- 元の初点からの全 Hom は、同じ二つの実 prism の全単体で厳密に一致する。 -/
lemma pointedMorphismPrism_head {K L : KanObject.{u}} (f : K ⟶ L) {n : ℕ}
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌) (j : Fin (n + 1)) :
    (pointedMorphismReverseSimplex f t p).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (pointedMorphismSimplex_obj f t p 0) (pointedMorphismSimplex_obj f t p j.succ)) =
    (pointedMorphismSourceSimplex f t p).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ := by
  have ht : (stdSimplex.objEquiv t).toOrderHom j = 0 ∨
      (stdSimplex.objEquiv t).toOrderHom j = 1 :=
    (by decide : ∀ z : Fin 2, z = 0 ∨ z = 1) _
  rcases ht with hj | hj
  · let hT := pointedMorphismSourceSimplex_obj_zero f t p j hj
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom rfl hT))).mp
    calc
      _ = (pointedMorphismReverseSimplex f t p).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom (pointedMorphismSimplex_obj f t p 0)
            ((pointedMorphismSimplex_obj f t p j.succ).trans hT)) := by
        exact simplicialHom_display_comp _ (pointedMorphismSimplex_obj f t p 0)
          (pointedMorphismSimplex_obj f t p j.succ) rfl hT
      _ = pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p) :=
        pointedMorphismReverseSimplex_head_zero f t p j hj
      _ = _ := (morphismInitialHead_zero f pointKanObject (stdSimplex.objEquiv t) p j hj).symm
  · let hT := pointedMorphismSourceSimplex_obj_one f t p j hj
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom rfl hT))).mp
    calc
      _ = (pointedMorphismReverseSimplex f t p).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom (pointedMorphismSimplex_obj f t p 0)
            ((pointedMorphismSimplex_obj f t p j.succ).trans hT)) := by
        exact simplicialHom_display_comp _ (pointedMorphismSimplex_obj f t p 0)
          (pointedMorphismSimplex_obj f t p j.succ) rfl hT
      _ = CartesianMonoidalCategory.lift
          (pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p))
          (SSet.const (functorVertex f)) ≫ eComp SSet pointKanObject K L :=
        pointedMorphismReverseSimplex_head_one f t p j hj
      _ = _ := (morphismInitialHead_one f pointKanObject (stdSimplex.objEquiv t) p j hj).symm

end SerrePositivity.InfinityCategories.F2
