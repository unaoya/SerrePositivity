module

public import SerrePositivity.InfinityCategories.F2.PointedMorphismPrismSimplices

/-!
概要：元の反転合成単体の零時刻への head を、元の初点係数の評価へ同定する。
方針：実反転射の端点移送と一ラベルの式を、元の反転係数座標へ接続する。
規約：元の全単体・全 path を保持。使われ方：二つの実 prism の全 Hom の一致。
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

/-- 元の反転合成単体の実 head は、零時刻では元の同じ初点係数の評価。 -/
lemma pointedMorphismReverseSimplex_head_zero {K L : KanObject.{u}} (f : K ⟶ L) {n : ℕ}
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌)
    (j : Fin (n + 1)) (hj : (stdSimplex.objEquiv t).toOrderHom j = 0) :
    (pointedMorphismReverseSimplex f t p).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom (pointedMorphismSimplex_obj f t p 0)
        ((pointedMorphismSimplex_obj f t p j.succ).trans
          (pointedMorphismSourceSimplex_obj_zero f t p j hj))) =
      pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p) := by
  let r := stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom
  let σ := PinchedHom.constant (functorVertex f) n
  let τ := SSet.opObjEquiv p
  have hr : r j.rev ≠ 0 := by
    change ((stdSimplex.objEquiv t).toOrderHom j.rev.rev).rev ≠ 0
    rw [Fin.rev_rev, hj]
    decide
  change (((coherentReverseThickening (n + 1)).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
    coherentCompositionHom (X := Opposite.op L) (Y := Opposite.op K)
      (Z := Opposite.op pointKanObject) σ τ r j.succ.rev (Fin.rev 0)) ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]
  change ((coherentReverseThickening (n + 1)).map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
    coherentCompositionHom (X := Opposite.op L) (Y := Opposite.op K)
      (Z := Opposite.op pointKanObject) σ τ r j.succ.rev (Fin.rev 0)) ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (coherentCompositionObj (Opposite.op L) (Opposite.op K)
        (Opposite.op pointKanObject) r) (Fin.rev_succ j)).trans
          (coherentCompositionObj_one _ _ _ r j.rev hr))
      ((congrArg (coherentCompositionObj (Opposite.op L) (Opposite.op K)
        (Opposite.op pointKanObject) r) (Fin.rev_zero (n + 1))).trans
          (coherentCompositionObj_last _ _ _ n r))) = _
  refine (coherentReverseComposition_initial_transport (C := KanObject.{u}ᵒᵖ) σ τ r j
    (coherentCompositionObj_one _ _ _ r j.rev hr)
    (coherentCompositionObj_last _ _ _ n r)).trans ?_
  exact (coherentReverseComposition_initial_one (C := KanObject.{u}ᵒᵖ) σ τ r j hr).trans
    (coneInitialParameter_reflected_coefficient p j).symm

end SerrePositivity.InfinityCategories.F2
