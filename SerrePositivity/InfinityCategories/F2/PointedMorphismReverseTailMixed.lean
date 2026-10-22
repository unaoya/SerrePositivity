module

public import SerrePositivity.InfinityCategories.F2.PointedMorphismPrismSimplices
public import SerrePositivity.InfinityCategories.F2.ReverseCompositionPositiveHom

/-!
概要：元の実反転合成単体の零から一時刻の tail Hom を、元の指定射へ同定する。
方針：二端点の元のラベルを反転し、元の合成 Hom の定値性を使う。
規約：元の全 path を保持。使われ方：二つの全 prism の正頂点 Hom の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の零から一時刻の実反転 tail Hom は元の指定射。 -/
lemma pointedMorphismReverseSimplex_tail_mixed {K L : KanObject.{u}} (f : K ⟶ L) {n : ℕ}
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (p : (SimplicialCategory.sHom pointKanObject K).op _⦋n⦌)
    (i j : Fin (n + 1)) (hi : (stdSimplex.objEquiv t).toOrderHom i = 0)
    (hj : (stdSimplex.objEquiv t).toOrderHom j = 1) :
    (pointedMorphismReverseSimplex f t p).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        ((pointedMorphismSimplex_obj f t p i.succ).trans
          (pointedMorphismSourceSimplex_obj_zero f t p i hi))
        ((pointedMorphismSimplex_obj f t p j.succ).trans
          (pointedMorphismSourceSimplex_obj_one f t p j hj))) =
      SSet.const (functorVertex f) := by
  let r := stableReverseOrderHom (stdSimplex.objEquiv t).toOrderHom
  let σ := PinchedHom.constant (functorVertex f) n
  let τ := SSet.opObjEquiv p
  have hi' : r i.rev ≠ 0 := by
    change ((stdSimplex.objEquiv t).toOrderHom i.rev.rev).rev ≠ 0
    rw [Fin.rev_rev, hi]
    decide
  have hj' : r j.rev = 0 := by
    change ((stdSimplex.objEquiv t).toOrderHom j.rev.rev).rev = 0
    rw [Fin.rev_rev, hj]
    decide
  have hv : coherentCompositionHom (X := Opposite.op L) (Y := Opposite.op K)
      (Z := Opposite.op pointKanObject) σ τ r j.rev.castSucc i.rev.castSucc ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionObj_zero _ _ _ r j.rev hj')
        (coherentCompositionObj_one _ _ _ r i.rev hi')) =
      SSet.const (functorVertex f) := by
    refine (coherentCompositionHom_zero_one (C := KanObject.{u}ᵒᵖ)
      σ τ r j.rev i.rev hj' hi').trans ?_
    have hc : SSet.yonedaEquiv.symm σ =
        (SSet.const (functorVertex f) : (Δ[n] : SSet.{u}) ⟶ _) := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      rfl
    exact (congrArg (fun a ↦ pathCutMaximumMap r hj' i.rev.castSucc ≫ a) hc).trans
      (SSet.comp_const _ _)
  have h := coherentReverseComposition_positive_const (C := KanObject.{u}) σ τ r i j
    (coherentCompositionObj_zero _ _ _ r j.rev hj')
    (coherentCompositionObj_one _ _ _ r i.rev hi') _ hv
  exact h

end SerrePositivity.InfinityCategories.F2
