module

public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionDiagonalCut

/-!
概要：合成対角の混合 Hom を、同じ豊穣合成の標準区間比較の混合 Hom と同定する。
方針：切断の像で一致する最大座標を使い、同じ座標で二つの射を合成する。
規約：同じ対象への正規化を明示し、元の path の旗を保持する。
使われ方：coherent 合成三角形の対角の全単体での一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ対角の混合 Hom は、同じ豊穣合成の標準 Hom 比較の混合 Hom そのもの。 -/
lemma coherentCompositionDiagonalCutSimplex_mixedHom
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    (coherentCompositionDiagonalCutSimplex σ τ t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionDiagonalCutSimplex_obj_zero σ τ t i hi)
        (coherentCompositionDiagonalCutSimplex_obj_one σ τ t j hj)) =
    (coherentRightIntervalCutSimplex
      ((eComp SSet X Y Z).app (Opposite.op ⦋n⦌) (σ, τ)) t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentRightIntervalCutSimplex_obj_zero _ t i hi)
        (coherentRightIntervalCutSimplex_obj_one _ t j hj)) := by
  let D := (SimplicialThickening.functor (coherentPrismCut t).uliftMap).map
    (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
        (coherentPrismCut_zero t i hi) (coherentPrismCut_one t j (by rw [hj]; decide)))
  have hD : D ≫ pathCutMaximumMap t hi (Fin.last (n + 1)) = D ≫ pathLastMaximumMap i :=
    coherentPrismCut_diagonalMaximumMap t i j hi (by rw [hj]; decide)
  calc
    _ = lift (D ≫ pathCutMaximumMap t hi (Fin.last (n + 1)) ≫ SSet.yonedaEquiv.symm σ)
          (D ≫ pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm τ) ≫ eComp SSet X Y Z := by
      change (_ ≫ coherentCompositionHom σ τ t (coherentPrismCut t i)
        (coherentPrismCut t j)) ≫ eqToHom _ = _
      rw [Category.assoc, coherentCompositionHom_transport σ τ t
        (coherentPrismCut_zero t i hi) (coherentPrismCut_one t j (by rw [hj]; decide))
        (coherentCompositionObj_zero X Y Z t i hi) (coherentCompositionObj_last X Y Z n t),
        coherentCompositionHom_zero_last]
      simp only [← Category.assoc, comp_lift]
      rfl
    _ = lift (D ≫ pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm σ)
          (D ≫ pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm τ) ≫ eComp SSet X Y Z := by
      rw [← Category.assoc, hD]
      simp only [Category.assoc]
    _ = D ≫ pathLastMaximumMap i ≫
        SSet.yonedaEquiv.symm ((eComp SSet X Y Z).app (Opposite.op ⦋n⦌) (σ, τ)) := by
      simp only [← Category.assoc]
      rw [← comp_lift, Category.assoc, simplicialHom_yoneda_comp]
    _ = _ := (coherentRightIntervalCutSimplex_mixedHom _ t i j hi hj).symm

end SerrePositivity.InfinityCategories
