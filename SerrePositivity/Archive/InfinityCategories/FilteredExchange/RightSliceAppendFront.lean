module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSliceAppendEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCurryHomExt
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionSquareEvaluation

/-!
概要：指定射を追加した全錐族の始端側の面は、元の全錐族そのもの。
方針：同じ固定終点と全標準単体で実全図式を比較する。
規約：全係数を保持し、境界一致だけへ弱めない。使われ方：実四面体の元の面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全錐族を同じ追加族の始端側の実全面から厳密に回収する。 -/
lemma coherentRightSliceAppendEdge_front
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {Z W : C} (g : Z ⟶ W)
    {A : SSet.{max u v}}
    (F : A ⟶ sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex Z))) :
    joinMap (𝟙 A) (stdSimplex.δ (1 : Fin 2)) ≫
        sliceOverUncurry (F ≫ coherentRightSliceAppendEdge g) = sliceOverUncurry F := by
  apply join_left_hom_ext
  · calc
      _ = (stdSimplex.δ (1 : Fin 2)) ≫
          SSet.yonedaEquiv.symm (coherentNerveEdge g).edge := by
        rw [← Category.assoc, joinInr_joinMap, Category.assoc, sliceOverUncurry_fixed]
      _ = SSet.yonedaEquiv.symm (coherentNerveVertex Z) := by
        change stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
          SSet.yonedaEquiv.symm (coherentNerveEdge g).edge = _
        rw [SSet.yonedaEquiv_symm_naturality_left]
        exact congrArg SSet.yonedaEquiv.symm (coherentNerveEdge g).src_eq
      _ = _ := (sliceOverUncurry_fixed F).symm
  · intro n a
    let c := F.app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv a)
    have h₁ : joinMap a (𝟙 (Δ[1] : SSet.{max u v})) ≫
        sliceOverUncurry (F ≫ coherentRightSliceAppendEdge g) =
          coherentRightSliceAppendEdgeCone g c := by
      simpa only [Equiv.symm_apply_apply, coherentRightSliceAppendEdge, NatTrans.comp_app,
        types_comp_apply, TypeCat.ofHom_apply, c] using
        sliceOverUncurry_simplex_coordinate (F ≫ coherentRightSliceAppendEdge g)
          (SSet.yonedaEquiv a)
    have h₀ : joinMap a (𝟙 (Δ[0] : SSet.{max u v})) ≫ sliceOverUncurry F = c.val := by
      simpa only [Equiv.symm_apply_apply] using
        sliceOverUncurry_simplex_coordinate F (SSet.yonedaEquiv a)
    have hx : joinMap a (𝟙 (Δ[0] : SSet.{max u v})) ≫
        joinMap (𝟙 A) (stdSimplex.δ (1 : Fin 2)) =
      joinMap (𝟙 Δ[n]) (stdSimplex.δ (1 : Fin 2)) ≫ joinMap a (𝟙 Δ[1]) := by
      simp only [← joinMap_comp, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, hx, Category.assoc, h₁, coherentRightSliceAppendEdgeCone_start, h₀]

end SerrePositivity.InfinityCategories.F2
