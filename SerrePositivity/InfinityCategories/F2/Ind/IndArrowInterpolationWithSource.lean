module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationData

/-!
概要：指定した元の全始点余錐を選び直さず、二段補間データへ延長する。
方針：同じ始点境界から slice 円柱を持ち上げ、実 scalar comma で円柱を延長する。
規約：指定全始点族を厳密に回収。使われ方：評価対象の下での表示族の補間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 指定した元の全始点余錐そのものを sourceCone に持つ、実二段補間を構成する。 -/
lemma exists_indArrowInterpolationData_with_sourceCone (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C A : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
    (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶
      pullback (indYoneda κ C) (sliceOverProjection D))
    (hG : (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ G ≫
      diagramConePointRestriction κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
        q ≫ diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :
    ∃ V : IndArrowInterpolationData κ D q, V.sourceCone = G := by
  let g := (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u}))
  let H := g ≫ G
  have hH : H ≫ diagramConePointRestriction κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
      q ≫ diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    simpa only [H, g, Category.assoc] using hG
  obtain ⟨W⟩ := indArrowSlicePrism_nonempty κ D q H hH
  let F := rightIntervalUniverseShape A ≫ indArrowEndpointFamily κ D q H W
  let G' := indArrowSourceEndpointFamily κ D G
  have hFG : (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₀ ≫ F = g ≫ G' := by
    calc
      _ = SSet.ι₀ ≫ indArrowEndpointFamily κ D q H W := by
        dsimp only [F]
        rw [← Category.assoc, rightIntervalUniverseShape_zero]
      _ = indArrowSourceEndpointFamily κ D H := indArrowEndpointFamily_zero κ D q H W hH
      _ = _ := by simpa only [H, G'] using (indArrowSourceEndpointFamily_precomp κ D G g).symm
  obtain ⟨E, he, hs⟩ := exists_indComma_arrowInterpolation_extension κ
    (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))))
    hA F G' (by simpa only [g] using hFG)
  exact ⟨⟨G, hG, W, E, he, hs⟩, rfl⟩

end SerrePositivity.InfinityCategories.F2.Ind
