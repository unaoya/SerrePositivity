module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationData
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramInitialConeFamily

/-!
概要：元の任意の κ-small 試験族から、互換な F,G と実全円柱延長を構成する。
方針：元の始点全錐から F の slice 円柱を持ち上げ、両全境界を厳密に貼り合わせる。
規約：追加の同値性・fibration 仮定なし。使われ方：元の射図式 comma の余錐への帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の κ-small な全試験族の二段補間は、全境界を保持した実データとして存在する。 -/
lemma indArrowInterpolationData_nonempty (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C A : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
    (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D) :
    Nonempty (IndArrowInterpolationData κ D q) := by
  obtain ⟨G, hG, _⟩ := exists_arrowDiagram_initialCone_family κ D hA q
  let g := (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u}))
  let H := g ≫ G
  have hH : H ≫ diagramConePointRestriction κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
      q ≫ diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    simpa only [H, g, Category.assoc] using hG
  obtain ⟨V⟩ := indArrowSlicePrism_nonempty κ D q H hH
  let F := rightIntervalUniverseShape A ≫ indArrowEndpointFamily κ D q H V
  let G' := indArrowSourceEndpointFamily κ D G
  have hFG : (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₀ ≫ F = g ≫ G' := by
    calc
      _ = SSet.ι₀ ≫ indArrowEndpointFamily κ D q H V := by
        dsimp only [F]
        rw [← Category.assoc, rightIntervalUniverseShape_zero]
      _ = indArrowSourceEndpointFamily κ D H := indArrowEndpointFamily_zero κ D q H V hH
      _ = _ := by simpa only [H, G'] using (indArrowSourceEndpointFamily_precomp κ D G g).symm
  obtain ⟨E, he, hs⟩ := exists_indComma_arrowInterpolation_extension κ
    (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2))))
    hA F G' (by simpa only [g] using hFG)
  exact ⟨⟨G, hG, V, E, he, hs⟩⟩

end SerrePositivity.InfinityCategories.F2.Ind
