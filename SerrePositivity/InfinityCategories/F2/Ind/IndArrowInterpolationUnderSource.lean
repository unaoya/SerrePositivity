module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramInitialConeUnder
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationWithSource

/-!
概要：指定した始点評価図式の下で、元の射図式族の二段補間を構成する。
方針：coslice 内で選んだ全始点余錐を、同じ sourceCone の補間データへ渡す。
規約：指定全変換は全パラメーターで保持。使われ方：評価の cofinal 性の相対入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の指定始点評価図式の下で、全始点族を厳密に保持する実二段補間が存在する。 -/
lemma exists_indArrowInterpolationData_under_source
    (κ : Cardinal.{u}) [Fact κ.IsRegular] {C A L : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      leftKanShape (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (ht : q ≫ diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      t ≫ sliceUnderProjection z) :
    ∃ V : IndArrowInterpolationData κ D q,
      ∃ P : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶ sliceUnder z,
        (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ P = t ∧
        V.sourceCone ≫ diagramConePointRestriction κ D
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = P ≫ sliceUnderProjection z := by
  obtain ⟨G, P, hG, hP, hGP⟩ := exists_diagramComma_initialCone_family_under κ D
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) (diagramShapeFirstPoint_leftAnodyne 1)
    hA hL z q t ht
  obtain ⟨V, hV⟩ := exists_indArrowInterpolationData_with_sourceCone κ D hA q G hG
  refine ⟨V, P, hP, ?_⟩
  rw [hV]
  exact hGP

end SerrePositivity.InfinityCategories.F2.Ind
