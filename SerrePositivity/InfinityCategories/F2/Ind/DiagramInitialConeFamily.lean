module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramConePointRestriction
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Stable.UniverseJoinSimplexShapes

/-!
概要：元の全図式 comma の試験族から、始点余錐を元の全錐 comma 内で構成する。
方針：自明 Kan な始点制限の切断で持ち上げ、κ-small な試験族の余錐を取る。
規約：元の始点の全変換と C 側の全図式を厳密に保つ。使われ方：射の二段表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の試験族の始点余錐を、元の全 Ind 図式への錐とともに構成できる。 -/
lemma exists_diagramComma_initialCone_family (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {K C A : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C) (k : K _⦋0⦌)
    (hi : leftAnodyneExtensions (diagramShapePoint k)) (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶
        pullback (indYoneda κ C) (sliceOverProjection D),
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ G ≫
        diagramConePointRestriction κ D k = q ≫ diagramCommaEvaluation κ D k ∧
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ G ≫
        pullback.fst (indYoneda κ C) (sliceOverProjection D) =
          q ≫ diagramCommaProjection κ D ≫
            (SSet.uliftFunctor.{u + 1, u}).map (evaluateFunctorAt (Y := C) k) := by
  have := diagramConePointRestriction_trivialKanFibration κ D k hi
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (diagramConePointRestriction κ D k)
  let H := q ≫ diagramCommaEvaluation κ D k ≫ s
  have hH : H ≫ diagramConePointRestriction κ D k = q ≫ diagramCommaEvaluation κ D k := by
    simp only [H, Category.assoc, hs, Category.comp_id]
  obtain ⟨c⟩ := nonempty_indConeComma_cocone κ D (diagramShapePoint k) hi hA H
  let G := (uliftCoconeShapeIso.{u, u + 1} A 0).hom ≫ c.val
  have hg : (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u})) ≫ G = H := by
    dsimp only [G]
    rw [← Category.assoc, uliftCoconeShapeIso_inl]
    exact c.property
  have hG : (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u})) ≫ G ≫
      diagramConePointRestriction κ D k = q ≫ diagramCommaEvaluation κ D k := by
    rw [← Category.assoc, hg, hH]
  refine ⟨G, hG, ?_⟩
  have hp := congrArg (fun f => f ≫
    leftKanProjection (indYoneda κ C) (D.app (Opposite.op ⦋0⦌) (ULift.up k))) hG
  simpa only [Category.assoc, diagramConePointRestriction_projection,
    diagramCommaEvaluation_projection] using hp

/-- 元の射図式の始点余錐は、形状に関する追加仮定なしに全錐 comma 内で存在する。 -/
lemma exists_arrowDiagram_initialCone_family (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C A : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
    (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶
        pullback (indYoneda κ C) (sliceOverProjection D),
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ G ≫
        diagramConePointRestriction κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
          q ≫ diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ∧
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ G ≫
        pullback.fst (indYoneda κ C) (sliceOverProjection D) =
          q ≫ diagramCommaProjection κ D ≫ (SSet.uliftFunctor.{u + 1, u}).map
            (evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :=
  exists_diagramComma_initialCone_family κ D _ (diagramShapeFirstPoint_leftAnodyne 1) hA q

end SerrePositivity.InfinityCategories.F2.Ind
