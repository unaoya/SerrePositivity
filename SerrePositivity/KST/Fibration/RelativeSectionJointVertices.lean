module
public import SerrePositivity.KST.Fibration.RelativeSectionBaseChangeJointPoint

/-! # 切断の共同図式の指定二重評価は、同じ実切断 Kan 空間の標準頂点 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} {J : Type u} [Category.{u} J]

/-- 共同切断図式の同じ二重評価は、指定係数の実 Kan 値。 -/
theorem relativeSectionDiagramInfinity_double_vertex (A : Jᵒᵖ ⥤ Over B)
    (X : LeftFibrationObject B) (j : J) :
    (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
      (ULift.up (nerveVertex j)) (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
        (functorVertex (relativeSectionDiagramInfinity A)) =
      spaceInfinityVertex (((relativeSectionEnrichedDiagram A).obj j).obj X) := by
  rw [doubleFunctorEvaluation_vertex]
  change (evaluateFunctorAt (X := LeftFibrationInfinity B) (Y := SpaceInfinity.{u})
    (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
      ((relativeSectionDiagramInfinity A).app (Opposite.op ⦋0⦌)
        (ULift.up (nerveVertex j))) = _
  rw [relativeSectionDiagramInfinity_vertex A j, evaluateFunctorAt_functorVertex]
  exact coherentNerveMap_vertex (relativeFunctorEnrichedEvaluation (A.obj (Opposite.op j))) X

/-- 底変換した共同切断図式の同じ評価は、元の pullback 切断空間。 -/
theorem relativeSectionDiagramInfinity_double_precomp_vertex (k : D ⟶ B)
    (A : Jᵒᵖ ⥤ Over D) (X : LeftFibrationObject B) (j : J) :
    (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
      (ULift.up (nerveVertex j)) (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
        (functorVertex (relativeSectionDiagramInfinity A ≫
          (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})) =
      spaceInfinityVertex
        ((((relativeSectionEnrichedDiagram A).precompose
          (leftFibrationBaseChangeEnriched k)).obj j).obj X) := by
  rw [doubleFunctorEvaluation_vertex]
  change (evaluateFunctorAt (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
    (((pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}).app
      (Opposite.op ⦋0⦌) ((relativeSectionDiagramInfinity A).app (Opposite.op ⦋0⦌)
        (ULift.up (nerveVertex j)))) = _
  rw [relativeSectionDiagramInfinity_vertex]
  change (evaluateFunctorAt (coherentNerveVertex X)).app (Opposite.op ⦋0⦌)
    (functorVertex (leftFibrationInfinityBaseChange k ≫
      coherentNerveMap (relativeFunctorEnrichedEvaluation (A.obj (Opposite.op j))))) = _
  rw [evaluateFunctorAt_functorVertex]
  change (coherentNerveMap (relativeFunctorEnrichedEvaluation (A.obj (Opposite.op j)))).app
    (Opposite.op ⦋0⦌)
    ((leftFibrationInfinityBaseChange k).app (Opposite.op ⦋0⦌) (coherentNerveVertex X)) = _
  rw [leftFibrationInfinityBaseChange_vertex, coherentNerveMap_vertex]
  rfl

/-- 同じ共同底変換同型の指定成分を、元の二つの切断空間で表示する。 -/
def relativeSectionJointBaseChangeValueIso (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D)
    (X : LeftFibrationObject B) (j : J) :=
  F2.isoNormalizeEndpoints
    (VertexIso.map (relativeSectionDiagramInfinityBaseChangeIso k A)
      (doubleFunctorEvaluation (Y := SpaceInfinity.{u})
        (ULift.up (nerveVertex j)) (coherentNerveVertex X)))
    (congrArg HomotopyCategory.mk
      (relativeSectionDiagramInfinity_double_precomp_vertex k A X j))
    (congrArg HomotopyCategory.mk
      (relativeSectionDiagramInfinity_double_vertex (A ⋙ Over.map k) X j))

/-- 元の共同同型の指定成分は、元の切断比較の同じ係数成分と厳密一致する。 -/
theorem relativeSectionJointBaseChangeValueIso_eq (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D)
    (X : LeftFibrationObject B) (j : J) :
    relativeSectionJointBaseChangeValueIso k A X j =
      relativeSectionBaseChangeComponentIso k A X j :=
  F2.isoNormalizeEndpoints_eq_of_heq _ _ _ _
    (relativeSectionBaseChangeComponentIso_heq_jointMap k A X j).symm

/-- 指定逆成分は、元の第一射影像の点から同じ pullback 切断の点を回収する。 -/
theorem relativeSectionJointBaseChangeValueIso_inv_pointHom
    (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) (X : LeftFibrationObject B) (j : J)
    (v : ((((relativeSectionEnrichedDiagram A).precompose
      (leftFibrationBaseChangeEnriched k)).obj j).obj X).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (A ⋙ Over.map k)).obj j).obj X)).symm
        ((relativeFunctorBaseChangeForward X.val.hom k (A.obj (Opposite.op j)).hom).app
          (Opposite.op ⦋0⦌) v)) ≫
      (relativeSectionJointBaseChangeValueIso k A X j).inv =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((((relativeSectionEnrichedDiagram A).precompose
        (leftFibrationBaseChangeEnriched k)).obj j).obj X)).symm v) := by
  rw [relativeSectionJointBaseChangeValueIso_eq]
  apply (Iso.comp_inv_eq _).2
  exact (relativeSectionBaseChangeComponentIso_pointHom k A X j v).symm

end SerrePositivity.KST.Fibration
