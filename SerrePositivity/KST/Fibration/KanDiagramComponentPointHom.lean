module
public import SerrePositivity.KST.Fibration.KanPointComponentComposition
public import SerrePositivity.KST.Fibration.PointedTransformationPointHom
public import SerrePositivity.KST.Fibration.FunctorIsoComponent
public import SerrePositivity.InfinityCategories.F1.KanDiagramNaturalTransformation

/-! # 元の Kan 変換の同じ指定成分は、その元の係数点の射を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {F G : KanDiagramObject I}
  (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
  (hη : ∀ c, IsQCatEquivalence (X := (F.val.obj c).obj) (Y := (G.val.obj c).obj) (η.app c))

/-- 同じ図式変換の指定成分を、元の二つの Kan 値の標準頂点で表示する。 -/
def kanDiagramComponentValueIso (i : I) :
    VertexIso (spaceInfinityVertex (F.val.obj i)) (spaceInfinityVertex (G.val.obj i)) :=
  (eqToIso (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex F.val i))).symm ≪≫
    (kanDiagramFunctorIsoOfPointwise η hη).app (ULift.up (nerveVertex i)) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex G.val i))

/-- 同じ指定成分の順方向射は、元の係数射の coherent な辺の類。 -/
theorem kanDiagramComponentValueIso_hom (i : I) :
    (kanDiagramComponentValueIso η hη i).hom =
      Truncated.HomotopyCategory.homMk
        (((coherentNerveEdge (show F.val.obj i ⟶ G.val.obj i from η.app i)).ofEq
          (spaceInfinityVertex_eq_coherent (F.val.obj i)).symm
          (spaceInfinityVertex_eq_coherent (G.val.obj i)).symm).toTruncated) := by
  simp only [kanDiagramComponentValueIso, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
    eqToIso.hom, functorIso_app_hom_evaluate]
  change eqToHom (congrArg HomotopyCategory.mk
      (kanDiagramCoherentNerve_vertex F.val i)).symm ≫
    functorHomEvaluate (kanDiagramFunctorIsoOfPointwise η hη).hom (ULift.up (nerveVertex i)) ≫
    eqToHom (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex G.val i)) = _
  rw [show (kanDiagramFunctorIsoOfPointwise η hη).hom =
    Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated from rfl,
    functorHomEvaluate_edge_hom]
  exact homMk_transport (kanDiagramCoherentNerve_vertex F.val i)
    (kanDiagramCoherentNerve_vertex G.val i) _ _ (kanDiagramNaturalTransformationEdge_at η i)

/-- 元の係数点の射は、同じ図式同型の指定成分で元の像の点の射へ移る。 -/
theorem kanDiagramComponentValueIso_pointHom (i : I) (v : (F.val.obj i).obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv (F.val.obj i)).symm v) ≫
      (kanDiagramComponentValueIso η hη i).hom =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv (G.val.obj i)).symm
      ((η.app i).app (Opposite.op ⦋0⦌) v)) := by
  rw [kanDiagramComponentValueIso_hom]
  exact kanPointHom_comp_of_edge (show F.val.obj i ⟶ G.val.obj i from η.app i) _ rfl v

end SerrePositivity.KST.Fibration
