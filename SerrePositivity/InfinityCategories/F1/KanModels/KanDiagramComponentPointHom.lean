module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointComponentComposition
public import SerrePositivity.InfinityCategories.F1.Transport.PointedTransformationPointHom
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoComponent
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramNaturalTransformation

/-! # 元の Kan 変換の同じ指定成分は、その元の係数点の射を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.KanModels
open SerrePositivity.KST.Fibration
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
    (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso η hη i).hom =
      Truncated.HomotopyCategory.homMk
        (((coherentNerveEdge (show F.val.obj i ⟶ G.val.obj i from η.app i)).ofEq
          (spaceInfinityVertex_eq_coherent (F.val.obj i)).symm
          (spaceInfinityVertex_eq_coherent (G.val.obj i)).symm).toTruncated) := by
  simp only [_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
    eqToIso.hom, _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIso_app_hom_evaluate]
  change eqToHom (congrArg HomotopyCategory.mk
      (kanDiagramCoherentNerve_vertex F.val i)).symm ≫
    functorHomEvaluate (kanDiagramFunctorIsoOfPointwise η hη).hom (ULift.up (nerveVertex i)) ≫
    eqToHom (congrArg HomotopyCategory.mk (kanDiagramCoherentNerve_vertex G.val i)) = _
  rw [show (kanDiagramFunctorIsoOfPointwise η hη).hom =
    Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge η).toTruncated from rfl,
    _root_.SerrePositivity.InfinityCategories.F1.Transport.functorHomEvaluate_edge_hom]
  exact homMk_transport (kanDiagramCoherentNerve_vertex F.val i)
    (kanDiagramCoherentNerve_vertex G.val i) _ _ (kanDiagramNaturalTransformationEdge_at η i)

/-- 元の係数点の射は、同じ図式同型の指定成分で元の像の点の射へ移る。 -/
theorem kanDiagramComponentValueIso_pointHom (i : I) (v : (F.val.obj i).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv (F.val.obj i)).symm v) ≫
      (_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso η hη i).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv (G.val.obj i)).symm
      ((η.app i).app (Opposite.op ⦋0⦌) v)) := by
  rw [_root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso_hom]
  exact _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanPointHom_comp_of_edge (show F.val.obj i ⟶ G.val.obj i from η.app i) _ rfl v

end SerrePositivity.InfinityCategories.F1.KanModels

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramComponentValueIso := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramComponentValueIso_hom := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramComponentValueIso_pointHom := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso_pointHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramComponentValueIso._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramComponentValueIso._proof_2 := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramComponentValueIso._proof_3 := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.kanDiagramComponentValueIso.eq_1 := _root_.SerrePositivity.InfinityCategories.F1.KanModels.kanDiagramComponentValueIso.eq_1
