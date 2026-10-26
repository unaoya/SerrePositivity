module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ExtendedNativeCocone
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoconeVertexRecovery
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ClosedEdgeRecovery
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentVertexInclusion
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyEdges

/-!
概要：coherent 終頂点付加余錐から回収する頂点射は、拡張図式の指定終頂点射。
方針：同じ実一次単体と端点移送を比較する。
規約：strict 性は不要。
使われ方：native 余錐のホモロジー脚を拡張図式へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  (A : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve (WithTerminal J)) ⟶
    dgNerve R (RightModule R D))

lemma dgBarExtendedSource_vertex (j : J) :
    dgCoherentBarSource R D (dgBarExtendedBaseDiagram R D A) ⟨0, nerveEquiv.symm j⟩ =
      coherentDiagramVertex A (nerveEquiv.symm (WithTerminal.of j)) := by
  rw [dgCoherentBarSource_vertex]
  rfl

lemma dgBarExtendedCoconeVertexMap_recover (j : J) :
    dgBarCoconeVertexModuleMap R D (dgBarExtendedBaseDiagram R D A)
        (dgBarExtendedNativeCocone R D A) (nerveEquiv.symm j) =
      eqToHom (congrArg (ForgetEnrichment.of (Complex R)) (dgBarExtendedSource_vertex R D A j)) ≫
        dgCoherentBarDiagramEdge R D A (WithTerminal.homFrom j) ≫
          eqToHom (congrArg (ForgetEnrichment.of (Complex R))
            (dgBarExtendedNativeCocone_module R D A).symm) := by
  rw [dgBarCoconeVertexModuleMap_eq]
  let e := (UniverseEdge.up.{u, max (u + 1) v} (X := nerve (WithTerminal J))
    (CategoryTheory.nerve.edgeMk (WithTerminal.homFrom j)).toTruncated).map
      ((SSet.truncation 2).map A)
  have he : e.edge = dgCoherentBarCoconeSimplex R D (dgBarExtendedBaseDiagram R D A)
      (dgBarExtendedNativeCocone R D A) (nerveEquiv.symm j) :=
    (dgBarExtendedNativeCocone_simplex_zero R D A j).symm
  exact dgBarEdgeClosed_recover_transport R D e he
    (dgCoherentBarCoconeSimplex_source R D _ _ _) (dgCoherentBarCoconeSimplex_last R D _ _ _)
    (dgBarExtendedSource_vertex R D A j) (dgBarExtendedNativeCocone_module R D A)

lemma dgBarExtendedCoconeVertexMap_naturality (j : J) :
    dgBarCoconeVertexModuleMap R D (dgBarExtendedBaseDiagram R D A)
        (dgBarExtendedNativeCocone R D A) (nerveEquiv.symm j) ≫
      eqToHom (congrArg (ForgetEnrichment.of (Complex R))
        (dgBarExtendedNativeCocone_module R D A)) =
    eqToHom (congrArg (ForgetEnrichment.of (Complex R)) (dgBarExtendedSource_vertex R D A j)) ≫
      dgCoherentBarDiagramEdge R D A (WithTerminal.homFrom j) := by
  rw [dgBarExtendedCoconeVertexMap_recover]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories
