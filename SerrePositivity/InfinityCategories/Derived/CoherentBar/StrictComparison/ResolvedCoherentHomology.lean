module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.QuasiIsoEdgeRecovery
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyHomotopyIso

/-!
概要：実半自由分解した coherent 図式の頂点ホモロジーを元の図式へ比較する。
方針：元の全分解 augmentation を前合成し、同じ準同型辺を回収する。
規約：poset 上でも分解後の図式を strict と仮定しない。
使われ方：filtered strict 余極限比較のホモロジー側。
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

abbrev dgBarModuleResolution :=
  dgModuleResolvedInfinity R (RightModule R D) D (DGFunctor.id (RightModule R D))

variable {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgModuleNerve R D)

abbrev dgBarResolvedCoherentDiagram := G ≫ dgBarModuleResolution R D ≫ dgNerve.map
  (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D))

def dgBarResolvedCoherentAugmentation : SSet.Homotopy (dgBarResolvedCoherentDiagram R D G) G := by
  let h := functorHomotopyPrecomp (dgModuleResolutionAugmentationHomotopy R D) G
  exact { h := h.h
          h₀ := h.h₀
          h₁ := by simpa only [Category.comp_id] using! h.h₁
          rel := h.rel }

lemma dgBarResolvedCoherentAugmentation_vertex_mem (s : I _⦋0⦌) :
    (simplicialHomotopyVertexEdge (dgBarResolvedCoherentAugmentation R D G)
      (ULift.up s)).edge ∈ dgModuleQuasiIsomorphismEdges R D := by
  change (simplicialHomotopyVertexEdge
    (functorHomotopyPrecomp (dgModuleResolutionAugmentationHomotopy R D) G) (ULift.up s)).edge ∈ _
  rw [simplicialHomotopyVertexEdge_precomp_edge]
  exact dgModuleResolutionAugmentationHomotopy_vertex_mem R D _

variable {J : Type u} [Category.{u} J]
  (H : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ dgModuleNerve R D)

def dgBarResolvedCoherentHomologyIso (x : D) (q : ℤ) :
    dgCoherentBarHomologyDiagram R D (dgBarResolvedCoherentDiagram R D H) x q ≅
      dgCoherentBarHomologyDiagram R D H x q :=
  dgCoherentBarHomologyHomotopyIso R D (dgBarResolvedCoherentAugmentation R D H)
    (fun j => dgBarEdgeClosed_quasiIso_of_mem R D _
      (dgBarResolvedCoherentAugmentation_vertex_mem R D H (nerveEquiv.symm j))) x q

end SerrePositivity.InfinityCategories
