module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictResolutionDiagramIso
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyHomotopyIso

/-!
概要：正本の実導来関手の augmentation を、元の全加群図式へ直接接続する。
方針：同じ出力分解の全単体 augmentation と閉零ラベルの付け外しを使う。
規約：比較対象を別の分解関手の頂点へ変更しない。
使われ方：正本の strict 図式と同じ余錐・頂点の C2 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarOutputAugmentation_vertex_mem
    {C : Type (max (u + 1) v)} [DGCategory R C] (F : DGFunctor R C (RightModule R D))
    (x : (dgNerve R C) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (dgModuleResolvedAugmentationHomotopy R C D F) x).edge ∈
      dgModuleQuasiIsomorphismEdges R D := by
  obtain ⟨M, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := C)).symm.surjective x
  let Q := dgModuleOutputResolutionObject R C D F M
  refine ⟨_, _, Q.augmentation, Q.quasiIso, ?_⟩
  exact (dgModuleResolvedAugmentationHomotopy_vertex_edge R C D F M).symm

def dgBarDerivedAugmentationHomotopy : SSet.Homotopy
    (dgBarRightModuleDerived R D ≫ dgNerve.map
      (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)))
    (𝟙 (dgNerve R (RightModule R D))) := by
  let H := functorHomotopyPrecomp
    (dgModuleResolvedAugmentationHomotopy R (ModuleCategory R D) D (dgConeModuleForget R D))
    (dgNerve.map (dgBarRightModuleRelabel R D))
  exact { h := H.h
          h₀ := H.h₀
          h₁ := H.h₁.trans (by
            rw [← dgNerve.map_comp, dgBarRightModuleRelabel_forget, dgNerve.map_id]
            rfl)
          rel := H.rel }

lemma dgBarDerivedAugmentationHomotopy_vertex_mem
    (x : (dgNerve R (RightModule R D)) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (dgBarDerivedAugmentationHomotopy R D) x).edge ∈
      dgModuleQuasiIsomorphismEdges R D := by
  change (simplicialHomotopyVertexEdge (functorHomotopyPrecomp
    (dgModuleResolvedAugmentationHomotopy R (ModuleCategory R D) D (dgConeModuleForget R D))
    (dgNerve.map (dgBarRightModuleRelabel R D))) x).edge ∈ dgModuleQuasiIsomorphismEdges R D
  rw [simplicialHomotopyVertexEdge_precomp_edge]
  exact dgBarOutputAugmentation_vertex_mem R D _ _

variable {J : Type u} [Category.{u} J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ dgNerve R (RightModule R D))

abbrev dgBarDerivedCoherentDiagram := G ≫ dgBarRightModuleDerived R D ≫ dgNerve.map
  (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D))

def dgBarDerivedCoherentAugmentation : SSet.Homotopy (dgBarDerivedCoherentDiagram R D G) G := by
  let H := functorHomotopyPrecomp (dgBarDerivedAugmentationHomotopy R D) G
  exact { h := H.h
          h₀ := H.h₀
          h₁ := by simpa only [Category.comp_id] using! H.h₁
          rel := H.rel }

lemma dgBarDerivedCoherentAugmentation_vertex_mem (j : J) :
    (simplicialHomotopyVertexEdge (dgBarDerivedCoherentAugmentation R D G)
      (ULift.up (nerveEquiv.symm j))).edge ∈ dgModuleQuasiIsomorphismEdges R D := by
  change (simplicialHomotopyVertexEdge
    (functorHomotopyPrecomp (dgBarDerivedAugmentationHomotopy R D) G)
      (ULift.up (nerveEquiv.symm j))).edge ∈ dgModuleQuasiIsomorphismEdges R D
  rw [simplicialHomotopyVertexEdge_precomp_edge]
  exact dgBarDerivedAugmentationHomotopy_vertex_mem R D _

def dgBarDerivedCoherentHomologyIso (x : D) (q : ℤ) :
    dgCoherentBarHomologyDiagram R D (dgBarDerivedCoherentDiagram R D G) x q ≅
      dgCoherentBarHomologyDiagram R D G x q :=
  dgCoherentBarHomologyHomotopyIso R D (dgBarDerivedCoherentAugmentation R D G)
    (fun j => dgBarEdgeClosed_quasiIso_of_mem R D _
      (dgBarDerivedCoherentAugmentation_vertex_mem R D G j)) x q

end SerrePositivity.InfinityCategories
