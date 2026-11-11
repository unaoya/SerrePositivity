module

public import SerrePositivity.KST.LocalizingInvariants.FiberMappingFibration
public import SerrePositivity.KST.LocalizingInvariants.SpectrumComponentClass
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools

/-!
概要：指定した BF 写像空間の辺を、段ごとの fibration の後合成へ持ち上げる。
方針：全写像空間の Kan fibration に辺を持ち上げ、終点を同じ BF 射へ復号する。
規約：射影された全区間を指定のまま保持。使われ方：coherent 右辺比較の厳密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberMapping

variable {X Y Z : OmegaSpectrum.{u}} (p : Y ⟶ Z) (a : X ⟶ Y) (b : X ⟶ Z)
  (γ : (mappingSpace X Z).Edge (vertexOfHom (a ≫ p)) (vertexOfHom b))

structure PathLift where
  map : X ⟶ Y
  fac : map ≫ p = b
  path : (mappingSpace X Y).Edge (vertexOfHom a) (vertexOfHom map)
  «over» : SSet.yonedaEquiv.symm path.edge ≫ SpectrumMappingAcyclic.post X p =
    SSet.yonedaEquiv.symm γ.edge

def pathLift (hp : ∀ n, Fibration (p.app n).right) : PathLift p a b γ := by
  apply Classical.choice
  let q := SpectrumMappingAcyclic.post X p
  let : Fibration q := spectrumPost_fibration X p hp
  let e := (γ.ofEq (SpectrumMappingAcyclic.post_vertex a p).symm rfl).toTruncated
  obtain ⟨F, hF₀, hFq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftEdge_source q (vertexOfHom a) e
  let v := (mappingSpace X Y).δ 0 (SSet.yonedaEquiv F)
  let r := homOfVertex v
  have hr : vertexOfHom r = v := vertexOfHom_homOfVertex v
  have he : q.app (Opposite.op ⦋0⦌) v = vertexOfHom b := by
    calc
      _ = (mappingSpace X Z).δ 0
          (q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F)) :=
        ConcreteCategory.congr_hom (q.naturality (SimplexCategory.δ 0).op)
          (SSet.yonedaEquiv F)
      _ = (mappingSpace X Z).δ 0 e.edge := by
        rw [← SSet.yonedaEquiv_comp, hFq]
        exact congrArg (fun t : (mappingSpace X Z) _⦋1⦌ ↦ (mappingSpace X Z).δ 0 t)
          ((SSet.yonedaEquiv (X := mappingSpace X Z) (n := ⦋1⦌)).apply_symm_apply e.edge)
      _ = vertexOfHom b := e.tgt_eq
  have hfac : r ≫ p = b := by
    apply (homVertexEquiv X Z).injective
    change vertexOfHom (r ≫ p) = vertexOfHom b
    rw [← SpectrumMappingAcyclic.post_vertex, hr]
    exact he
  let P : (mappingSpace X Y).Edge (vertexOfHom a) (vertexOfHom r) :=
    SSet.Edge.mk (SSet.yonedaEquiv F)
      (by rw [← stdSimplex.yonedaEquiv_δ_comp, hF₀, Equiv.apply_symm_apply])
      hr.symm
  refine ⟨⟨r, hfac, P, ?_⟩⟩
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv F) ≫ q =
    SSet.yonedaEquiv.symm e.edge
  rw [Equiv.symm_apply_apply]
  exact hFq

namespace PathLift

lemma component (L : PathLift p a b γ) :
    SpectrumMappingAcyclic.component a = SpectrumMappingAcyclic.component L.map :=
  π₀.sound L.path

lemma hom (L : PathLift p a b γ) : SpectrumHo.hom a = SpectrumHo.hom L.map :=
  SpectrumHo.hom_eq_of_component_eq _ _ (L.component)

lemma homotopyMap (L : PathLift p a b γ) (j : ℤ) :
    OmegaSpectrum.homotopyMap a j = OmegaSpectrum.homotopyMap L.map j :=
  SpectrumHo.homotopyMap_eq_of_hom_eq _ _ L.hom j

end PathLift
end SerrePositivity.KST.LocalizingInvariants.FiberMapping
