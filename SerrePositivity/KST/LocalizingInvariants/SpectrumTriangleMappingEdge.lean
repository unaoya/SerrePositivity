module

public import SerrePositivity.KST.Spectra.CoherentNerve
public import SerrePositivity.InfinityCategories.F1.CatInfinity.CoherentTriangleEdge

/-!
概要：Sp の指定した三辺を持つ二単体から、元の全 BF 写像空間の辺を読む。
方針：三つの頂点と元の BF 射を照合し、coherent な精密化の像を輸送する。
規約：二単体の指定された辺を保持。使われ方：図式の prism の右辺の厳密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open SerrePositivity.InfinityCategories.F2
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPrism

local instance triangleMappingSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

open OmegaSpectrum

def triangleEdge {X Y Z : OmegaSpectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (s : Sp.{u} _⦋2⦌)
    (h₂ : Sp.δ 2 s = (coherentNerveEdge f).edge)
    (h₀ : Sp.δ 0 s = (coherentNerveEdge g).edge)
    (h₁ : Sp.δ 1 s = (coherentNerveEdge h).edge) :
    (mappingSpace X Z).Edge (vertexOfHom h) (vertexOfHom (f ≫ g)) := by
  have hx : s.obj ⟨ULift.up 0⟩ = X :=
    congrArg (fun t : Sp.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 0⟩) h₂
  have hy : s.obj ⟨ULift.up 1⟩ = Y :=
    congrArg (fun t : Sp.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h₂
  have hz : s.obj ⟨ULift.up 2⟩ = Z :=
    congrArg (fun t : Sp.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h₀
  subst X
  subst Y
  subst Z
  have hf : coherentEdgeHom (Sp.δ 2 s) = f := by
    have h := congrArg coherentNerveArrowData h₂
    rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow] at h
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hg : coherentEdgeHom (Sp.δ 0 s) = g := by
    have h := congrArg coherentNerveArrowData h₀
    rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow] at h
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hh : coherentEdgeHom (Sp.δ 1 s) = h := by
    have he := congrArg coherentNerveArrowData h₁
    rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow] at he
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
  have e := F2.coherentTriangleEdge s
  dsimp only [Sp] at hf hg hh
  rw [hf, hg, hh] at e
  have hv (r : s.obj ⟨ULift.up 0⟩ ⟶ s.obj ⟨ULift.up 2⟩) :
      SimplicialCategory.homEquiv' _ _ r = vertexOfHom r := by
    change (SSet.unitHomEquiv _)
      ((SSet.unitHomEquiv _).symm (vertexOfHom r)) = vertexOfHom r
    exact Equiv.apply_symm_apply _ _
  exact e.ofEq (hv h) (hv (f ≫ g))


end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPrism
