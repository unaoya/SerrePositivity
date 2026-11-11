module

public import SerrePositivity.KST.Spectra.CoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTriangleEdge

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

namespace SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPrism

local instance triangleMappingSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

open OmegaSpectrum

def triangleEdge {X Y Z : OmegaSpectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (s : Sp.{u} _⦋2⦌)
    (h₂ : Sp.δ 2 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (h₀ : Sp.δ 0 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge)
    (h₁ : Sp.δ 1 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h).edge) :
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
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (Sp.δ 2 s) = f := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData h₂
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow] at h
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (Sp.δ 0 s) = g := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData h₀
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow] at h
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (Sp.δ 1 s) = h := by
    have he := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData h₁
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow] at he
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentTriangleEdge s
  dsimp only [Sp] at hf hg hh
  rw [hf, hg, hh] at e
  have hv (r : s.obj ⟨ULift.up 0⟩ ⟶ s.obj ⟨ULift.up 2⟩) :
      SimplicialCategory.homEquiv' _ _ r = vertexOfHom r := by
    change (SSet.unitHomEquiv _)
      ((SSet.unitHomEquiv _).symm (vertexOfHom r)) = vertexOfHom r
    exact Equiv.apply_symm_apply _ _
  exact e.ofEq (hv h) (hv (f ≫ g))


end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPrism
