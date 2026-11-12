module

public import SerrePositivity.Spectra.Stable.LocalizingMaps
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AdjunctionHom
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # The simplicial Hom test of stabilization is the adjoint bonding map

This comparison is an isomorphism of actual arrows of simplicial sets,
for every cosimplicial object in C and every spectrum. No stable model or
Omega-spectrum characterization is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.GeneralSymmetricSpectrum

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] (K : C)

def bondingAdjunction (n : ℕ) :
    tensorRight K ⋙ freeAt (K := K) (n + 1) ⊣ evaluation (K := K) (n + 1) ⋙ ihom K :=
  ((ihom.adjunction K).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight K)).comp
    (freeAtAdjunction (K := K) (n + 1))

lemma bondingAdjunction_homEquiv (n : ℕ) (A : C) (E : GeneralSymmetricSpectrum C K)
    (f : (tensorRight K ⋙ freeAt (K := K) (n + 1)).obj A ⟶ E) :
    (bondingAdjunction (C := C) K n).homEquiv A E f =
      curry ((β_ K A).hom ≫ freeAtHomEquiv (n + 1) (A ⊗ K) E f) := by
  rw [bondingAdjunction, Adjunction.comp_homEquiv]
  change (((ihom.adjunction K).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight K)).homEquiv A _)
      ((freeAtAdjunction (K := K) (n + 1)).homEquiv _ E f) = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  rfl

def localizingHomArrowIso (n : ℕ) (A : SimplexCategory ⥤ C)
    (E : GeneralSymmetricSpectrum C K) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (Functor.whiskerLeft A (stabilizationMap K n))).app E) ≅
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map (adjointStructureMap E n)) :=
  Arrow.isoMk
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIsoSameUniverse (freeAtAdjunction (K := K) n) A).app E)
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIsoSameUniverse (bondingAdjunction K n) A).app E) (by
      ext m f
      change freeAtHomEquiv n (A.obj m.unop) E f ≫ adjointStructureMap E n =
        (bondingAdjunction K n).homEquiv (A.obj m.unop) E (localizingMap K n _ ≫ f)
      rw [bondingAdjunction_homEquiv, localizingMap_adjoint])

end SerrePositivity.SpectrumStabilization
