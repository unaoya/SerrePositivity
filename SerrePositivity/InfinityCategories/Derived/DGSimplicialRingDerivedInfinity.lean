module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingDGAlgebraFunctor
public import SerrePositivity.InfinityCategories.Derived.DGAlgebraPerfectMoritaInfinity
/-!
概要：単体環の実 D と Perf および準同型不変性。
方針：同じ正規化 dg 代数射の実相対 tensor を既存界面に接続する。
規約：可換性や平坦性を仮定しない。使われ方：β5(g) の正規化界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory HomologicalComplex KST.ProExcision
open AlgebraicTopology AlgebraicTopology.DoldKan
open scoped TensorProduct Simplicial
abbrev simplicialRingDerivedInfinityCategory (A : SimplicialObject RingCat.{u}) :=
  dgAlgebraDerivedInfinityCategory simplicialRingCoefficient (simplicialRingNormalizedDGAlgebra A)
abbrev simplicialRingPerfectInfinityCategory (A : SimplicialObject RingCat.{u}) :=
  dgAlgebraPerfectInfinityCategory simplicialRingCoefficient (simplicialRingNormalizedDGAlgebra A)
def simplicialRingDerivedExtensionInfinity {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) : simplicialRingDerivedInfinityCategory A ⟶
      simplicialRingDerivedInfinityCategory B :=
  dgAlgebraExtensionInfinity simplicialRingCoefficient (simplicialRingNormalizedDGAlgebraMap f)
def simplicialRingPerfectExtensionInfinity {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) : simplicialRingPerfectInfinityCategory A ⟶
      simplicialRingPerfectInfinityCategory B :=
  dgAlgebraPerfectExtensionInfinity simplicialRingCoefficient
    (simplicialRingNormalizedDGAlgebraMap f)
lemma simplicialRingDerivedExtensionInfinity_isQCatEquivalence_of_quasiIso
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (hf : QuasiIso (simplicialRingNormalizedMap f)) :
    IsQCatEquivalence (simplicialRingDerivedExtensionInfinity f) :=
  dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso simplicialRingCoefficient
    (simplicialRingNormalizedDGAlgebraMap f)
    ((simplicialRingNormalizedDGAlgebraMap_quasiIso_iff f).mpr hf)
lemma simplicialRingPerfectExtensionInfinity_isQCatEquivalence_of_quasiIso
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (hf : QuasiIso (simplicialRingNormalizedMap f)) :
    IsQCatEquivalence (simplicialRingPerfectExtensionInfinity f) :=
  dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_quasiIso simplicialRingCoefficient
    (simplicialRingNormalizedDGAlgebraMap f)
    ((simplicialRingNormalizedDGAlgebraMap_quasiIso_iff f).mpr hf)
end SerrePositivity.InfinityCategories
