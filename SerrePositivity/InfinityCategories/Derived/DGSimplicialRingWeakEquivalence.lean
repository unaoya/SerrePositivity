module
public import SerrePositivity.InfinityCategories.Derived.ModuleNormalizedWeakEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingPiMoore
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingDerivedInfinity
/-!
概要：任意非可換単体環の実 dg 代数化と D・Perf の弱同値不変性。
方針：元の射と全基点の誘導写像を保ち、既存の実 Whitehead 逆へ接続する。
規約：可換性・平坦性を仮定しない。使われ方：β5(g) の正規化界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology Opposite
open KST.Spectra
open scoped Simplicial
abbrev simplicialRingUnderlyingMap {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    KST.Comparison.ringSpace A ⟶ KST.Comparison.ringSpace B :=
  Functor.whiskerRight f (forget RingCat)
lemma simplicialRingNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    QuasiIso (simplicialRingNormalizedMap f) ↔
      IsWeakHomotopyEquivalence (simplicialRingUnderlyingMap f) :=
  moduleNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence (simplicialRingIntegerModuleMap f)
lemma simplicialRingNormalizedDGAlgebraMap_quasiIso_iff_isWeakHomotopyEquivalence
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    QuasiIso (simplicialRingNormalizedDGAlgebraMap f).hom ↔
      IsWeakHomotopyEquivalence (simplicialRingUnderlyingMap f) :=
  (simplicialRingNormalizedDGAlgebraMap_quasiIso_iff f).trans
    (simplicialRingNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence f)
lemma simplicialRingDerivedExtensionInfinity_isQCatEquivalence_of_weakHomotopyEquivalence
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (hf : IsWeakHomotopyEquivalence (simplicialRingUnderlyingMap f)) :
    IsQCatEquivalence (simplicialRingDerivedExtensionInfinity f) :=
  simplicialRingDerivedExtensionInfinity_isQCatEquivalence_of_quasiIso f
    ((simplicialRingNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence f).mpr hf)
lemma simplicialRingPerfectExtensionInfinity_isQCatEquivalence_of_weakHomotopyEquivalence
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (hf : IsWeakHomotopyEquivalence (simplicialRingUnderlyingMap f)) :
    IsQCatEquivalence (simplicialRingPerfectExtensionInfinity f) :=
  simplicialRingPerfectExtensionInfinity_isQCatEquivalence_of_quasiIso f
    ((simplicialRingNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence f).mpr hf)
end SerrePositivity.InfinityCategories
