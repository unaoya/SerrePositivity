module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ModuleNormalizedWeakEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingPiMoore
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingDerivedInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology Opposite
open KST.Spectra
open scoped _root_.Simplicial
abbrev simplicialRingUnderlyingMap {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    KST.Comparison.ringSpace A ⟶ KST.Comparison.ringSpace B :=
  Functor.whiskerRight f (forget RingCat)
lemma simplicialRingNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (simplicialRingUnderlyingMap f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.moduleNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModuleMap f)
lemma simplicialRingNormalizedDGAlgebraMap_quasiIso_iff_isWeakHomotopyEquivalence
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebraMap f).hom ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (simplicialRingUnderlyingMap f) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebraMap_quasiIso_iff f).trans
    (simplicialRingNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence f)
lemma simplicialRingDerivedExtensionInfinity_isQCatEquivalence_of_weakHomotopyEquivalence
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (simplicialRingUnderlyingMap f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDerivedExtensionInfinity f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDerivedExtensionInfinity_isQCatEquivalence_of_quasiIso f
    ((simplicialRingNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence f).mpr hf)
lemma simplicialRingPerfectExtensionInfinity_isQCatEquivalence_of_weakHomotopyEquivalence
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (simplicialRingUnderlyingMap f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingPerfectExtensionInfinity f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingPerfectExtensionInfinity_isQCatEquivalence_of_quasiIso f
    ((simplicialRingNormalizedMap_quasiIso_iff_isWeakHomotopyEquivalence f).mpr hf)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
