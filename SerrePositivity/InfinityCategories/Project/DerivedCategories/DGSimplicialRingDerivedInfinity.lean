module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingDGAlgebraFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPerfectMoritaInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory HomologicalComplex
open AlgebraicTopology AlgebraicTopology.DoldKan
open scoped TensorProduct _root_.Simplicial
abbrev simplicialRingDerivedInfinityCategory (A : SimplicialObject RingCat.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraDerivedInfinityCategory _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebra A)
abbrev simplicialRingPerfectInfinityCategory (A : SimplicialObject RingCat.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectInfinityCategory _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebra A)
def simplicialRingDerivedExtensionInfinity {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) : simplicialRingDerivedInfinityCategory A ⟶
      simplicialRingDerivedInfinityCategory B :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraExtensionInfinity _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebraMap f)
def simplicialRingPerfectExtensionInfinity {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) : simplicialRingPerfectInfinityCategory A ⟶
      simplicialRingPerfectInfinityCategory B :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectExtensionInfinity _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebraMap f)
lemma simplicialRingDerivedExtensionInfinity_isQCatEquivalence_of_quasiIso
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (hf : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (simplicialRingDerivedExtensionInfinity f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebraMap f)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebraMap_quasiIso_iff f).mpr hf)
lemma simplicialRingPerfectExtensionInfinity_isQCatEquivalence_of_quasiIso
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B)
    (hf : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (simplicialRingPerfectExtensionInfinity f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_quasiIso _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebraMap f)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGAlgebraMap_quasiIso_iff f).mpr hf)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
