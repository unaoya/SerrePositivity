module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ResolvedCoefficientHomSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyIsoPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedComplexModelComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexPinchedQuasiIso

/-! 元の導来比較の実端点間 Hom と元の係数を、同じ augmentation の空間写像で結ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (c : C) (N : _root_.SerrePositivity.DifferentialGraded.RightModule R C)

def dgGluingDerivedCoefficientHomIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C
        (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R C))).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (representable R c)))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C
        (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)) ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomComplex R C c N) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedComparison_vertex R C (representable R c))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedComparison_vertex R C N) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C (representable R c))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C N)

def dgGluingDerivedCoefficientHomSpanLeft :=
  (dgGluingDerivedCoefficientHomIso R C c N).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost R C c N)

def dgGluingDerivedCoefficientHomSpanRight :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (N.obj (Opposite.op c)) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientMiddleComplex R C c N) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientYonedaPre R C c N)

lemma dgGluingDerivedCoefficientHomSpanLeft_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingDerivedCoefficientHomSpanLeft R C c N) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyEquivalence_precomp_iso_iff
    (dgGluingDerivedCoefficientHomIso R C c N) _).mpr
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost R C c N) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost_quasiIso R C c N
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_quasiIso_equivalence _

lemma dgGluingDerivedCoefficientHomSpanRight_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingDerivedCoefficientHomSpanRight R C c N) := by
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientYonedaPre R C c N) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientYonedaPre_quasiIso R C c N
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_quasiIso_equivalence _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
