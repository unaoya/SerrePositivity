module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ResolvedCoefficientHomSpan
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIsoPrecomposition
public import SerrePositivity.InfinityCategories.Derived.PinchedComplexModelComparison
public import SerrePositivity.InfinityCategories.Derived.ComplexPinchedQuasiIso

/-! 元の導来比較の実端点間 Hom と元の係数を、同じ augmentation の空間写像で結ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (c : C) (N : RightModule R C)

def dgGluingDerivedCoefficientHomIso :
    InfinityCategories.pinchedHom (X := dgModuleDerivedInfinityCategory R C)
      ((dgModuleResolvedInfinity R (RightModule R C) C
        (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌)
        (Simplex.vertex (representable R c)))
      ((dgModuleResolvedInfinity R (RightModule R C) C
        (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌) (Simplex.vertex N)) ≅
      complexPinchedSpace.{u, max (u + 1) v} (dgGluingResolvedCoefficientHomComplex R C c N) :=
  pinchedEndpointIso (dgGluingModuleDerivedComparison_vertex R C (representable R c))
      (dgGluingModuleDerivedComparison_vertex R C N) ≪≫
    pinchedComplexModelIso (dgGluingResolvedModule R C (representable R c))
      (dgGluingResolvedModule R C N)

def dgGluingDerivedCoefficientHomSpanLeft :=
  (dgGluingDerivedCoefficientHomIso R C c N).hom ≫
    complexPinchedMap.{u, max (u + 1) v} (dgGluingResolvedCoefficientHomPost R C c N)

def dgGluingDerivedCoefficientHomSpanRight :
    complexPinchedSpace.{u, max (u + 1) v} (N.obj (Opposite.op c)) ⟶
      complexPinchedSpace.{u, max (u + 1) v} (dgGluingResolvedCoefficientMiddleComplex R C c N) :=
  complexPinchedMap (dgGluingResolvedCoefficientYonedaPre R C c N)

lemma dgGluingDerivedCoefficientHomSpanLeft_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingDerivedCoefficientHomSpanLeft R C c N) := by
  apply (dgGluingHomotopyEquivalence_precomp_iso_iff
    (dgGluingDerivedCoefficientHomIso R C c N) _).mpr
  let : QuasiIso (dgGluingResolvedCoefficientHomPost R C c N) :=
    dgGluingResolvedCoefficientHomPost_quasiIso R C c N
  exact complexPinchedMap_quasiIso_equivalence _

lemma dgGluingDerivedCoefficientHomSpanRight_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingDerivedCoefficientHomSpanRight R C c N) := by
  let : QuasiIso (dgGluingResolvedCoefficientYonedaPre R C c N) :=
    dgGluingResolvedCoefficientYonedaPre_quasiIso R C c N
  exact complexPinchedMap_quasiIso_equivalence _

end SerrePositivity.InfinityCategories
