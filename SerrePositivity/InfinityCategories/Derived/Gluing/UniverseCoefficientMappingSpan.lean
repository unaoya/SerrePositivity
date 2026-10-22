module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ResolvedCoefficientMappingSpan
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedUniverseNaturality
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedStructure
public import SerrePositivity.InfinityCategories.F1.UniverseHomotopy
public import SerrePositivity.InfinityCategories.F1.UniversePinchedHom

/-! 元の一般宇宙の導来比較の実端点間 Hom と元の係数の実 augmentation span。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (c : C) (N : RightModule R C)

def dgGluingUniverseDerivedCoefficientHomIso :
    InfinityCategories.pinchedHom
      (X := (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (dgModuleDerivedInfinityCategory R C))
      ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex (representable R c))))
      ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex N))) ≅
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (complexPinchedSpace.{u, max (u + 1) v}
          (dgGluingResolvedCoefficientHomComplex R C c N)) :=
  (uliftPinchedHomIso.{max (u + 1) v, max (u + 1) v w}
    ((dgModuleResolvedInfinity R (RightModule R C) C
      (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌)
      (Simplex.vertex (representable R c)))
    ((dgModuleResolvedInfinity R (RightModule R C) C
      (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌) (Simplex.vertex N))).symm ≪≫
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).mapIso
      (dgGluingDerivedCoefficientHomIso R C c N)

def dgGluingUniverseDerivedCoefficientHomSpanLeft :=
  (dgGluingUniverseDerivedCoefficientHomIso.{u, v, w} R C c N).hom ≫
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
      (complexPinchedMap.{u, max (u + 1) v} (dgGluingResolvedCoefficientHomPost R C c N))

def dgGluingUniverseDerivedCoefficientHomSpanRight :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (N.obj (Opposite.op c))) ⟶
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (complexPinchedSpace.{u, max (u + 1) v}
          (dgGluingResolvedCoefficientMiddleComplex R C c N)) :=
  (dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v}
    (N.obj (Opposite.op c))).hom ≫
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (dgGluingDerivedCoefficientHomSpanRight R C c N)

lemma dgGluingUniverseDerivedCoefficientHomSpanLeft_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingUniverseDerivedCoefficientHomSpanLeft.{u, v, w} R C c N) := by
  apply (dgGluingHomotopyEquivalence_precomp_iso_iff
    (dgGluingUniverseDerivedCoefficientHomIso.{u, v, w} R C c N) _).mpr
  let : QuasiIso (dgGluingResolvedCoefficientHomPost R C c N) :=
    dgGluingResolvedCoefficientHomPost_quasiIso R C c N
  exact (complexPinchedMap_quasiIso_equivalence.{u, max (u + 1) v}
    (dgGluingResolvedCoefficientHomPost R C c N)).ulift

lemma dgGluingUniverseDerivedCoefficientHomSpanRight_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c N) := by
  apply (dgGluingHomotopyEquivalence_precomp_iso_iff
    (dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v}
      (N.obj (Opposite.op c))) _).mpr
  exact (dgGluingDerivedCoefficientHomSpanRight_equivalence R C c N).ulift

end SerrePositivity.InfinityCategories
