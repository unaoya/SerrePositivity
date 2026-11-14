module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ResolvedCoefficientMappingSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ComplexPinchedUniverseNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseDerivedStructure
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Homotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.PinchedHom

/-! 元の一般宇宙の導来比較の実端点間 Hom と元の係数の実 augmentation span。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (c : C) (N : _root_.SerrePositivity.DifferentialGraded.RightModule R C)

def dgGluingUniverseDerivedCoefficientHomIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      (X := (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (representable R c))))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N))) ≅
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v}
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomComplex R C c N)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftPinchedHomIso.{max (u + 1) v, max (u + 1) v w}
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C
      (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R C))).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (representable R c)))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R C) C
      (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N))).symm ≪≫
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).mapIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientHomIso R C c N)

def dgGluingUniverseDerivedCoefficientHomSpanLeft :=
  (dgGluingUniverseDerivedCoefficientHomIso.{u, v, w} R C c N).hom ≫
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost R C c N))

def dgGluingUniverseDerivedCoefficientHomSpanRight :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (N.obj (Opposite.op c))) ⟶
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v}
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientMiddleComplex R C c N)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v}
    (N.obj (Opposite.op c))).hom ≫
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientHomSpanRight R C c N)

lemma dgGluingUniverseDerivedCoefficientHomSpanLeft_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (dgGluingUniverseDerivedCoefficientHomSpanLeft.{u, v, w} R C c N) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyEquivalence_precomp_iso_iff
    (dgGluingUniverseDerivedCoefficientHomIso.{u, v, w} R C c N) _).mpr
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost R C c N) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost_quasiIso R C c N
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_quasiIso_equivalence.{u, max (u + 1) v}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost R C c N)).ulift

lemma dgGluingUniverseDerivedCoefficientHomSpanRight_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c N) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyEquivalence_precomp_iso_iff
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v}
      (N.obj (Opposite.op c))) _).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientHomSpanRight_equivalence R C c N).ulift

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
