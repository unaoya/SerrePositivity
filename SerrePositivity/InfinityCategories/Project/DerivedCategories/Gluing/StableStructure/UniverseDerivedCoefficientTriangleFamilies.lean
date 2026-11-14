module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ModuleDerivedCoefficientTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseModuleDerivedSimplexFamilies

/-! 同じ導来二単体族を、元の Hom 複体と全三辺を保って共通宇宙へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingUniverseDerivedLeftCoefficientTriangleFamily (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedSimplexFamily.{u, v, w} R C
    (homObject R C X.left Y.left) 2 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedLeftCoefficientTriangleFamily R C D M X Y)

def dgGluingUniverseDerivedRightCoefficientTriangleFamily (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedSimplexFamily.{u, v, w} R C
    (homObject R D X.right Y.right) 2
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedRightCoefficientTriangleFamily R C D M X Y)

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_zero (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y)))) :=
by
  rw [dgGluingUniverseDerivedLeftCoefficientTriangleFamily,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedSimplexFamily_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedLeftCoefficientTriangleFamily_zero R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_one (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom)) :=
by
  rw [dgGluingUniverseDerivedLeftCoefficientTriangleFamily,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedSimplexFamily_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedLeftCoefficientTriangleFamily_one R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_two (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientInput R C D M X Y)) :=
by
  rw [dgGluingUniverseDerivedLeftCoefficientTriangleFamily,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedSimplexFamily_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedLeftCoefficientTriangleFamily_two R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_zero (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientInput R C D M X Y)) :=
by
  rw [dgGluingUniverseDerivedRightCoefficientTriangleFamily,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedSimplexFamily_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedRightCoefficientTriangleFamily_zero R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_one (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom)) :=
by
  rw [dgGluingUniverseDerivedRightCoefficientTriangleFamily,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedSimplexFamily_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedRightCoefficientTriangleFamily_one R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_two (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫
        dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)))) :=
by
  rw [dgGluingUniverseDerivedRightCoefficientTriangleFamily,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedSimplexFamily_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleDerivedRightCoefficientTriangleFamily_two R C D M X Y]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedFamilyInterval_evaluate.{u, v, w} R C _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
