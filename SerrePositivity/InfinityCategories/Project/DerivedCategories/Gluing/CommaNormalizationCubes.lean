module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationCubeIntervalFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaImageAugmentationPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaNormalizedCochainLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FunctorPinchedIntervalImage

/-! 元 comma の全 Hom 族を保持し、実正規化 cube の一面を元 augmentation、他面を明示 lift へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (F : DGFunctor R C E) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
  {K : SSet.{max u v}} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) X Y)
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F Y
local notation "NX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E (F.obj Y.source)

def dgGluingCommaPreNormalizeCube :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeCube R E IX IY
    (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (E := Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Y))

def dgGluingCommaPostNormalizeCube :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizeCube R E IX IY
    (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (E := Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Y))

lemma dgGluingCommaPreNormalizeCube_original_face :
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K)) ≫ dgGluingCommaPreNormalizeCube R C E F X Y f =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace
        (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y))) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism R C E F := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFunctorPinchedIntervalImage (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor R C E F) f
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry ((f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
      (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (E := Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Y)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Q)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex IX) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex IY)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace
      (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor R C E F) at hf
  rw [dgGluingCommaPreNormalizeCube, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeCube_interval_one,
    hf, whiskerLeft_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageAugmentationPrism R C E F]

lemma dgGluingCommaPostNormalizeCube_normalized_face :
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)) ≫ dgGluingCommaPostNormalizeCube R C E F X Y f =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry ((f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
        (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (E := Q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedHom R C E F X Y)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Q)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex NX) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex NY))) ≫
              _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (E := Q) (T := Q)
    (x := X) (y := Y) (x' := IX) (y' := IY) (x'' := NX) (y'' := NY)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizeHom R E IX IY)
  have hh : (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (E := Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Y)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Q) (E := Q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizeHom R E IX IY) =
      f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (E := Q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedHom R C E F X Y) := by
    rw [Category.assoc, ← hc]
    rfl
  rw [dgGluingCommaPostNormalizeCube, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizeCube_interval_zero, hh]
  rfl

lemma dgGluingCommaPostNormalizeCube_cochain_face :
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)) ≫ dgGluingCommaPostNormalizeCube R C E F X Y f =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry ((f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
        (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (E := Q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E X.replacement (F.obj Y.source) _
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedReplacement R C E F X Y)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedSource R C E F X Y)
          (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedNegativePrimitive_boundary R C E F X Y))) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Q)
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex NX) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex NY))) ≫
                _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) := by
  rw [dgGluingCommaPostNormalizeCube_normalized_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedHom_eq_cochainLift]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
