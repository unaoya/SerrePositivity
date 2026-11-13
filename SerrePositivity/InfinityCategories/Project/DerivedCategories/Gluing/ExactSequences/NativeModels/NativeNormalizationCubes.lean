module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeNormalizationRawCubes
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseCubeBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.UniverseTransport.UniverseHomChainMap

/-! 元の一般宇宙の gluing Hom 全体から、元加群 nerve の共通宇宙へ実正規化 cube を供給。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "E" => _root_.SerrePositivity.DifferentialGraded.RightModule R C
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R C))
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaObject R C D M Y

def dgGluingNativeNormalizationHomInput :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y) ⟶
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Q IX IY) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeIdentityCommaFunctor R C D M).map X Y)

def dgGluingNativeNormalizationCube
    (V : (Δ[1] : SSet.{max (u + 1) v}) ⊗
      (Δ[1] ⊗ (Δ[1] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R Q IX IY)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) :
    (Δ[1] : SSet.{max (u + 1) v w}) ⊗
      (Δ[1] ⊗ (Δ[1] ⊗ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y))) ⟶
          (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) :=
  (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y))) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftCubeFamily.{max (u + 1) v, max (u + 1) v w} V

def dgGluingNativePreNormalizeCube :=
  dgGluingNativeNormalizationCube R C D M X Y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeRawCube R C D M X Y)

def dgGluingNativePostNormalizeCube :=
  dgGluingNativeNormalizationCube R C D M X Y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePostNormalizeRawCube R C D M X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
