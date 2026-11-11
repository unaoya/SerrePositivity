module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetLaxInputEvaluations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetLaxArrowCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IntervalEndpointUncurry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PinchedInputCoordinateUncurry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PinchedPullbackInputEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FunctorRawIntervalEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetCompositionTriangles
/-!
概要：元の二脚の全区間評価を、同じ底座標の左右二射影で照合する。
方針：同じ実比較の全射影・端点輸送・全入力を保持する。
規約：新たな主経路仮定を置かない。使われ方：K-S• の全 lax 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetLaxHomIntervalInputMap_coordinates :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalInputBase R C D E p q X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalBaseCoordinateIso R C D E p q X Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput R C D E p q X Y) ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput R C D E p q X Y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalBaseCoordinateIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowBaseCoordinateIso, Iso.trans_hom, Iso.symm_hom,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalMappingProductIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalProductSplit,
      Category.assoc, lift_fst, tensorHom_fst]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
    simp only [← Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost_uncurry,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalEndpointIso_hom_uncurry, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalInputBase_raw_evaluation]
    simp only [Category.assoc, tensorHom_fst]
    rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomRawInputIso_inv_first_uncurry R C D E p q X Y]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput_raw_evaluation,
      reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_naturality (fst _ _),
      ← reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_precomp]
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalBaseCoordinateIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowBaseCoordinateIso, Iso.trans_hom, Iso.symm_hom,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalMappingProductIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalProductSplit,
      Category.assoc, lift_snd, tensorHom_snd]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
    simp only [← Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPost_uncurry,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalEndpointIso_hom_uncurry, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomIntervalInputBase_raw_evaluation]
    simp only [Category.assoc, tensorHom_snd]
    rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomRawInputIso_inv_second_uncurry R C D E p q X Y]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput_raw_evaluation,
      reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_naturality (snd _ _),
      ← reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry_precomp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
