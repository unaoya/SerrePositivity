module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxInputEvaluations
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxArrowCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalEndpointUncurry
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedInputCoordinateUncurry
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedPullbackInputEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.FunctorRawIntervalEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCompositionTriangles
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetLaxHomIntervalInputMap_coordinates :
    (dgGluingHomTargetLaxHomRawInputIso R C D E p q X Y).inv ≫
      dgGluingHomTargetLaxHomIntervalInputBase R C D E p q X Y ≫
        (dgGluingHomTargetLaxHomIntervalBaseCoordinateIso R C D E p q X Y).hom =
      (dgGluingHomTargetLeftIntervalInput R C D E p q X Y) ⊗ₘ
        (dgGluingHomTargetRightIntervalInput R C D E p q X Y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [dgGluingHomTargetLaxHomIntervalBaseCoordinateIso, dgGluingArrowBaseCoordinateIso, Iso.trans_hom, Iso.symm_hom,
      dgGluingIntervalMappingProductIso, dgGluingIntervalProductSplit,
      Category.assoc, lift_fst, tensorHom_fst]
    apply intervalMappingUncurry_injective _ _
    simp only [← Category.assoc]
    rw [intervalMappingPost_uncurry,
      dgGluingIntervalEndpointIso_hom_uncurry, dgGluingHomTargetLaxHomIntervalInputBase_raw_evaluation]
    simp only [Category.assoc, tensorHom_fst]
    rw [reassoc_of% dgGluingHomTargetLaxHomRawInputIso_inv_first_uncurry R C D E p q X Y]
    rw [intervalMappingUncurry_precomp, dgGluingHomTargetLeftIntervalInput_raw_evaluation,
      reassoc_of% rightMappingSpacePrism_naturality (fst _ _),
      ← reassoc_of% pinchedHomUncurry_precomp]
  · simp only [dgGluingHomTargetLaxHomIntervalBaseCoordinateIso, dgGluingArrowBaseCoordinateIso, Iso.trans_hom, Iso.symm_hom,
      dgGluingIntervalMappingProductIso, dgGluingIntervalProductSplit,
      Category.assoc, lift_snd, tensorHom_snd]
    apply intervalMappingUncurry_injective _ _
    simp only [← Category.assoc]
    rw [intervalMappingPost_uncurry,
      dgGluingIntervalEndpointIso_hom_uncurry, dgGluingHomTargetLaxHomIntervalInputBase_raw_evaluation]
    simp only [Category.assoc, tensorHom_snd]
    rw [reassoc_of% dgGluingHomTargetLaxHomRawInputIso_inv_second_uncurry R C D E p q X Y]
    rw [intervalMappingUncurry_precomp, dgGluingHomTargetRightIntervalInput_raw_evaluation,
      reassoc_of% rightMappingSpacePrism_naturality (snd _ _),
      ← reassoc_of% pinchedHomUncurry_precomp]
end SerrePositivity.InfinityCategories
