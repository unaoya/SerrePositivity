module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomIntervalBaseCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomIntervalInputBaseEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomRawInputInverseUncurry
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedRawInputEvaluations
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalEndpointUncurry
/-!
概要：正本標的の入力側の底写像を元左右 Hom 複体上の導来二作用の積へ同定する。
方針：全区間族を二射影へ分離し、逆入力座標と各導来入力の同じ評価を照合する。
規約：全パラメーターと固定終点を保持し、元二入力を忘れない。
使われ方：正本標的と既存の入力付き四座標標的を厳密同型で結ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
lemma dgGluingLaxHomIntervalInputMap_coordinates :
    (dgGluingLaxHomRawInputIso R C D M X Y).inv ≫
      dgGluingLaxHomIntervalInputBase R C D M X Y ≫
        (dgGluingLaxHomIntervalBaseCoordinateIso R C D M X Y).hom =
      (dgGluingDerivedLeftCoefficientInput R C D M X Y) ⊗ₘ
        (dgGluingDerivedRightCoefficientInput R C D M X Y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [dgGluingLaxHomIntervalBaseCoordinateIso, Iso.trans_hom, Iso.symm_hom,
      dgGluingIntervalMappingProductIso, dgGluingIntervalProductSplit,
      Category.assoc, lift_fst, tensorHom_fst]
    apply intervalMappingUncurry_injective _ _
    simp only [← Category.assoc]
    rw [intervalMappingPost_uncurry,
      dgGluingIntervalEndpointIso_hom_uncurry, dgGluingLaxHomIntervalInputBase_raw_evaluation]
    simp only [Category.assoc, tensorHom_fst]
    rw [reassoc_of% dgGluingLaxHomRawInputIso_inv_first_uncurry R C D M X Y]
    rw [intervalMappingUncurry_precomp, dgGluingDerivedLeftCoefficientInput_raw_evaluation,
      reassoc_of% rightMappingSpacePrism_naturality (fst _ _),
      ← reassoc_of% pinchedHomUncurry_precomp]
  · simp only [dgGluingLaxHomIntervalBaseCoordinateIso, Iso.trans_hom, Iso.symm_hom,
      dgGluingIntervalMappingProductIso, dgGluingIntervalProductSplit,
      Category.assoc, lift_snd, tensorHom_snd]
    apply intervalMappingUncurry_injective _ _
    simp only [← Category.assoc]
    rw [intervalMappingPost_uncurry,
      dgGluingIntervalEndpointIso_hom_uncurry, dgGluingLaxHomIntervalInputBase_raw_evaluation]
    simp only [Category.assoc, tensorHom_snd]
    rw [reassoc_of% dgGluingLaxHomRawInputIso_inv_second_uncurry R C D M X Y]
    rw [intervalMappingUncurry_precomp, dgGluingDerivedRightCoefficientInput_raw_evaluation,
      reassoc_of% rightMappingSpacePrism_naturality (snd _ _),
      ← reassoc_of% pinchedHomUncurry_precomp]
end SerrePositivity.InfinityCategories
