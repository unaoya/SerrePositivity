module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexCochainPrismUniverseNaturality
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizedCoefficientPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeArrowComparisonPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientAugmentationHomotopy

/-! 加群側の係数模型を元の係数宇宙へ輸送し、同じ正本 Hom 入力と明示 prism を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory SSet
open DGNerve DGNerve.PinchedHom
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "K" => dgGluingHomComplex R C D M X Y
local notation "L" => Bimodule.value M X.left Y.right

lemma dgGluingNativeCochainModelInput_universe :
    dgGluingNativeModuleCochainModelInput R C D M X Y ≫
        (dgGluingCommonComplexPinchedUniverseIso.{u, max (u + 1) v, max u v w,
          max (u + 1) v w} K).hom = dgGluingNativeHomModelMap R C D M X Y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (linearEquiv (complexPinchedSource.{u, max u v w} K)
    (complexPinchedTarget.{u, max u v w} K) n).injective
  change toLinearSimplex (dgGluingComplexPinchedUniverseEquiv.{u, max (u + 1) v, max u v w}
      K n ((dgGluingNativeModuleCochainModelInput R C D M X Y).app (Opposite.op ⦋n⦌) s).down) =
    toLinearSimplex ((pinchedComplexModelIso (A := R) X Y).hom.app (Opposite.op ⦋n⦌) s.down)
  rw [dgGluingComplexPinchedUniverseEquiv_linear]
  have hl := dgGluingUniverseHomChainMap_linear.{u, max u v w, max (u + 1) v,
      max (u + 1) v w}
    (C := DGGluingObject R C D M) (D := DGComplexPinchedModel.{u, max (u + 1) v} K)
    (x := X) (y := Y) (x' := complexPinchedSource K) (y' := complexPinchedTarget K)
    (complexUnitHomIso K).hom s
  have hr := pinchedHomChainMapSimplex_linear.{u, max u v w}
    (D := DGGluingObject R C D M) (E := DGComplexPinchedModel.{u, max u v w} K)
    (x := X) (y := Y) (x' := complexPinchedSource K) (y' := complexPinchedTarget K)
    (complexUnitHomIso K).hom s.down
  exact hl.trans hr.symm

lemma dgGluingNativeNormalizedPrism_coefficient_universe :
    dgGluingNativeModuleNormalizedPrism R C D M X Y ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (dgGluingNativeModuleCochainCoefficientMap R C D M X Y) ≫
        (dgGluingCommonComplexPinchedUniverseIso.{u, max (u + 1) v, max u v w,
          max (u + 1) v w} L).hom =
      (Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
          (dgGluingHomCoefficientAugmentationPrism R C D M X Y) := by
  rw [← Category.assoc, dgGluingNativeModuleNormalizedPrism_coefficient, Category.assoc,
    dgGluingComplexCochainPrism_universe_naturality.{u, max (u + 1) v, max u v w,
      max (u + 1) v w}]
  rw [← Category.assoc, ← whiskerLeft_comp, dgGluingNativeCochainModelInput_universe]
  rfl

end SerrePositivity.InfinityCategories
