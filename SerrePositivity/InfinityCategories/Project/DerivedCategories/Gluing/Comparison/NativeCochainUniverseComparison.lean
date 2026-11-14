module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ComplexCochainPrismUniverseNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeNormalizedCoefficientPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.NativeArrowComparisonPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomCoefficientAugmentationHomotopy

/-! 加群側の係数模型を元の係数宇宙へ輸送し、同じ正本 Hom 入力と明示 prism を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory SSet

open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y
local notation "L" => _root_.SerrePositivity.DifferentialGraded.Bimodule.value M X.left Y.right

lemma dgGluingNativeCochainModelInput_universe :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainModelInput R C D M X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, max (u + 1) v, max u v w,
          max (u + 1) v w} K).hom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource.{u, max u v w} K)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget.{u, max u v w} K) n).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv.{u, max (u + 1) v, max u v w}
      K n ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainModelInput R C D M X Y).app (Opposite.op ⦋n⦌) s).down) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (A := R) X Y).hom.app (Opposite.op ⦋n⦌) s.down)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseEquiv_linear]
  have hl := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap_linear.{u, max u v w, max (u + 1) v,
      max (u + 1) v w}
    (C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max (u + 1) v} K)
    (x := X) (y := Y) (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource K) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget K)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).hom s
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear.{u, max u v w}
    (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v w} K)
    (x := X) (y := Y) (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource K) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget K)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).hom s.down
  exact hl.trans hr.symm

lemma dgGluingNativeNormalizedPrism_coefficient_universe :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleNormalizedPrism R C D M X Y ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainCoefficientMap R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u, max (u + 1) v, max u v w,
          max (u + 1) v w} L).hom =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleNormalizedPrism_coefficient, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainPrism_universe_naturality.{u, max (u + 1) v, max u v w,
      max (u + 1) v w}]
  rw [← Category.assoc, ← whiskerLeft_comp, dgGluingNativeCochainModelInput_universe]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
