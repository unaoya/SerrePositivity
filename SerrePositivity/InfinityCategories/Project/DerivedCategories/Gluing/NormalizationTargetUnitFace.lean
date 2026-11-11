module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationSourceTetrahedron
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationStandardUnitFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionSecondUnitTriangle
/-!
概要：正規化 augmentation 四面体の終側射影の第一面を厳密な単位退化へ同定する。
方針：同じ後正規化三角形の射影自然性へ coherent 第二単位則を代入する。
規約：Small 仮定なしで同じ四面体と全 Hom 入力を保持する。
使われ方：主経路の右単位閉路を同じ全正方形の退化として消去する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) {K : SSet.{max u v}}
  (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)

lemma dgGluingPostAugmentationTriangle_target_unit_face :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)) =
    (stdSimplex.σ (1 : Fin 2) ▷ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeProjectionInput_naturality R E X Y f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R E E (DGFunctor.id E))
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizePrism R E X Y f) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R E E (DGFunctor.id E)) = _ at hn
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut_source] at hn
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizePrism R E X Y f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R E E (DGFunctor.id E)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle, ← Category.assoc,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality]
    simp only [Category.assoc]
    erw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism_one R E E (DGFunctor.id E))]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaTargetLift_down]
  rw [hp, hn, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_two]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily_second_unit R E _

lemma dgGluingNormalizationTargetTetrahedron_unit_face :
    (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[3] ⊗ K) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)) =
    (stdSimplex.σ (1 : Fin 2) ▷ K) ≫ (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[3] ⊗ K) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)) := by
  have hp : (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[3] ⊗ K) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron R E X Y f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle R E X Y f ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max u v, max u v} R E)) := by
    rw [← reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
      reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationAugmentationTetrahedron_one R E X Y f]
  rw [hp]
  exact dgGluingPostAugmentationTriangle_target_unit_face R E X Y f
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
