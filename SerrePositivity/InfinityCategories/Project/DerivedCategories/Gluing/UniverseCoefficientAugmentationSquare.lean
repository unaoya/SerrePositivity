module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseCoefficientMappingSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ResolvedCoefficientAugmentationSquare

/-! 同じ係数四角形を gluing の共通宇宙へ移し、実導来 Hom への同値を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (c : C) (N : _root_.SerrePositivity.DifferentialGraded.RightModule R C)

lemma dgGluingUniverseCoefficientAugmentation_square :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C N).val ≫
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientHomPost R C c N)) =
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c N := by
  have hs := congrArg
    ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientAugmentation_space_square R C c N)
  rw [Functor.map_comp, Functor.map_comp] at hs
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficientHomSpanRight]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedCoefficientHomSpanRight] at hs ⊢
  rw [Category.assoc, hs, ← Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUniverseIso_naturality, Category.assoc]

def dgGluingUniverseResolvedCoefficientHomComparison :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C N).val ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficientHomIso.{u, v, w} R C c N).inv

lemma dgGluingUniverseResolvedCoefficientHomComparison_augmentation :
    dgGluingUniverseResolvedCoefficientHomComparison.{u, v, w} R C c N ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficientHomSpanLeft.{u, v, w} R C c N =
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedCoefficientEvaluation R C c N)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c N := by
  rw [dgGluingUniverseResolvedCoefficientHomComparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficientHomSpanLeft, Category.assoc,
    Iso.inv_hom_id_assoc, dgGluingUniverseCoefficientAugmentation_square]

lemma dgGluingUniverseResolvedCoefficientHomComparison_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (dgGluingUniverseResolvedCoefficientHomComparison.{u, v, w} R C c N) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyEquivalence_postcomp_iso_iff _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficientHomIso.{u, v, w} R C c N).symm).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficientHomSpanRight_equivalence R C c
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C N).val)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
