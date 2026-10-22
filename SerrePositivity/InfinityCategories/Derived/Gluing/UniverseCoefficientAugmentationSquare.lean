module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseCoefficientMappingSpan
public import SerrePositivity.InfinityCategories.Derived.Gluing.ResolvedCoefficientAugmentationSquare

/-! 同じ係数四角形を gluing の共通宇宙へ移し、実導来 Hom への同値を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (c : C) (N : RightModule R C)

lemma dgGluingUniverseCoefficientAugmentation_square :
    dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c
        (dgGluingResolvedModule R C N).val ≫
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingResolvedCoefficientHomPost R C c N)) =
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingResolvedCoefficientEvaluation R C c N)) ≫
      dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c N := by
  have hs := congrArg
    ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map)
    (dgGluingResolvedCoefficientAugmentation_space_square R C c N)
  rw [Functor.map_comp, Functor.map_comp] at hs
  dsimp only [dgGluingUniverseDerivedCoefficientHomSpanRight]
  dsimp only [dgGluingDerivedCoefficientHomSpanRight] at hs ⊢
  rw [Category.assoc, hs, ← Category.assoc,
    ← dgGluingComplexPinchedUniverseIso_naturality, Category.assoc]

def dgGluingUniverseResolvedCoefficientHomComparison :=
  dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c
      (dgGluingResolvedModule R C N).val ≫
    (dgGluingUniverseDerivedCoefficientHomIso.{u, v, w} R C c N).inv

lemma dgGluingUniverseResolvedCoefficientHomComparison_augmentation :
    dgGluingUniverseResolvedCoefficientHomComparison.{u, v, w} R C c N ≫
      dgGluingUniverseDerivedCoefficientHomSpanLeft.{u, v, w} R C c N =
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingResolvedCoefficientEvaluation R C c N)) ≫
      dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c N := by
  rw [dgGluingUniverseResolvedCoefficientHomComparison,
    dgGluingUniverseDerivedCoefficientHomSpanLeft, Category.assoc,
    Iso.inv_hom_id_assoc, dgGluingUniverseCoefficientAugmentation_square]

lemma dgGluingUniverseResolvedCoefficientHomComparison_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingUniverseResolvedCoefficientHomComparison.{u, v, w} R C c N) := by
  exact (dgGluingHomotopyEquivalence_postcomp_iso_iff _
    (dgGluingUniverseDerivedCoefficientHomIso.{u, v, w} R C c N).symm).mpr
      (dgGluingUniverseDerivedCoefficientHomSpanRight_equivalence R C c
        (dgGluingResolvedModule R C N).val)

end SerrePositivity.InfinityCategories
