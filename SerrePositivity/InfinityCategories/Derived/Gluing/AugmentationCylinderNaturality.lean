module
public import SerrePositivity.InfinityCategories.Derived.Gluing.AugmentationCylinderOver
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedCylinderNaturality
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainCylinderMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativePrismHomotopy

/-! 明示 augmentation 円柱と鎖写像上の選択円柱を、二端・全基底固定の全二次元族で比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {K L : Complex R} (a : K ⟶ L)

def dgGluingAugmentationCylinderMapPrism :=
  dgGluingAugmentationCylinderPrism.{u, v} K ≫
    complexPinchedMap.{u, max u v} (dgGluingCochainCylinderMap a)

lemma dgGluingAugmentationCylinderPrisms_zero :
    prismEndpoint 0 _ ≫ dgGluingAugmentationCylinderMapPrism.{u, v} a =
      prismEndpoint 0 _ ≫ dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a := by
  rw [dgGluingAugmentationCylinderMapPrism, ← Category.assoc,
    dgGluingAugmentationCylinderPrism_zero, ← complexPinchedMap_comp,
    dgGluingCochainCylinderMap_zero, complexPinchedMap_comp]
  rw [dgGluingComplexPinchedCylinderPrecompPrism, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc, dgGluingComplexPinchedCylinderPrism_zero]

lemma dgGluingAugmentationCylinderPrisms_one :
    prismEndpoint 1 _ ≫ dgGluingAugmentationCylinderMapPrism.{u, v} a =
      prismEndpoint 1 _ ≫ dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a := by
  rw [dgGluingAugmentationCylinderMapPrism, ← Category.assoc,
    dgGluingAugmentationCylinderPrism_one, ← complexPinchedMap_comp,
    dgGluingCochainCylinderMap_one, complexPinchedMap_comp]
  rw [dgGluingComplexPinchedCylinderPrecompPrism, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc, dgGluingComplexPinchedCylinderPrism_one]

lemma dgGluingAugmentationCylinderPrisms_over :
    dgGluingAugmentationCylinderMapPrism.{u, v} a ≫
        complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection L) =
      dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a ≫
        complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection L) := by
  rw [dgGluingAugmentationCylinderMapPrism, Category.assoc, ← complexPinchedMap_comp,
    dgGluingCochainCylinderMap_projection, complexPinchedMap_comp, ← Category.assoc,
    dgGluingAugmentationCylinderPrism_over]
  rw [dgGluingComplexPinchedCylinderPrecompPrism, Category.assoc,
    dgGluingComplexPinchedCylinderPrism_over, whiskerLeft_snd]

lemma dgGluingAugmentationCylinderNaturality_exists :
    ∃ H : SSet.Homotopy (dgGluingAugmentationCylinderMapPrism.{u, v} a)
        (dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a),
      (((SSet.boundary 1).ι ▷ complexPinchedSpace.{u, max u v} K) ▷
          (Δ[1] : SSet.{max u v})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max u v}) ⊗ complexPinchedSpace.{u, max u v} K)
          (Δ[1] : SSet.{max u v}) ≫
          ((SSet.boundary 1).ι ▷ complexPinchedSpace.{u, max u v} K) ≫
          dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a ∧
      H.h ≫ complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection L) =
        fst ((Δ[1] : SSet.{max u v}) ⊗ complexPinchedSpace.{u, max u v} K)
          (Δ[1] : SSet.{max u v}) ≫ dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a ≫
          complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection L) := by
  let : QuasiIso (dgGluingCochainCylinderProjection L) :=
    dgGluingCochainCylinderProjection_quasiIso L
  let : TrivialKanFibration
      (complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection L)) :=
    complexPinchedMap_trivialKanFibration _ (dgGluingCochainCylinderProjection_surjective L)
  exact dgGluingRelativePrismHomotopy_exists
    (complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection L)) _ _
    (dgGluingAugmentationCylinderPrisms_zero a)
    (dgGluingAugmentationCylinderPrisms_one a)
    (dgGluingAugmentationCylinderPrisms_over a)

end SerrePositivity.InfinityCategories
