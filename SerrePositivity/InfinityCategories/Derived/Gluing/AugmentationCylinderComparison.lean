module
public import SerrePositivity.InfinityCategories.Derived.Gluing.AugmentationCylinderOver
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedCylinderPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativePrismHomotopy

/-! 明示 augmentation 円柱と既存の選択円柱を、両端・元複体を固定して比較する。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] (K : Complex R)

lemma dgGluingAugmentationCylinderComparison_exists :
    ∃ H : SSet.Homotopy (dgGluingAugmentationCylinderPrism.{u, v} K)
        (dgGluingComplexPinchedCylinderPrism.{u, max u v} K),
      (((boundary 1).ι ▷ complexPinchedSpace.{u, max u v} K) ▷
          (Δ[1] : SSet.{max u v})) ≫ H.h =
        fst ((boundary 1 : SSet.{max u v}) ⊗ complexPinchedSpace.{u, max u v} K) Δ[1] ≫
          ((boundary 1).ι ▷ complexPinchedSpace.{u, max u v} K) ≫
            dgGluingComplexPinchedCylinderPrism.{u, max u v} K ∧
      H.h ≫ complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection K) =
        fst ((Δ[1] : SSet.{max u v}) ⊗ complexPinchedSpace.{u, max u v} K) Δ[1] ≫
          dgGluingComplexPinchedCylinderPrism.{u, max u v} K ≫
            complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection K) := by
  let : QuasiIso (dgGluingCochainCylinderProjection K) :=
    dgGluingCochainCylinderProjection_quasiIso K
  let : TrivialKanFibration
      (complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection K)) :=
    complexPinchedMap_trivialKanFibration _ (dgGluingCochainCylinderProjection_surjective K)
  apply dgGluingRelativePrismHomotopy_exists
    (complexPinchedMap.{u, max u v} (dgGluingCochainCylinderProjection K))
  · rw [dgGluingAugmentationCylinderPrism_zero, dgGluingComplexPinchedCylinderPrism_zero]
  · rw [dgGluingAugmentationCylinderPrism_one, dgGluingComplexPinchedCylinderPrism_one]
  · rw [dgGluingAugmentationCylinderPrism_over, dgGluingComplexPinchedCylinderPrism_over]

end SerrePositivity.InfinityCategories
