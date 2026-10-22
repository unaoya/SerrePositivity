module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedCochainHomotopy

/-! 主係数 path に使う実円柱ホモトピーは、元の複体上で全時刻定値である。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R]

lemma dgGluingComplexPinchedCylinderHomotopy_over (K : Complex R) :
    (dgGluingComplexPinchedCylinderHomotopy.{u, v} K).h ≫
        complexPinchedMap.{u, v} (dgGluingCochainCylinderProjection K) =
      fst (complexPinchedSpace.{u, v} K) (Δ[1] : SSet.{max u v}) := by
  dsimp only [dgGluingComplexPinchedCylinderHomotopy]
  rw [dgGluingHomotopy_of_trivialFibration_post_eq_over, ← complexPinchedMap_comp,
    dgGluingCochainCylinderOne_projection, complexPinchedMap_id, Category.comp_id]

end SerrePositivity.InfinityCategories
