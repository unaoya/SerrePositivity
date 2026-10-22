module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedCylinderOver

/-! 主経路の円柱ホモトピーを区間第一因子の prism として保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] (K : Complex R)

def dgGluingComplexPinchedCylinderPrism :
    (Δ[1] : SSet.{max u v}) ⊗ complexPinchedSpace.{u, v} K ⟶
      complexPinchedSpace.{u, v} (dgGluingCochainCylinder K) :=
  (β_ (Δ[1] : SSet.{max u v}) (complexPinchedSpace.{u, v} K)).hom ≫
    (dgGluingComplexPinchedCylinderHomotopy K).h

lemma dgGluingComplexPinchedCylinderPrism_zero :
    prismEndpoint 0 _ ≫ dgGluingComplexPinchedCylinderPrism.{u, v} K =
      complexPinchedMap.{u, v} (dgGluingCochainCylinderZero K) := by
  have hi : prismEndpoint 0 _ ≫
      (β_ (Δ[1] : SSet.{max u v}) (complexPinchedSpace.{u, v} K)).hom = SSet.ι₀ := rfl
  rw [dgGluingComplexPinchedCylinderPrism, ← Category.assoc, hi]
  exact (dgGluingComplexPinchedCylinderHomotopy K).h₀

lemma dgGluingComplexPinchedCylinderPrism_one :
    prismEndpoint 1 _ ≫ dgGluingComplexPinchedCylinderPrism.{u, v} K =
      complexPinchedMap.{u, v} (dgGluingCochainCylinderOne K) := by
  have hi : prismEndpoint 1 _ ≫
      (β_ (Δ[1] : SSet.{max u v}) (complexPinchedSpace.{u, v} K)).hom = SSet.ι₁ := rfl
  rw [dgGluingComplexPinchedCylinderPrism, ← Category.assoc, hi]
  exact (dgGluingComplexPinchedCylinderHomotopy K).h₁

lemma dgGluingComplexPinchedCylinderPrism_over :
    dgGluingComplexPinchedCylinderPrism.{u, v} K ≫
        complexPinchedMap.{u, v} (dgGluingCochainCylinderProjection K) =
      snd (Δ[1] : SSet.{max u v}) (complexPinchedSpace.{u, v} K) := by
  rw [dgGluingComplexPinchedCylinderPrism, Category.assoc,
    dgGluingComplexPinchedCylinderHomotopy_over K]
  rfl

end SerrePositivity.InfinityCategories
