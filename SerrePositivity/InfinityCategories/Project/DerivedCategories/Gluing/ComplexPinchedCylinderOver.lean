module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedCochainHomotopy

/-! 主係数 path に使う実円柱ホモトピーは、元の複体上で全時刻定値である。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R]

lemma dgGluingComplexPinchedCylinderHomotopy_over (K : Complex R) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderHomotopy.{u, v} K).h ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection K) =
      fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} K) (Δ[1] : SSet.{max u v}) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderHomotopy]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopy_of_trivialFibration_post_eq_over, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderOne_projection, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
