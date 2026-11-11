module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeBlocks
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RepresentableEvaluation

/-! 右 Hom cone 係数は、第三成分が零の厳密な双加群作用の正方形から得られる。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "r" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcompositionComponents R C D M X Y Z f
local notation "μ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y
local notation "ν" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Z
local notation "h" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeThird R C D M X Y Z f
local notation "a" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Z

/-- 右成分の実後合成と双加群作用は厳密に可換する。 -/
lemma dgGluingHomConeRightAction_square : a ≫ g = r ≫ b := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareRestriction_boundary r p g biprod.inr biprod.inr
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRight_square R C D M X Y Z f) μ ν h
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeThird_boundary R C D M X Y Z f)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference_inr, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference_inr, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeThird_inr] at he
  simp only [δ_zero, zero_add] at he
  have hz : Cochain.ofHom (a ≫ g - r ≫ b) = Cochain.ofHom 0 := by
    simpa only [Cochain.ofHom_zero] using he
  exact sub_eq_zero.mp (Cochain.ofHom_injective hz)

/-- 右係数は、同じ厳密正方形の標準 cone 写像そのものである。 -/
lemma dgGluingHomConeRightCoefficient_map :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightCoefficient R C D M X Y Z f =
      mappingCone.map r g a b (dgGluingHomConeRightAction_square R C D M X Y Z f).symm := by
  have hc := dgGluingHomConeRightAction_square R C D M X Y Z f
  have h0 : δ (-1) 0 (0 : Cochain (homObject R D X.right Y.right)
      (M.value X.left Z.right) (-1)) + Cochain.ofHom (a ≫ g - r ≫ b) = 0 := by
    rw [hc, sub_self]
    simp only [δ_zero, Cochain.ofHom_zero, add_zero]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMap_zero r g a b hc.symm h0
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightCoefficient, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference_inr,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeThird_inr] using he

variable [Small.{u} D] in
/-- 右 Hom cone を D の同じ Yoneda cone 加群からの全 Hom と同定する。 -/
def dgGluingHomConeRightModuleIso : mappingCone r ≅
    moduleHom R D (representable R X.right)
      (ForgetEnrichment.to (Complex R) (moduleCone R D
        ((dgYoneda R D).onClosed.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map f)))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso R D X.right Y.right Z.right ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
