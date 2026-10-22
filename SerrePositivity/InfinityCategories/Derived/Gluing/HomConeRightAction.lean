module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeBlocks
public import SerrePositivity.InfinityCategories.Derived.Gluing.RepresentableEvaluation

/-! 右 Hom cone 係数は、第三成分が零の厳密な双加群作用の正方形から得られる。 -/
@[expose] public section
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "r" => dgGluingHomConeRightArrow R C D M X Y Z f
local notation "g" => dgGluingHomConeAction R C D M X Y Z f
local notation "p" => dgGluingPostcompositionComponents R C D M X Y Z f
local notation "μ" => dgGluingDifference R C D M X Y
local notation "ν" => dgGluingDifference R C D M X Z
local notation "h" => dgGluingHomConeThird R C D M X Y Z f
local notation "a" => dgGluingRightAction R C D M X Y
local notation "b" => dgGluingRightAction R C D M X Z

/-- 右成分の実後合成と双加群作用は厳密に可換する。 -/
lemma dgGluingHomConeRightAction_square : a ≫ g = r ≫ b := by
  have he := dgGluingConeSquareRestriction_boundary r p g biprod.inr biprod.inr
    (dgGluingHomConeRight_square R C D M X Y Z f) μ ν h
    (dgGluingHomConeThird_boundary R C D M X Y Z f)
  rw [dgGluingDifference_inr, dgGluingDifference_inr, dgGluingHomConeThird_inr] at he
  simp only [δ_zero, zero_add] at he
  have hz : Cochain.ofHom (a ≫ g - r ≫ b) = Cochain.ofHom 0 := by
    simpa only [Cochain.ofHom_zero] using he
  exact sub_eq_zero.mp (Cochain.ofHom_injective hz)

/-- 右係数は、同じ厳密正方形の標準 cone 写像そのものである。 -/
lemma dgGluingHomConeRightCoefficient_map :
    dgGluingHomConeRightCoefficient R C D M X Y Z f =
      mappingCone.map r g a b (dgGluingHomConeRightAction_square R C D M X Y Z f).symm := by
  have hc := dgGluingHomConeRightAction_square R C D M X Y Z f
  have h0 : δ (-1) 0 (0 : Cochain (homObject R D X.right Y.right)
      (M.value X.left Z.right) (-1)) + Cochain.ofHom (a ≫ g - r ≫ b) = 0 := by
    rw [hc, sub_self]
    simp only [δ_zero, Cochain.ofHom_zero, add_zero]
  have he := dgGluingConeSquareMap_zero r g a b hc.symm h0
  simpa only [dgGluingHomConeRightCoefficient, dgGluingDifference_inr,
    dgGluingHomConeThird_inr] using he

variable [Small.{u} D] in
/-- 右 Hom cone を D の同じ Yoneda cone 加群からの全 Hom と同定する。 -/
def dgGluingHomConeRightModuleIso : mappingCone r ≅
    moduleHom R D (representable R X.right)
      (ForgetEnrichment.to (Complex R) (moduleCone R D
        ((dgYoneda R D).onClosed.map ((dgGluingRight R C D M).onClosed.map f)))) :=
  dgGluingYonedaConeIso R D X.right Y.right Z.right ((dgGluingRight R C D M).onClosed.map f)

end SerrePositivity.InfinityCategories
