module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientInputs

/-! 同じ二三角形の可変辺は、主比較の端点表示に正規化した元の二入力を表す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedLeftCoefficientTriangle_variable (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫ dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y =
      intervalMappingUncurry (dgGluingHomDerivedLeftCoefficientInput R C D M X Y) := by
  rw [dgGluingHomDerivedLeftCoefficientTriangle, ← Category.assoc, ← whisker_exchange,
    Category.assoc, dgGluingUniverseDerivedLeftCoefficientTriangleFamily_two R C D M X Y,
    ← intervalMappingUncurry_precomp]
  exact (dgGluingHomDerivedLeftCoefficientInput_uncurry R C D M X Y).symm

lemma dgGluingHomDerivedRightCoefficientTriangle_variable (X Y : DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫ dgGluingHomDerivedRightCoefficientTriangle R C D M X Y =
      intervalMappingUncurry (dgGluingHomDerivedRightCoefficientInput R C D M X Y) := by
  rw [dgGluingHomDerivedRightCoefficientTriangle, ← Category.assoc, ← whisker_exchange,
    Category.assoc, dgGluingUniverseDerivedRightCoefficientTriangleFamily_zero R C D M X Y,
    ← intervalMappingUncurry_precomp]
  exact (dgGluingHomDerivedRightCoefficientInput_uncurry R C D M X Y).symm

end SerrePositivity.InfinityCategories
