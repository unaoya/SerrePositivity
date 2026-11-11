module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomDerivedCoefficientInputs

/-! 同じ二三角形の可変辺は、主比較の端点表示に正規化した元の二入力を表す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedLeftCoefficientTriangle_variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLeftCoefficientInput R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLeftCoefficientTriangle, ← Category.assoc, ← whisker_exchange,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedLeftCoefficientTriangleFamily_two R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLeftCoefficientInput_uncurry R C D M X Y).symm

lemma dgGluingHomDerivedRightCoefficientTriangle_variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedRightCoefficientTriangle R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedRightCoefficientInput R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedRightCoefficientTriangle, ← Category.assoc, ← whisker_exchange,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedRightCoefficientTriangleFamily_zero R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedRightCoefficientInput_uncurry R C D M X Y).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
