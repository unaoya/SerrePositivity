module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomTriangleHomotopyFamilies

/-! 二三角形の全時間族は augmentation 固定辺と元 Hom 可変辺を時間方向にも保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingLaxHomFirstTriangleHomotopyFamily_fixed (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstTriangleHomotopyFamily R C D M X Y =
      fst _ _ ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstTriangleHomotopyFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFamilyAlongHomotopy_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation_fixed R C D M X Y,
    ← Category.assoc, whiskerLeft_fst]

lemma dgGluingLaxHomLastTriangleHomotopyFamily_fixed (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastTriangleHomotopyFamily R C D M X Y =
      fst _ _ ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastTriangleHomotopyFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFamilyAlongHomotopy_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation_fixed R C D M X Y,
    ← Category.assoc, whiskerLeft_fst]

lemma dgGluingLaxHomFirstTriangleHomotopyFamily_variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstTriangleHomotopyFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
        (fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedRightCoefficientInput R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstTriangleHomotopyFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFamilyAlongHomotopy_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation_variable R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstInputHomotopy_over R C D M X Y, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedRightCoefficientInput_raw_factor R C D M X Y]

lemma dgGluingLaxHomLastTriangleHomotopyFamily_variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastTriangleHomotopyFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
        (fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLeftCoefficientInput R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastTriangleHomotopyFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFamilyAlongHomotopy_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation_variable R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastInputHomotopy_over R C D M X Y, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLeftCoefficientInput_raw_factor R C D M X Y]

lemma dgGluingLaxHomFirstTriangleHomotopyFamily_diagonal (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstTriangleHomotopyFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstTriangleHomotopyFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFamilyAlongHomotopy_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation_diagonal R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

lemma dgGluingLaxHomLastTriangleHomotopyFamily_diagonal (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastTriangleHomotopyFamily R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastInputHomotopy R C D M X Y).h ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastTriangleHomotopyFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFamilyAlongHomotopy_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation_diagonal R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
