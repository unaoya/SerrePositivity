module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeArrowComparisonPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomArrowTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ArrowHomTriangleNaturality

/-! 元 native cube の augmentation 面の二三角形は、正本 F2 の元二三角形に全 Hom パラメータで一致。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
abbrev dgGluingNativePinchedHomParameter :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X Y)
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativeNormalizationArrowSquare :=
  ((β_ (Δ[1] : SSet.{max (u + 1) v w}) Δ[1]).hom ▷ P) ≫ (α_ Δ[1] Δ[1] P).hom ≫
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 P)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube R C D M X Y

lemma dgGluingNativeArrowComparisonPrism_cube :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y) =
      dgGluingNativeNormalizationArrowSquare R C D M X Y := by
  rw [dgGluingNativeNormalizationArrowSquare,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeDerivedPreNormalizeCube_original_face]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeArrowComparisonPrism R C D M X Y

def dgGluingNativeNormalizationFirstTriangle :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ P) ≫ dgGluingNativeNormalizationArrowSquare R C D M X Y

def dgGluingNativeNormalizationLastTriangle :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ P) ≫ dgGluingNativeNormalizationArrowSquare R C D M X Y

lemma dgGluingNativeNormalizationFirstTriangle_eq :
    dgGluingNativeNormalizationFirstTriangle R C D M X Y =
      (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowTriangles R C D M X Y).first := by
  rw [dgGluingNativeNormalizationFirstTriangle, ← dgGluingNativeArrowComparisonPrism_cube]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair.first
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTriangles_naturality (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y))

lemma dgGluingNativeNormalizationLastTriangle_eq :
    dgGluingNativeNormalizationLastTriangle R C D M X Y =
      (Δ[2] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowTriangles R C D M X Y).second := by
  rw [dgGluingNativeNormalizationLastTriangle, ← dgGluingNativeArrowComparisonPrism_cube]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingArrowHomTrianglePair.second
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTriangles_naturality (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowIntervalComparison R C D M X Y))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
