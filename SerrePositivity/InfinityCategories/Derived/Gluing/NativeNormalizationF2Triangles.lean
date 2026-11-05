module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeArrowComparisonPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomTriangleNaturality

/-! 元 native cube の augmentation 面の二三角形は、正本 F2 の元二三角形に全 Hom パラメータで一致。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory MonoidalClosed DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
abbrev dgGluingNativePinchedHomParameter :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
    (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y)
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativeNormalizationArrowSquare :=
  ((β_ (Δ[1] : SSet.{max (u + 1) v w}) Δ[1]).hom ▷ P) ≫ (α_ Δ[1] Δ[1] P).hom ≫
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 P)) ≫
      dgGluingNativeDerivedPreNormalizeCube R C D M X Y

lemma dgGluingNativeArrowComparisonPrism_cube :
    intervalFunctorHomPrism (dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingLaxHomArrowIntervalComparison R C D M X Y) =
      dgGluingNativeNormalizationArrowSquare R C D M X Y := by
  rw [dgGluingNativeNormalizationArrowSquare,
    dgGluingNativeDerivedPreNormalizeCube_original_face]
  exact dgGluingNativeArrowComparisonPrism R C D M X Y

def dgGluingNativeNormalizationFirstTriangle :=
  (squareTriangle 0 ▷ P) ≫ dgGluingNativeNormalizationArrowSquare R C D M X Y

def dgGluingNativeNormalizationLastTriangle :=
  (squareTriangle 1 ▷ P) ≫ dgGluingNativeNormalizationArrowSquare R C D M X Y

lemma dgGluingNativeNormalizationFirstTriangle_eq :
    dgGluingNativeNormalizationFirstTriangle R C D M X Y =
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        (dgGluingLaxHomArrowTriangles R C D M X Y).first := by
  rw [dgGluingNativeNormalizationFirstTriangle, ← dgGluingNativeArrowComparisonPrism_cube]
  exact congrArg DGGluingArrowHomTrianglePair.first
    (dgGluingArrowHomTriangles_naturality (dgGluingNativeHomModelMap R C D M X Y)
      (dgGluingLaxHomArrowIntervalComparison R C D M X Y))

lemma dgGluingNativeNormalizationLastTriangle_eq :
    dgGluingNativeNormalizationLastTriangle R C D M X Y =
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        (dgGluingLaxHomArrowTriangles R C D M X Y).second := by
  rw [dgGluingNativeNormalizationLastTriangle, ← dgGluingNativeArrowComparisonPrism_cube]
  exact congrArg DGGluingArrowHomTrianglePair.second
    (dgGluingArrowHomTriangles_naturality (dgGluingNativeHomModelMap R C D M X Y)
      (dgGluingLaxHomArrowIntervalComparison R C D M X Y))

end SerrePositivity.InfinityCategories
