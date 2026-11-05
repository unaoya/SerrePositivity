module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitCollarDiagonalTriangle
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitCompositionInputPaths
/-! # 四面体の補正対角三角形と実入力対角道

概要：対角三角形の二面を、元入力 fiber 内の実補正道の対角評価へ厳密に同定する。
方針：同じ三角形評価の対角と区間 uncurry の自然性を使う。
規約：全時間と元 Hom 入力を保持する。
使われ方：四面体の高次貼り合わせを写像空間内の合成三角形へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

lemma dgGluingNativePreCollarInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
        dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingNativePreCollarInputPath R C D M X Y ≫
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [← dgGluingNativePreCollarInputPath_evaluation R C D M X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingDerivedFirstInputTriangleEvaluation_diagonal R C D M X Y,
    ← intervalMappingUncurry_precomp]

lemma dgGluingNativeUnitCollarDiagonalTriangleFamily_two_interval :
    (Δ[1] ◁ (stdSimplex.δ (2 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCollarDiagonalTriangleFamily R C D M X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom) ≫
        intervalMappingUncurry (dgGluingNativePreCollarInputPath R C D M X Y ≫
          dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingNativeUnitCollarDiagonalTriangleFamily_two R C D M X Y,
    dgGluingNativePreCollarInputPath_diagonal_evaluation R C D M X Y]

lemma dgGluingNativeExitCollarInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
        dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingNativeExitCollarInputPath R C D M X Y ≫
        dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [← dgGluingNativeExitCollarInputPath_evaluation R C D M X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingDerivedLastInputTriangleEvaluation_diagonal R C D M X Y,
    ← intervalMappingUncurry_precomp]

lemma dgGluingNativeUnitCollarDiagonalTriangleFamily_zero_interval :
    (Δ[1] ◁ (stdSimplex.δ (0 : Fin 3) ▷ P)) ≫
        dgGluingNativeUnitCollarDiagonalTriangleFamily R C D M X Y =
      (Δ[1] ◁ (β_ (Δ[1] : SSet.{max (u + 1) v w}) P).hom) ≫
        intervalMappingUncurry (dgGluingNativeExitCollarInputPath R C D M X Y ≫
          dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingNativeUnitCollarDiagonalTriangleFamily_zero R C D M X Y,
    dgGluingNativeExitCollarInputPath_diagonal_evaluation R C D M X Y]
end SerrePositivity.InfinityCategories
