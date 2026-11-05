module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitCompositionInputPaths
/-! # 単位補正対角と実入力対角道

概要：二つの単位補正の対角を、元入力 fiber 内の実補正道の対角評価へ厳密に同定する。
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


lemma dgGluingNativePreCapInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
        dgGluingNativePreUnitCapTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingNativePreCapInputPath R C D M X Y ≫
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [← dgGluingNativePreCapInputPath_evaluation R C D M X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingDerivedFirstInputTriangleEvaluation_diagonal R C D M X Y,
    ← intervalMappingUncurry_precomp]

lemma dgGluingNativeExitCapInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
        dgGluingNativeExitUnitCapTriangleFamily R C D M X Y =
      intervalMappingUncurry (dgGluingNativeExitCapInputPath R C D M X Y ≫
        dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [← dgGluingNativeExitCapInputPath_evaluation R C D M X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingDerivedLastInputTriangleEvaluation_diagonal R C D M X Y,
    ← intervalMappingUncurry_precomp]
end SerrePositivity.InfinityCategories
