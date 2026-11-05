module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationF2Triangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCanonicalIntervalFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationSharedFace

/-! # 実正規化 cube の三角形族

概要：実前正規化 cube を二つの三角形の全時間族として保持する。
方針：元の正方形と同じ二三角形を取り、残る区間を Hom 入力の後に置く。
規約：元面の三角形は正本 F2 の実二三角形そのものであり、全入力を保つ。
使われ方：cube の実変形を入力付き合成 fiber へ持ち上げる前の三角形表示。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial

/-- 概要：cube の二方向を三角形へ制限し、残りを全時間として保持する。
方針：元の矢印 Hom 正方形と同じ座標交換を使う。
規約：時間を Hom パラメーターの後に置く。使われ方：実正規化三角形の族。 -/
def dgGluingCubeTriangleFamily {P Z : SSet.{u}}
    (V : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ P)) ⟶ Z) (i : Fin 2) :
    (Δ[2] : SSet.{u}) ⊗ (P ⊗ Δ[1]) ⟶ Z :=
  (Δ[2] ◁ (β_ P (Δ[1] : SSet.{u})).hom) ≫
    (squareTriangle i ▷ (Δ[1] ⊗ P)) ≫
      ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ▷ (Δ[1] ⊗ P)) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[1] (Δ[1] ⊗ P)).hom ≫ V

lemma dgGluingCubeTriangleFamily_endpoint {P Z : SSet.{u}}
    (V : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ P)) ⟶ Z) (i j : Fin 2) :
    (Δ[2] ◁ (if j = 0 then (ι₀ : P ⟶ P ⊗ Δ[1]) else ι₁)) ≫
        dgGluingCubeTriangleFamily V i =
      (squareTriangle i ▷ P) ≫ ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ▷ P) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[1] P).hom ≫
          (Δ[1] ◁ (Δ[1] ◁ prismEndpoint j P)) ≫ V := by
  fin_cases j <;> apply SSet.hom_ext <;> intro d <;>
    apply ConcreteCategory.hom_ext <;> intro a <;> rfl

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

/-- 概要：実前正規化 cube の三角形を全時間で評価する。
方針：元の二三角形と同じ制限を使う。
規約：正本の実導来関手の後合成を保持する。使われ方：入力固定変形の構成。 -/
def dgGluingNativePreNormalizeTriangleFamily (i : Fin 2) :=
  dgGluingCubeTriangleFamily (dgGluingNativeDerivedPreNormalizeCube R C D M X Y) i

lemma dgGluingNativePreNormalizeTriangleFamily_first_one :
    (Δ[2] ◁ ι₁) ≫ dgGluingNativePreNormalizeTriangleFamily R C D M X Y 0 =
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        (dgGluingLaxHomArrowTriangles R C D M X Y).first := by
  have he := dgGluingCubeTriangleFamily_endpoint
    (dgGluingNativeDerivedPreNormalizeCube R C D M X Y) 0 1
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at he
  exact he.trans (dgGluingNativeNormalizationFirstTriangle_eq R C D M X Y)

lemma dgGluingNativePreNormalizeTriangleFamily_last_one :
    (Δ[2] ◁ ι₁) ≫ dgGluingNativePreNormalizeTriangleFamily R C D M X Y 1 =
      (Δ[2] ◁ dgGluingNativeHomModelMap R C D M X Y) ≫
        (dgGluingLaxHomArrowTriangles R C D M X Y).second := by
  have he := dgGluingCubeTriangleFamily_endpoint
    (dgGluingNativeDerivedPreNormalizeCube R C D M X Y) 1 1
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at he
  exact he.trans (dgGluingNativeNormalizationLastTriangle_eq R C D M X Y)

local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

/-- 概要：実後正規化 cube の三角形を全時間で保持する。
方針：前 cube と同じ座標交換を使う。
規約：二つの cube の共有面を変えない。使われ方：正規化係数面への三角形比較。 -/
def dgGluingNativePostNormalizeTriangleFamily (i : Fin 2) :=
  dgGluingCubeTriangleFamily (dgGluingNativeDerivedPostNormalizeCube R C D M X Y) i

lemma dgGluingNativePreNormalizeTriangleFamily_shared (i : Fin 2) :
    (Δ[2] ◁ ι₀) ≫ dgGluingNativePreNormalizeTriangleFamily R C D M X Y i =
      (squareTriangle i ▷ P) ≫ ((β_ (Δ[1] : SSet.{max (u + 1) v w}) Δ[1]).hom ▷ P) ≫
        (α_ (Δ[1] : SSet.{max (u + 1) v w}) Δ[1] P).hom ≫
          (Δ[1] ◁ prismEndpoint 0 _) ≫
            dgGluingNativeDerivedPostNormalizeCube R C D M X Y := by
  have he := dgGluingCubeTriangleFamily_endpoint
    (dgGluingNativeDerivedPreNormalizeCube R C D M X Y) i 0
  rw [dgGluingNativeDerivedNormalizationCube_shared_face] at he
  exact he

lemma dgGluingNativePostNormalizeTriangleFamily_canonical (i : Fin 2) :
    (Δ[2] ◁ ι₀) ≫ dgGluingNativePostNormalizeTriangleFamily R C D M X Y i =
      (squareTriangle i ▷ P) ≫ ((β_ (Δ[1] : SSet.{max (u + 1) v w}) Δ[1]).hom ▷ P) ≫
        (α_ (Δ[1] : SSet.{max (u + 1) v w}) Δ[1] P).hom ≫
          (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeHomModelMap R C D M X Y)) ≫
            dgGluingPrismIntervalSquare
              (dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
                (dgGluingHomCoefficientAugmentationPrism R C D M X Y))
              (dgGluingCanonicalCoefficientIntervalEvaluation R C D M X Y) := by
  have he := dgGluingCubeTriangleFamily_endpoint
    (dgGluingNativeDerivedPostNormalizeCube R C D M X Y) i 0
  rw [dgGluingNativeDerivedPostNormalizeCube_canonical_interval_face] at he
  exact he

end SerrePositivity.InfinityCategories
