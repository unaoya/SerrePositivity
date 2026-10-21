module
public import SerrePositivity.KST.SConstruction.SerreCubeFaceNormalRightExtension
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorFaces

/-! # 元の全 tensor 生成元の右側自由座標付き標準面
概要：元の全端点・辺 tensor 生成元の標準面に、元の右側自由座標の恒等を付ける。
方針：元の標準面の point・keep と、元の右側延長の再帰を適用する。
規約：元の全生成元と座標順を保持。使われ方：HA 語の実鎖射との全生成元帰納。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全 tensor 生成元の標準面に右側自由座標を付けた、同じ元の実射。 -/
def serreCubeGeneratorRightFace (n : ℕ) (i : SerreCubeGeneratorIndex n) (t : ℕ) :
    serreCubeComonoid A (serreCubeGeneratorFreeDimension n i + t) ⟶
      serreCubeComonoid A (n + t) :=
  serreCubeFaceNormalRightExtension A (serreCubeGeneratorFaceNormal n i) t

/-- 右側が零次元なら、元の全 tensor 生成元の同じ標準面を回収する。 -/
lemma serreCubeGeneratorRightFace_zero (n : ℕ) (i : SerreCubeGeneratorIndex n) :
    serreCubeGeneratorRightFace A n i 0 =
      serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i) := rfl

/-- 元の左生成元が零次元なら、右側自由座標を保つ同じ恒等射になる。 -/
lemma serreCubeGeneratorRightFace_zero_left (i : SerreCubeGeneratorIndex 0) (t : ℕ) :
    serreCubeGeneratorRightFace A 0 i t = 𝟙 (serreCubeComonoid A (0 + t)) := by
  exact serreCubeRightExtension_id A 0 t

/-- 元の零端点の追加は、元の同じ右側自由座標数の標準零面との合成。 -/
lemma serreCubeGeneratorRightFace_point_zero (n : ℕ) (i : SerreCubeGeneratorIndex n) (t : ℕ) :
    serreCubeGeneratorRightFace A (n + 1) (i, 0) t =
      serreCubeGeneratorRightFace A n i t ≫ serreCubeRightFace A false n t :=
  serreCubeFaceNormalRightExtension_point A (serreCubeGeneratorFaceNormal n i) false t

/-- 元の一端点の追加は、元の同じ右側自由座標数の標準一面との合成。 -/
lemma serreCubeGeneratorRightFace_point_one (n : ℕ) (i : SerreCubeGeneratorIndex n) (t : ℕ) :
    serreCubeGeneratorRightFace A (n + 1) (i, 1) t =
      serreCubeGeneratorRightFace A n i t ≫ serreCubeRightFace A true n t :=
  serreCubeFaceNormalRightExtension_point A (serreCubeGeneratorFaceNormal n i) true t

/-- 元の辺の追加は、元の右側自由座標を一つ増やす表示に異種等号で一致する。 -/
lemma serreCubeGeneratorRightFace_edge (n : ℕ) (i : SerreCubeGeneratorIndex n) (t : ℕ) :
    HEq (serreCubeGeneratorRightFace A (n + 1) (i, 2) t)
      (serreCubeGeneratorRightFace A n i (t + 1)) :=
  serreCubeFaceNormalRightExtension_keep A (serreCubeGeneratorFaceNormal n i) t

/-- 元の右側自由座標付き標準面の実鎖射は、元の Serre tensor 比較の前後合成そのもの。 -/
lemma serreCubeGeneratorRightFace_tensor_chain (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (t : ℕ) :
    (serreCubeGeneratorRightFace A n i t).hom =
      (serreCubeTensorIso A (serreCubeGeneratorFreeDimension n i) t).hom.hom ≫
        ((serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom ⊗ₘ
          𝟙 (serreCubeComplex A t)) ≫ (serreCubeTensorIso A n t).inv.hom :=
  serreCubeRightExtension_tensor_chain A
    (serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)) t

end SerrePositivity.KST.SConstruction
