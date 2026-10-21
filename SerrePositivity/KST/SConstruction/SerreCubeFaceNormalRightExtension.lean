module
public import SerrePositivity.KST.SConstruction.SerreCubeRightExtensionTensor
public import SerrePositivity.KST.SConstruction.SerreCubeRightExtensionTransport
public import SerrePositivity.KST.SConstruction.SerreCubeRightExtensionFace
public import SerrePositivity.KST.SConstruction.SerreCubeFaceNormal

/-! # 元の標準面表示の右側自由座標による延長
概要：元の端点・保持による標準面の右に、元の自由座標の恒等を付ける。
方針：元の右側延長の合成則と零座標面の移動、辺保持の結合替えを使う。
規約：元の余モノイド射と座標順を保持。使われ方：全生成元語との実鎖射の帰納。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の標準面表示の右側に自由座標の恒等を付けた、同じ元の余モノイド射。 -/
def serreCubeFaceNormalRightExtension {n m : ℕ} (d : CubeFaceNormal n m) (t : ℕ) :
    serreCubeComonoid A (n + t) ⟶ serreCubeComonoid A (m + t) :=
  serreCubeRightExtension A (serreCubeFaceNormal A d) t

/-- 元の右側自由座標が零個なら、元の同じ標準面を厳密に回収する。 -/
lemma serreCubeFaceNormalRightExtension_zero {n m : ℕ} (d : CubeFaceNormal n m) :
    serreCubeFaceNormalRightExtension A d 0 = serreCubeFaceNormal A d := rfl

/-- 元の全座標保持の標準面は、右側自由座標を付けても元の恒等射。 -/
lemma serreCubeFaceNormalRightExtension_id (n t : ℕ) :
    serreCubeFaceNormalRightExtension A (cubeFaceNormalId n) t =
      𝟙 (serreCubeComonoid A (n + t)) := by
  unfold serreCubeFaceNormalRightExtension
  rw [serreCubeFaceNormal_id, serreCubeRightExtension_id]

/-- 元の標準面への端点追加は、右側自由座標数 t と同じ座標 t の元の標準面。 -/
lemma serreCubeFaceNormalRightExtension_point {n m : ℕ} (d : CubeFaceNormal n m)
    (b : Bool) (t : ℕ) :
    serreCubeFaceNormalRightExtension A (.point b d) t =
      serreCubeFaceNormalRightExtension A d t ≫ serreCubeRightFace A b m t := by
  change serreCubeRightExtension A (serreCubeFaceNormal A d ≫ serreCubeFace A b m 0) t = _
  rw [serreCubeRightExtension_comp, serreCubeRightExtension_face_zero]
  rfl

/-- 元の標準面で一座標を保持してから延長すると、元の右側自由座標の一段追加。 -/
lemma serreCubeFaceNormalRightExtension_keep {n m : ℕ} (d : CubeFaceNormal n m) (t : ℕ) :
    HEq (serreCubeFaceNormalRightExtension A (.keep d) t)
      (serreCubeFaceNormalRightExtension A d (t + 1)) := by
  exact serreCubeRightExtension_rightTensor_heq A (serreCubeFaceNormal A d) t

end SerrePositivity.KST.SConstruction
