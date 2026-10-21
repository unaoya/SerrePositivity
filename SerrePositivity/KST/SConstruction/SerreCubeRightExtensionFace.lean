module
public import SerrePositivity.KST.SConstruction.SerreCubeRightExtension
public import SerrePositivity.KST.SConstruction.SerreCubeChainFace

/-! # 元の端点挿入の右側自由座標による延長
概要：元の零座標の端点挿入の右に t 個の自由座標を付けると、同じ座標 t の標準面。
方針：元の面と次元移送の一段の右 tensor 再帰を同時に帰納する。
規約：元の余モノイド射と実鎖面を保持。使われ方：生成元の零・一端点の追加の再帰。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右側に t 座標を保持する、同じ座標 t の標準面。 -/
def serreCubeRightFace (b : Bool) (n t : ℕ) :
    serreCubeComonoid A (n + t) ⟶ serreCubeComonoid A ((n + 1) + t) :=
  serreCubeFace A b (n + t) ⟨t, by omega⟩ ≫
    serreCubeDimensionMap A (show (n + t) + 1 = (n + 1) + t by omega)

/-- 右側が零個なら、元の零座標の標準面を回収する。 -/
lemma serreCubeRightFace_zero (b : Bool) (n : ℕ) :
    serreCubeRightFace A b n 0 = serreCubeFace A b n 0 := by
  exact Category.comp_id _

/-- 元の右側自由座標を一つ増やすと、同じ元の面の一段の右 tensor 射。 -/
lemma serreCubeRightFace_succ (b : Bool) (n t : ℕ) :
    serreCubeRightFace A b n (t + 1) = serreCubeRightTensorMap A (serreCubeRightFace A b n t) := by
  have h : (n + t) + 1 = (n + 1) + t := by omega
  change serreCubeFace A b ((n + t) + 1) (Fin.succ ⟨t, by omega⟩) ≫
    serreCubeDimensionMap A (congrArg Nat.succ h) =
      serreCubeRightTensorMap A
        (serreCubeFace A b (n + t) ⟨t, by omega⟩ ≫ serreCubeDimensionMap A h)
  rw [serreCubeRightTensorMap_face, serreCubeDimensionMap_succ, serreCubeRightTensorMap_comp]

/-- 元の零座標の端点挿入を延長すると、同じ元の数値座標の標準面を回収する。 -/
lemma serreCubeRightExtension_face_zero (b : Bool) (n t : ℕ) :
    serreCubeRightExtension A (serreCubeFace A b n 0) t = serreCubeRightFace A b n t := by
  induction t with
  | zero => exact (serreCubeRightFace_zero A b n).symm
  | succ t ih =>
    exact (congrArg (serreCubeRightTensorMap A) ih).trans (serreCubeRightFace_succ A b n t).symm

/-- 元の次元移送の underlying 鎖射は、元の同じ鎖複体の次元移送。 -/
lemma serreCubeDimensionMap_hom {n m : ℕ} (h : n = m) :
    (serreCubeDimensionMap A h).hom = eqToHom (congrArg (serreCubeComplex A) h) := by
  cases h
  rfl

/-- 元の右側自由座標を保持する面の underlying 鎖射は、元の指定次元の鎖面。 -/
lemma serreCubeRightFace_hom (b : Bool) (n t : ℕ) :
    (serreCubeRightFace A b n t).hom =
      serreCubeChainFace A b (n + t) ((n + 1) + t) (by omega) ⟨t, by omega⟩ := by
  unfold serreCubeRightFace serreCubeChainFace
  rw [Comon.comp_hom', serreCubeDimensionMap_hom]
  congr 2

end SerrePositivity.KST.SConstruction
