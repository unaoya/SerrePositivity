module
public import SerrePositivity.KST.SConstruction.SerreCubeRightExtension

/-! # 元の右側自由座標の延長と次元比較
概要：元の射の異種等号を右側の延長へ移し、区間を一つ付ける順序と比較する。
方針：次元等号を消去し、元の一段の右 tensor 射の反復で帰納する。
規約：区間を右側に付ける順序は変更しない。使われ方：生成元の辺保持の帰納。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の同じ次元の射の比較を、元の一段の右 tensor 射へ移す。 -/
lemma serreCubeRightTensorMap_heq {n m n' m' : ℕ} (hn : n = n') (hm : m = m')
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m)
    (g : serreCubeComonoid A n' ⟶ serreCubeComonoid A m') (h : HEq f g) :
    HEq (serreCubeRightTensorMap A f) (serreCubeRightTensorMap A g) := by
  cases hn
  cases hm
  cases eq_of_heq h
  rfl

/-- 元の同じ次元の余モノイド射の比較は、元の underlying 鎖射の比較を与える。 -/
lemma serreCubeComonoidHom_heq_hom {n m n' m' : ℕ} (hn : n = n') (hm : m = m')
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m)
    (g : serreCubeComonoid A n' ⟶ serreCubeComonoid A m') (h : HEq f g) :
    HEq f.hom g.hom := by
  cases hn
  cases hm
  cases eq_of_heq h
  rfl

/-- 元の同じ次元の射の比較を、全ての元の右側自由座標による延長へ移す。 -/
lemma serreCubeRightExtension_heq {n m n' m' : ℕ} (hn : n = n') (hm : m = m')
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m)
    (g : serreCubeComonoid A n' ⟶ serreCubeComonoid A m') (h : HEq f g) (t : ℕ) :
    HEq (serreCubeRightExtension A f t) (serreCubeRightExtension A g t) := by
  cases hn
  cases hm
  cases eq_of_heq h
  rfl

/-- 元の一段の右 tensor の後に t 座標を付けると、元の t+1 座標の延長と一致する。 -/
lemma serreCubeRightExtension_rightTensor_heq {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) (t : ℕ) :
    HEq (serreCubeRightExtension A (serreCubeRightTensorMap A f) t)
      (serreCubeRightExtension A f (t + 1)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change HEq (serreCubeRightTensorMap A
      (serreCubeRightExtension A (serreCubeRightTensorMap A f) t))
      (serreCubeRightTensorMap A (serreCubeRightExtension A f (t + 1)))
    exact serreCubeRightTensorMap_heq A (by omega) (by omega) _ _ ih

end SerrePositivity.KST.SConstruction
