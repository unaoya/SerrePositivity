module
public import SerrePositivity.KST.SConstruction.SerreConcreteCubeMap
public import SerrePositivity.KST.SConstruction.SerreCubeRightTensorMap
public import SerrePositivity.KST.SConstruction.ConcreteCubeDimensionIso

/-! # 元の鎖立方体の次元移送
概要：元の次元の等号を鎖立方体の射へ移し、元の具体的構造射の評価を回収する。
方針：eqToHom と元の関手の恒等保存を使い、右端の一因子の保持とも照合する。
規約：元の座標の移送だけを使う。使われ方：連結鎖比較の結合・単位の coherence。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の次元の等号に沿った鎖立方体の射。 -/
def serreCubeDimensionMap {n m : ℕ} (h : n = m) :
    serreCubeComonoid A n ⟶ serreCubeComonoid A m := eqToHom (congrArg (serreCubeComonoid A) h)

/-- 元の恒等な次元移送は恒等射。 -/
lemma serreCubeDimensionMap_refl (n : ℕ) :
    serreCubeDimensionMap A (rfl : n = n) = 𝟙 (serreCubeComonoid A n) := rfl

/-- 元の次元移送の一段更新は、元の右 tensor と同じ射。 -/
lemma serreCubeDimensionMap_succ {n m : ℕ} (h : n = m) :
    serreCubeDimensionMap A (congrArg Nat.succ h) =
      serreCubeRightTensorMap A (n := n) (m := m) (serreCubeDimensionMap A h) := by
  cases h
  exact (serreCubeRightTensorMap_id A n).symm

/-- 元の具体的な次元同型の評価は、同じ鎖立方体の次元移送。 -/
lemma serreConcreteCubeMap_dimension {n m : ℕ} (h : n = m) :
    serreConcreteCubeMap A (concreteCubeDimensionIso
      (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n) (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m) h).hom = serreCubeDimensionMap A h := by
  cases h
  exact serreConcreteCubeMap_id A n

/-- 元の結合の次元移送は、一つ右端を保持しても同じ移送を与える。 -/
lemma serreCubeDimensionMap_assoc_succ (n m k : ℕ) :
    serreCubeDimensionMap A (Nat.add_assoc n m (k + 1)) =
      serreCubeRightTensorMap A (n := (n + m) + k) (m := n + (m + k))
        (serreCubeDimensionMap A (Nat.add_assoc n m k)) :=
  serreCubeDimensionMap_succ A (Nat.add_assoc n m k)

/-- 元の左単位の次元移送も、一つ右端を保持して更新される。 -/
lemma serreCubeDimensionMap_zero_add_succ (m : ℕ) :
    serreCubeDimensionMap A (Nat.zero_add (m + 1)) =
      serreCubeRightTensorMap A (n := 0 + m) (m := m)
        (serreCubeDimensionMap A (Nat.zero_add m)) :=
  serreCubeDimensionMap_succ A (Nat.zero_add m)

end SerrePositivity.KST.SConstruction
