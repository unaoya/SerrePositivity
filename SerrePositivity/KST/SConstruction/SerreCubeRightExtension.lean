module
public import SerrePositivity.KST.SConstruction.SerreCubeDimensionTransport

/-! # 元の Serre 鎖立方体の右側自由座標による延長
概要：元の余モノイド射の右側に、指定個数の元の区間の恒等射を tensor する。
方針：元の一段の右 tensor 射を反復し、恒等・合成・次元移送の保存を示す。
規約：元の座標順を保持。使われ方：全生成元の標準面に右側自由座標を付ける。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の射の右側に t 個の自由座標の恒等射を付ける、元の同じ実余モノイド射。 -/
def serreCubeRightExtension {n m : ℕ} (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) :
    (t : ℕ) → (serreCubeComonoid A (n + t) ⟶ serreCubeComonoid A (m + t))
  | 0 => f
  | t + 1 => serreCubeRightTensorMap A (serreCubeRightExtension f t)

/-- 元の零個の右側自由座標では、元の同じ射を回収する。 -/
lemma serreCubeRightExtension_zero {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) :
    serreCubeRightExtension A f 0 = f := rfl

/-- 元の右側自由座標を一つ増やすと、元の同じ一段の右 tensor 射になる。 -/
lemma serreCubeRightExtension_succ {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) (t : ℕ) :
    serreCubeRightExtension A f (t + 1) =
      serreCubeRightTensorMap A (serreCubeRightExtension A f t) := rfl

/-- 元の右側自由座標による延長は、元の恒等射を保つ。 -/
lemma serreCubeRightExtension_id (n t : ℕ) :
    serreCubeRightExtension A (𝟙 (serreCubeComonoid A n)) t =
      𝟙 (serreCubeComonoid A (n + t)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change serreCubeRightTensorMap A _ = _
    rw [ih]
    exact serreCubeRightTensorMap_id A (n + t)

/-- 元の右側自由座標による延長は、元の射の合成を厳密に保つ。 -/
lemma serreCubeRightExtension_comp {n m k : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m)
    (g : serreCubeComonoid A m ⟶ serreCubeComonoid A k) (t : ℕ) :
    serreCubeRightExtension A (f ≫ g) t =
      serreCubeRightExtension A f t ≫ serreCubeRightExtension A g t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change serreCubeRightTensorMap A _ =
      serreCubeRightTensorMap A (serreCubeRightExtension A f t) ≫
        serreCubeRightTensorMap A (serreCubeRightExtension A g t)
    rw [ih, serreCubeRightTensorMap_comp]

/-- 元の次元等号を延長すると、元の同じ右側自由座標を加えた次元等号の移送。 -/
lemma serreCubeRightExtension_dimension {n m : ℕ} (h : n = m) (t : ℕ) :
    serreCubeRightExtension A (serreCubeDimensionMap A h) t =
      serreCubeDimensionMap A (congrArg (fun d => d + t) h) := by
  cases h
  rw [serreCubeDimensionMap_refl, serreCubeRightExtension_id]
  rfl

end SerrePositivity.KST.SConstruction
