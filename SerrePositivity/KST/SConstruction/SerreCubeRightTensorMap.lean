module
public import SerrePositivity.KST.SConstruction.CubeRightKeepHom
public import SerrePositivity.KST.SConstruction.MonoidalRightTensorMapLaws

/-! # 対象の次元を固定した元の右 tensor 射
概要：元の鎖立方体の射の右 tensor を、n+1・m+1 次元の元の対象型で与える。
方針：tensor 射の四つの対象を明示し、元の tensor 操作をそのまま使う。
規約：区間は右因子のまま。使われ方：右端保持と鎖 tensor の型を保った比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右 tensor 射を、源・標的の鎖立方体の次元を固定して与える。 -/
def serreCubeRightTensorMap {n m : ℕ} (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) :
    serreCubeComonoid A (n + 1) ⟶ serreCubeComonoid A (m + 1) :=
  @tensorHom (Comon (Complex A)) _ _ (serreCubeComonoid A n) (serreCubeComonoid A m)
    (serreIntervalComonoid A) (serreIntervalComonoid A) f (𝟙 (serreIntervalComonoid A))

/-- 次元を固定した右 tensor は元の恒等射を保つ。 -/
lemma serreCubeRightTensorMap_id (n : ℕ) :
    serreCubeRightTensorMap A (𝟙 (serreCubeComonoid A n)) =
      𝟙 (serreCubeComonoid A (n + 1)) := by
  exact monoidalRightTensorMap_id (serreCubeComonoid A n) (serreIntervalComonoid A)

/-- 次元を固定した右 tensor は元の射の合成を保つ。 -/
lemma serreCubeRightTensorMap_comp {n m l : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m)
    (g : serreCubeComonoid A m ⟶ serreCubeComonoid A l) :
    serreCubeRightTensorMap A (f ≫ g) =
      serreCubeRightTensorMap A f ≫ serreCubeRightTensorMap A g := by
  exact monoidalRightTensorMap_comp (X := serreCubeComonoid A n)
    (Y := serreCubeComonoid A m) (Z := serreCubeComonoid A l)
    (I := serreIntervalComonoid A) f g

/-- 元の面の内側の再帰式を、次元を固定した右 tensor として回収する。 -/
lemma serreCubeRightTensorMap_face (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    serreCubeFace A b (n + 1) i.succ =
      serreCubeRightTensorMap A (n := n) (m := n + 1) (serreCubeFace A b n i) :=
  serreCubeFace_succ A b n i

/-- 元の削除の内側の再帰式を、次元を固定した右 tensor として回収する。 -/
lemma serreCubeRightTensorMap_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    serreCubeDegeneracy A (n + 1) i.succ =
      serreCubeRightTensorMap A (n := n + 1) (m := n) (serreCubeDegeneracy A n i) :=
  serreCubeDegeneracy_succ A n i

/-- 元の connection の内側の再帰式を、次元を固定した右 tensor として回収する。 -/
lemma serreCubeRightTensorMap_connection (n : ℕ) (i : Fin (n + 1)) :
    serreCubeConnection A (n + 1) i.succ =
      serreCubeRightTensorMap A (n := n + 2) (m := n + 1) (serreCubeConnection A n i) :=
  serreCubeConnection_succ A n i

end SerrePositivity.KST.SConstruction
