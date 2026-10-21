module
public import SerrePositivity.KST.SConstruction.CubeThreeNormal

/-! # 三段表示への面の計算結果の吸収
概要：面の後の削除・connection の残余を、既存の削除・max の二段表示へ吸収する。
方針：高々一つの入力操作を二段表示の更新へ渡し、残る面を添える。
規約：元の頂点・Serre の両評価を保持する。使われ方：全混合語の三段正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 三段表示の元の削除・max 部分。 -/
def cubeThreeNormalPrefix {n m : ℕ} (r : CubeThreeNormal n m) :
    CubeDeletionConnectionNormal n r.blocks :=
  ⟨r.retained, r.deletion, r.connection⟩

/-- 二段表示に元の面の残余を添える。 -/
def cubeThreeNormalWithFace {n a m : ℕ} (p : CubeDeletionConnectionNormal n a)
    (f : CubeFaceNormal a m) : CubeThreeNormal n m :=
  ⟨p.middle, a, p.deletion, p.connection, f⟩

/-- 面を添える構成は元の頂点関数の合成。 -/
lemma cubeThreeNormalWithFace_vertex {n a m : ℕ} (p : CubeDeletionConnectionNormal n a)
    (f : CubeFaceNormal a m) :
    cubeThreeNormalVertex (cubeThreeNormalWithFace p f) =
      cubeFaceNormalVertex f ∘ cubeDeletionConnectionNormalVertex p := rfl

/-- 面の削除結果の入力操作を元の二段表示へ吸収する。 -/
def cubeThreeNormalAfterDeletion {n : ℕ} : {a m : ℕ} →
    CubeDeletionConnectionNormal n a → CubeFaceDeletionResult a m → CubeThreeNormal n m
  | _, _, p, .pure f => cubeThreeNormalWithFace p f
  | _, _, p, .input i f =>
      cubeThreeNormalWithFace (cubeDeletionConnectionNormalDelete p i) f

/-- 面の connection 結果の入力操作を元の二段表示へ吸収する。 -/
def cubeThreeNormalAfterConnection {n : ℕ} : {a m : ℕ} →
    CubeDeletionConnectionNormal n a → CubeFaceConnectionResult a m → CubeThreeNormal n m
  | _, _, p, .pure f => cubeThreeNormalWithFace p f
  | _, _, p, .input i f =>
      cubeThreeNormalWithFace (cubeDeletionConnectionNormalDelete p i) f
  | _, _, p, .connect i f =>
      cubeThreeNormalWithFace (cubeDeletionConnectionNormalConnect p i) f

/-- 削除結果の吸収は、元の頂点での後合成を保つ。 -/
lemma cubeThreeNormalAfterDeletion_vertex {n a m : ℕ} (p : CubeDeletionConnectionNormal n a)
    (r : CubeFaceDeletionResult a m) :
    cubeThreeNormalVertex (cubeThreeNormalAfterDeletion p r) =
      cubeFaceDeletionResultVertex r ∘ cubeDeletionConnectionNormalVertex p := by
  cases r with
  | pure f => rfl
  | input i f =>
    change cubeFaceNormalVertex f ∘
      cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalDelete p i) = _
    rw [cubeDeletionConnectionNormalDelete_vertex]
    rfl

/-- connection 結果の吸収は、元の頂点での後合成を保つ。 -/
lemma cubeThreeNormalAfterConnection_vertex {n a m : ℕ} (p : CubeDeletionConnectionNormal n a)
    (r : CubeFaceConnectionResult a m) :
    cubeThreeNormalVertex (cubeThreeNormalAfterConnection p r) =
      cubeFaceConnectionResultVertex r ∘ cubeDeletionConnectionNormalVertex p := by
  cases r with
  | pure f => rfl
  | input i f =>
    change cubeFaceNormalVertex f ∘
      cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalDelete p i) = _
    rw [cubeDeletionConnectionNormalDelete_vertex]
    rfl
  | connect i f =>
    change cubeFaceNormalVertex f ∘
      cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalConnect p i) = _
    rw [cubeDeletionConnectionNormalConnect_vertex]
    rfl

variable (A : Type u) [CommRing A]

/-- 面を添える構成は元の Serre 射の合成。 -/
lemma serreCubeThreeNormal_withFace {n a m : ℕ} (p : CubeDeletionConnectionNormal n a)
    (f : CubeFaceNormal a m) :
    serreCubeThreeNormal A (cubeThreeNormalWithFace p f) =
      serreCubeDeletionConnectionNormal A p ≫ serreCubeFaceNormal A f := rfl

/-- 削除結果の吸収は、元の Serre 射の後合成を保つ。 -/
lemma serreCubeThreeNormal_afterDeletion {n a m : ℕ} (p : CubeDeletionConnectionNormal n a)
    (r : CubeFaceDeletionResult a m) :
    serreCubeThreeNormal A (cubeThreeNormalAfterDeletion p r) =
      serreCubeDeletionConnectionNormal A p ≫ serreCubeFaceDeletionResult A r := by
  cases r with
  | pure f => rfl
  | input i f =>
    change serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalDelete p i) ≫
      serreCubeFaceNormal A f = _
    rw [serreCubeDeletionConnectionNormal_delete]
    exact Category.assoc _ _ _

/-- connection 結果の吸収は、元の Serre 射の後合成を保つ。 -/
lemma serreCubeThreeNormal_afterConnection {n a m : ℕ} (p : CubeDeletionConnectionNormal n a)
    (r : CubeFaceConnectionResult a m) :
    serreCubeThreeNormal A (cubeThreeNormalAfterConnection p r) =
      serreCubeDeletionConnectionNormal A p ≫ serreCubeFaceConnectionResult A r := by
  cases r with
  | pure f => rfl
  | input i f =>
    change serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalDelete p i) ≫
      serreCubeFaceNormal A f = _
    rw [serreCubeDeletionConnectionNormal_delete]
    exact Category.assoc _ _ _
  | connect i f =>
    change serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalConnect p i) ≫
      serreCubeFaceNormal A f = _
    rw [serreCubeDeletionConnectionNormal_connect]
    exact Category.assoc _ _ _

end SerrePositivity.KST.SConstruction
