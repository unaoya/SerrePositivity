module
public import SerrePositivity.KST.SConstruction.SerreCubeConnectionNormalDeletion
public import SerrePositivity.KST.SConstruction.CubeDeletionNormalComposition

/-! # 削除・max の二段表示の生成射による更新
概要：追加の入力削除を吸収し、任意座標の出力削除と connection を二段表示へ戻す。
方針：削除標準表示の合成とブロック削除の評価保存を合成する。
規約：元の頂点関数と Serre 射の両方を保持する。使われ方：max・削除の混合語の正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の恒等射の削除・max の二段表示。 -/
def cubeDeletionConnectionNormalId (n : ℕ) : CubeDeletionConnectionNormal n n :=
  cubeDeletionConnectionNormalFrom (cubeConnectionNormalId n)

/-- 追加の入力削除を、元の削除因子へ吸収する。 -/
def cubeDeletionConnectionNormalPrepend {n a m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a)
    (r : CubeDeletionConnectionNormal a m) : CubeDeletionConnectionNormal n m :=
  ⟨r.middle, cubeDeletionNormalComp d r.deletion, r.connection⟩

/-- 二段表示へ元の任意座標の connection を追加する。 -/
def cubeDeletionConnectionNormalConnect {n m : ℕ} (r : CubeDeletionConnectionNormal n (m + 2))
    (i : Fin (m + 1)) : CubeDeletionConnectionNormal n (m + 1) :=
  ⟨r.middle, r.deletion, cubeConnectionNormalConnect r.connection i⟩

/-- 二段表示へ元の任意座標の出力削除を追加する。 -/
def cubeDeletionConnectionNormalDelete {n m : ℕ} (r : CubeDeletionConnectionNormal n (m + 1))
    (i : Fin (m + 1)) : CubeDeletionConnectionNormal n m :=
  cubeDeletionConnectionNormalPrepend r.deletion (cubeConnectionNormalDelete r.connection i)

/-- 恒等射の二段表示の元の頂点関数は恒等。 -/
lemma cubeDeletionConnectionNormalId_vertex (n : ℕ) :
    cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalId n) = _root_.id := by
  funext x
  exact (cubeDeletionConnectionNormalFrom_vertex _ x).trans
    (congrFun (cubeConnectionNormalId_vertex n) x)

/-- 追加の入力削除の吸収は、元の頂点関数の前合成を回収する。 -/
lemma cubeDeletionConnectionNormalPrepend_vertex {n a m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a)
    (r : CubeDeletionConnectionNormal a m) :
    cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalPrepend d r) =
      cubeDeletionConnectionNormalVertex r ∘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d := by
  dsimp only [cubeDeletionConnectionNormalVertex, cubeDeletionConnectionNormalPrepend]
  rw [cubeDeletionNormalComp_vertex]
  rfl

/-- connection の追加は、元の頂点関数の同じ後合成を回収する。 -/
lemma cubeDeletionConnectionNormalConnect_vertex {n m : ℕ}
    (r : CubeDeletionConnectionNormal n (m + 2)) (i : Fin (m + 1)) :
    cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalConnect r i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m i ∘ cubeDeletionConnectionNormalVertex r := by
  dsimp only [cubeDeletionConnectionNormalVertex, cubeDeletionConnectionNormalConnect]
  rw [cubeConnectionNormalVertex_connect]
  rfl

/-- 出力削除の追加は、元の頂点関数の同じ後合成を回収する。 -/
lemma cubeDeletionConnectionNormalDelete_vertex {n m : ℕ}
    (r : CubeDeletionConnectionNormal n (m + 1)) (i : Fin (m + 1)) :
    cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalDelete r i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy m i ∘ cubeDeletionConnectionNormalVertex r := by
  dsimp only [cubeDeletionConnectionNormalDelete]
  rw [cubeDeletionConnectionNormalPrepend_vertex, cubeConnectionNormalDelete_vertex]
  rfl

variable (A : Type u) [CommRing A]

/-- 恒等射の二段表示は元の Serre 恒等射。 -/
lemma serreCubeDeletionConnectionNormal_id (n : ℕ) :
    serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalId n) = 𝟙 _ :=
  (serreCubeDeletionConnectionNormal_from A _).trans (serreCubeConnectionNormal_id A n)

/-- 入力削除の吸収は、元の Serre 射の同じ前合成。 -/
lemma serreCubeDeletionConnectionNormal_prepend {n a m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a)
    (r : CubeDeletionConnectionNormal a m) :
    serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalPrepend d r) =
      serreCubeDeletionNormal A d ≫ serreCubeDeletionConnectionNormal A r := by
  dsimp only [serreCubeDeletionConnectionNormal, cubeDeletionConnectionNormalPrepend]
  rw [serreCubeDeletionNormal_comp]
  exact Category.assoc _ _ _

/-- connection の追加は、元の Serre 射の同じ後合成。 -/
lemma serreCubeDeletionConnectionNormal_connect {n m : ℕ}
    (r : CubeDeletionConnectionNormal n (m + 2)) (i : Fin (m + 1)) :
    serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalConnect r i) =
      serreCubeDeletionConnectionNormal A r ≫ serreCubeConnection A m i := by
  dsimp only [serreCubeDeletionConnectionNormal, cubeDeletionConnectionNormalConnect]
  rw [serreCubeConnectionNormal_connect]
  exact (Category.assoc _ _ _).symm

/-- 出力削除の追加は、元の Serre 射の同じ後合成。 -/
lemma serreCubeDeletionConnectionNormal_delete {n m : ℕ}
    (r : CubeDeletionConnectionNormal n (m + 1)) (i : Fin (m + 1)) :
    serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalDelete r i) =
      serreCubeDeletionConnectionNormal A r ≫ serreCubeDegeneracy A m i := by
  dsimp only [cubeDeletionConnectionNormalDelete]
  rw [serreCubeDeletionConnectionNormal_prepend, serreCubeConnectionNormal_delete]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.KST.SConstruction
