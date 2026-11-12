module
public import SerrePositivity.KST.SConstruction.CubeDeletionFaceNormal

/-! # 削除・面の二段表示の元の Serre 評価
概要：二段表示の正規化が元の面・削除の後合成を実際の Serre 射として保存する。
方針：既存の各標準表示の評価と入力削除の吸収の評価を合成する。
規約：元の三つの射と中間対象を保持する。使われ方：混合語全体の評価保存の帰納。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の削除・面の二段標準表示の Serre 評価。 -/
def serreCubeDeletionFaceNormal {n m : ℕ} (r : CubeDeletionFaceNormal n m) :
    serreCubeComonoid A n ⟶ serreCubeComonoid A m :=
  serreCubeDeletionNormal A r.deletion ≫ serreCubeFaceNormal A r.face

/-- 元の恒等射の二段表示は、元の Serre 恒等射を回収する。 -/
lemma serreCubeDeletionFaceNormal_id (n : ℕ) :
    serreCubeDeletionFaceNormal A (cubeDeletionFaceNormalId n) = 𝟙 _ := by
  dsimp only [serreCubeDeletionFaceNormal, cubeDeletionFaceNormalId]
  rw [serreCubeDeletionNormal_id, serreCubeFaceNormal_id, Category.comp_id]

/-- 二段表示への面の追加は、元の同じ Serre 面の後合成を回収する。 -/
lemma serreCubeDeletionFaceNormal_point {n m : ℕ} (r : CubeDeletionFaceNormal n m)
    (b : Bool) (i : Fin (m + 1)) :
    serreCubeDeletionFaceNormal A (cubeDeletionFaceNormalPoint r b i) =
      serreCubeDeletionFaceNormal A r ≫ serreCubeFace A b m i := by
  dsimp only [serreCubeDeletionFaceNormal, cubeDeletionFaceNormalPoint]
  rw [serreCubeFaceNormal_insert]
  exact (Category.assoc _ _ _).symm

/-- 入力削除の吸収は、元の同じ Serre 計算結果との合成を回収する。 -/
lemma serreCubeDeletionFaceNormal_afterResult {n a m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a)
    (r : CubeFaceDeletionResult a m) :
    serreCubeDeletionFaceNormal A (cubeDeletionFaceNormalAfterResult d r) =
      serreCubeDeletionNormal A d ≫ serreCubeFaceDeletionResult A r := by
  cases r with
  | pure f => rfl
  | input i f =>
    change serreCubeDeletionNormal A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase d i) ≫
      serreCubeFaceNormal A f = _
    rw [serreCubeDeletionNormal_erase]
    exact Category.assoc _ _ _

/-- 二段表示への削除の追加は、元の同じ Serre 削除の後合成を回収する。 -/
lemma serreCubeDeletionFaceNormal_delete {n m : ℕ} (r : CubeDeletionFaceNormal n (m + 1))
    (i : Fin (m + 1)) :
    serreCubeDeletionFaceNormal A (cubeDeletionFaceNormalDelete r i) =
      serreCubeDeletionFaceNormal A r ≫ serreCubeDegeneracy A m i := by
  dsimp only [cubeDeletionFaceNormalDelete]
  rw [serreCubeDeletionFaceNormal_afterResult, serreCubeFaceNormal_delete]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.KST.SConstruction
