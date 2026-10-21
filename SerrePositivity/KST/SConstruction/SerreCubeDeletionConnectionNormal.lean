module
public import SerrePositivity.KST.SConstruction.CubeConnectionNormalDeletion
public import SerrePositivity.KST.SConstruction.SerreCubeConnectionDeletion
public import SerrePositivity.KST.SConstruction.SerreCubeConnectionDegeneracyFarRelations

/-! # 削除・max の二段表示の元の Serre 評価
概要：右端入力の削除・保持・結合の作用を、元の二段の Serre 射と照合する。
方針：削除と max の純粋な標準表示の評価を元の合成で束ねる。
規約：元の中間対象と元の射を保つ。使われ方：ブロック削除の評価保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の削除・max の二段表示の Serre 評価。 -/
def serreCubeDeletionConnectionNormal {n m : ℕ} (r : CubeDeletionConnectionNormal n m) :
    serreCubeComonoid A n ⟶ serreCubeComonoid A m :=
  serreCubeDeletionNormal A r.deletion ≫ serreCubeConnectionNormal A r.connection

/-- 入力を削除しない二段表示は、元の max の Serre 評価を回収する。 -/
lemma serreCubeDeletionConnectionNormal_from {n m : ℕ} (d : CubeConnectionNormal n m) :
    serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalFrom d) =
      serreCubeConnectionNormal A d := by
  dsimp only [serreCubeDeletionConnectionNormal, cubeDeletionConnectionNormalFrom]
  rw [serreCubeDeletionNormal_id, Category.id_comp]

/-- 右端入力の削除は、元の同じ入力削除の前合成。 -/
lemma serreCubeDeletionConnectionNormal_drop {n m : ℕ} (r : CubeDeletionConnectionNormal n m) :
    serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalDrop r) =
      serreCubeDegeneracy A n 0 ≫ serreCubeDeletionConnectionNormal A r := by
  exact Category.assoc _ _ _

/-- 新しいブロックの保持は、元の同じ二段評価と恒等の tensor。 -/
lemma serreCubeDeletionConnectionNormal_keep {n m : ℕ} (r : CubeDeletionConnectionNormal n m) :
    serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalKeep r) =
      serreCubeDeletionConnectionNormal A r ⊗ₘ 𝟙 (serreIntervalComonoid A) := by
  change (serreCubeDeletionNormal A r.deletion ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
    (serreCubeConnectionNormal A r.connection ⊗ₘ 𝟙 (serreIntervalComonoid A)) =
      (serreCubeDeletionNormal A r.deletion ≫ serreCubeConnectionNormal A r.connection) ⊗ₘ
        𝟙 (serreIntervalComonoid A)
  simp only [tensorHom_comp_tensorHom, Category.comp_id]

/-- 最初のブロックへの結合は、元の tensor 評価と右端 connection の合成。 -/
lemma serreCubeDeletionConnectionNormal_merge {n m : ℕ}
    (r : CubeDeletionConnectionNormal n (m + 1)) :
    serreCubeDeletionConnectionNormal A (cubeDeletionConnectionNormalMerge r) =
      (serreCubeDeletionConnectionNormal A r ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
        serreCubeConnection A m 0 := by
  let f : serreCubeComonoid A (n + 1) ⟶ serreCubeComonoid A (r.middle + 1) :=
    serreCubeDeletionNormal A r.deletion ⊗ₘ 𝟙 (serreIntervalComonoid A)
  let g : serreCubeComonoid A (r.middle + 1) ⟶ serreCubeComonoid A (m + 2) :=
    serreCubeConnectionNormal A r.connection ⊗ₘ 𝟙 (serreIntervalComonoid A)
  have ht : f ≫ g =
      (serreCubeDeletionNormal A r.deletion ≫ serreCubeConnectionNormal A r.connection) ⊗ₘ
        𝟙 (serreIntervalComonoid A) := by
    change (serreCubeDeletionNormal A r.deletion ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      (serreCubeConnectionNormal A r.connection ⊗ₘ 𝟙 (serreIntervalComonoid A)) = _
    simp only [tensorHom_comp_tensorHom, Category.comp_id]
  change f ≫ (g ≫ serreCubeConnection A m 0) =
    ((serreCubeDeletionNormal A r.deletion ≫ serreCubeConnectionNormal A r.connection) ⊗ₘ
      𝟙 (serreIntervalComonoid A)) ≫ serreCubeConnection A m 0
  rw [← Category.assoc, ht]
  rfl

end SerrePositivity.KST.SConstruction
