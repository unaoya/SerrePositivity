module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormalDetection
public import SerrePositivity.KST.SConstruction.SerreCubePrefixNaturality

/-! # 保持・削除標準表示の元の Serre 評価
概要：標準表示を元の右端削除と tensor 恒等で評価し、一出力削除との厳密な整合性を示す。
方針：右端削除の自然性と tensor 合成則を用いて入力次元で帰納する。
規約：元の Serre 余モノイド射のまま比較する。使われ方：削除語の表示非依存性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 保持・削除標準表示の元の Serre 余モノイド射による評価。 -/
def serreCubeDeletionNormal : {n m : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, _, .nil => 𝟙 _
  | _, _, .drop d => serreCubeDegeneracy A _ 0 ≫ serreCubeDeletionNormal d
  | _, _, .keep d => serreCubeDeletionNormal d ⊗ₘ 𝟙 (serreIntervalComonoid A)

/-- 全入力を保持する標準表示は、元の Serre 恒等射。 -/
lemma serreCubeDeletionNormal_id (n : ℕ) :
    serreCubeDeletionNormal A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId n) = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (serreCubeDeletionNormal A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId n) ⊗ₘ
      𝟙 (serreIntervalComonoid A)) = 𝟙 _
    rw [ih]
    simp

/-- 標準表示の一出力削除は、元の同じ Serre 削除との合成を厳密に回収する。 -/
lemma serreCubeDeletionNormal_erase {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n (m + 1))
    (i : Fin (m + 1)) :
    serreCubeDeletionNormal A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase d i) =
      serreCubeDeletionNormal A d ≫ serreCubeDegeneracy A m i := by
  induction n generalizing m with
  | zero => cases d
  | succ n ih =>
    cases d with
    | drop d =>
      change serreCubeDegeneracy A n 0 ≫
        serreCubeDeletionNormal A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase d i) = _
      rw [ih d i]
      exact (Category.assoc _ _ _).symm
    | keep d =>
      cases m with
      | zero =>
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        exact (serreCubeDegeneracy_zero_naturality A (serreCubeDeletionNormal A d)).symm
      | succ m =>
        refine Fin.cases ?_ (fun i => ?_) i
        · exact (serreCubeDegeneracy_zero_naturality A (serreCubeDeletionNormal A d)).symm
        · change serreCubeDeletionNormal A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase d i) ⊗ₘ
              𝟙 (serreIntervalComonoid A) =
            (serreCubeDeletionNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
              (serreCubeDegeneracy A m i ⊗ₘ 𝟙 (serreIntervalComonoid A))
          rw [ih d i]
          simp only [tensorHom_comp_tensorHom, Category.comp_id]

end SerrePositivity.KST.SConstruction
