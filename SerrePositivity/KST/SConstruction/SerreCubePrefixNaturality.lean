module
public import SerrePositivity.KST.SConstruction.SerreCubeCoordinateLaws
public import SerrePositivity.KST.SConstruction.TensorRightCoordinateNaturality

/-! # 左側の任意の射と右端の座標操作の交換
概要：左側の鎖立方体の任意の射は、右端の面・退化・connection と厳密に交換する。
方針：元の座標射の再帰式へ抽象 monoidal 自然性を適用する。
規約：両端点と任意の次元の左側の射を含む。使われ方：離れた cubical 座標の関係式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 左側の任意の射と右端の元の端点挿入は、厳密に自然。 -/
lemma serreCubeFace_zero_naturality {n m : ℕ} (b : Bool)
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) :
    f ≫ serreCubeFace A b m 0 = serreCubeFace A b n 0 ≫
      (f ⊗ₘ 𝟙 (serreIntervalComonoid A)) := by
  rw [serreCubeFace_zero, serreCubeFace_zero]
  simp only [id_tensorHom, tensorHom_id, Category.assoc]
  exact tensorRightPoint_naturality f (serreIntervalEndpointComonHom A b)

/-- 左側の任意の射と右端の元の削除は、厳密に自然。 -/
lemma serreCubeDegeneracy_zero_naturality {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) :
    (f ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫ serreCubeDegeneracy A m 0 =
      serreCubeDegeneracy A n 0 ≫ f := by
  rw [serreCubeDegeneracy_zero, serreCubeDegeneracy_zero]
  simp only [id_tensorHom, tensorHom_id, Category.assoc]
  exact tensorRightDeletion_naturality f (serreIntervalAugmentationComonHom A)

/-- 左側の任意の射と右端二因子の元の connection は、厳密に自然。 -/
lemma serreCubeConnection_zero_naturality {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) :
    ((f ⊗ₘ 𝟙 (serreIntervalComonoid A)) ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      serreCubeConnection A m 0 = serreCubeConnection A n 0 ≫
        (f ⊗ₘ 𝟙 (serreIntervalComonoid A)) := by
  rw [serreCubeConnection_zero, serreCubeConnection_zero]
  simp only [id_tensorHom, tensorHom_id, Category.assoc]
  exact tensorRightConnection_naturality f (serreIntervalMaxComonHom A)

end SerrePositivity.KST.SConstruction
