module
public import SerrePositivity.KST.SConstruction.SerreCubeCoordinateLaws

/-! # 同じ座標の端点挿入と退化の厳密な退縮
概要：任意の端点を挿入して同じ座標を削除すると、元の鎖立方体の恒等射になる。
方針：余モノイドの単位への射の一意性と tensor の関手性で帰納する。
規約：両端点と全座標を含む。使われ方：cubical 面退化関係の基本式。
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

/-- 元の両端点の挿入と増大の合成は、単位余モノイドの恒等射。 -/
lemma serreIntervalEndpointComonHom_augmentation (b : Bool) :
    serreIntervalEndpointComonHom A b ≫ serreIntervalAugmentationComonHom A =
      𝟙 (𝟙_ (Comon (Complex A))) :=
  Subsingleton.elim _ _

/-- 右端の挿入と同じ座標の削除は、厳密に恒等射。 -/
lemma serreCubeFace_zero_degeneracy (b : Bool) (n : ℕ) :
    serreCubeFace A b n 0 ≫ serreCubeDegeneracy A n 0 = 𝟙 (serreCubeComonoid A n) := by
  rw [serreCubeFace_zero, serreCubeDegeneracy_zero]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    serreIntervalEndpointComonHom_augmentation, tensorHom_id, id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id]

/-- 元の任意の座標の端点挿入は、同じ座標の退化の厳密な切断。 -/
lemma serreCubeFace_degeneracy (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    serreCubeFace A b n i ≫ serreCubeDegeneracy A n i = 𝟙 (serreCubeComonoid A n) := by
  induction n with
  | zero =>
    fin_cases i
    exact serreCubeFace_zero_degeneracy A b 0
  | succ n ih =>
    refine Fin.cases (serreCubeFace_zero_degeneracy A b (n + 1)) (fun j => ?_) i
    rw [serreCubeFace_succ, serreCubeDegeneracy_succ, tensorHom_comp_tensorHom, ih]
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight]
    rfl

end SerrePositivity.KST.SConstruction
