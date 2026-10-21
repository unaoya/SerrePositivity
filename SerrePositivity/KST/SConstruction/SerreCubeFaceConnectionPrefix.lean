module
public import SerrePositivity.KST.SConstruction.SerreCubeAbsorptionRelations
public import SerrePositivity.KST.SConstruction.SerreCubeFaceConnectionFarRelations
public import SerrePositivity.KST.SConstruction.SerreCubeCoordinateRetractions

/-! # 面の後の右端 max の prefix に関する計算
概要：二つの定数、または定数一の吸収を、元の Serre 射の合成として照合する。
方針：任意の prefix 射で単位・吸収・同座標削除の式を先に証明する。
規約：検証上限を変更しない。使われ方：面・connection の標準化の Serre 評価保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 二つの元の定数面と右端 max の合成は、同じ定数の max の面。 -/
lemma serreCubeFace_connection_constants (b c : Bool) (m : ℕ) :
    (serreCubeFace A c m 0 ≫ serreCubeFace A b (m + 1) 0) ≫
        serreCubeConnection A m 0 = serreCubeFace A (b ⊔ c) m 0 := by
  cases b with
  | false =>
    simp only [Bool.max_eq_or, Bool.false_or]
    rw [Category.assoc, serreCubeFace_zero_connection_right, Category.comp_id]
  | true =>
    simp only [Bool.max_eq_or, Bool.true_or]
    rw [Category.assoc, serreCubeFace_one_connection_right_zero, ← Category.assoc,
      serreCubeFace_zero_degeneracy, Category.id_comp]

/-- 元の任意の prefix の後の一端点挿入と max は、入力削除と定数一を回収する。 -/
lemma serreCubeFace_connection_right_one_prefix {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) :
    ((f ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫ serreCubeFace A true (m + 1) 0) ≫
        serreCubeConnection A m 0 =
      serreCubeDegeneracy A n 0 ≫ (f ≫ serreCubeFace A true m 0) := by
  let g : serreCubeComonoid A (n + 1) ⟶ serreCubeComonoid A (m + 1) :=
    f ⊗ₘ 𝟙 (serreIntervalComonoid A)
  have hn : g ≫ serreCubeDegeneracy A m 0 = serreCubeDegeneracy A n 0 ≫ f :=
    serreCubeDegeneracy_zero_naturality A f
  change (g ≫ serreCubeFace A true (m + 1) 0) ≫ serreCubeConnection A m 0 = _
  rw [Category.assoc, serreCubeFace_one_connection_right_zero, ← Category.assoc, hn,
    Category.assoc]

/-- 元の prefix と零面を tensor へ移した右端 max は、同じ prefix の入力保持。 -/
lemma serreCubeFace_connection_left_zero_prefix {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) :
    ((f ≫ serreCubeFace A false m 0) ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      serreCubeConnection A m 0 = f ⊗ₘ 𝟙 (serreIntervalComonoid A) := by
  let g : serreCubeComonoid A (n + 1) ⟶ serreCubeComonoid A (m + 1) :=
    f ⊗ₘ 𝟙 (serreIntervalComonoid A)
  have ht : ((f ≫ serreCubeFace A false m 0) ⊗ₘ 𝟙 (serreIntervalComonoid A)) =
      g ≫ serreCubeFace A false (m + 1) (0 : Fin (m + 1)).succ := by
    change ((f ≫ serreCubeFace A false m 0) ⊗ₘ 𝟙 (serreIntervalComonoid A)) =
      (f ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
        (serreCubeFace A false m 0 ⊗ₘ 𝟙 (serreIntervalComonoid A))
    simp only [tensorHom_comp_tensorHom, Category.comp_id]
  rw [ht]
  change (g ≫ serreCubeFace A false (m + 1) (0 : Fin (m + 1)).succ) ≫
    serreCubeConnection A m 0 = g
  rw [Category.assoc, serreCubeFace_zero_connection_left, Category.comp_id]

/-- 元の prefix と一面を tensor へ移した右端 max も、入力削除と定数一を回収する。 -/
lemma serreCubeFace_connection_left_one_prefix {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) :
    ((f ≫ serreCubeFace A true m 0) ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
        serreCubeConnection A m 0 =
      serreCubeDegeneracy A n 0 ≫ (f ≫ serreCubeFace A true m 0) := by
  let g : serreCubeComonoid A (n + 1) ⟶ serreCubeComonoid A (m + 1) :=
    f ⊗ₘ 𝟙 (serreIntervalComonoid A)
  have ht : ((f ≫ serreCubeFace A true m 0) ⊗ₘ 𝟙 (serreIntervalComonoid A)) =
      g ≫ serreCubeFace A true (m + 1) (0 : Fin (m + 1)).succ := by
    change ((f ≫ serreCubeFace A true m 0) ⊗ₘ 𝟙 (serreIntervalComonoid A)) =
      (f ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
        (serreCubeFace A true m 0 ⊗ₘ 𝟙 (serreIntervalComonoid A))
    simp only [tensorHom_comp_tensorHom, Category.comp_id]
  have hn : g ≫ serreCubeDegeneracy A m 0 = serreCubeDegeneracy A n 0 ≫ f :=
    serreCubeDegeneracy_zero_naturality A f
  rw [ht]
  change (g ≫ serreCubeFace A true (m + 1) (0 : Fin (m + 1)).succ) ≫
    serreCubeConnection A m 0 = _
  rw [Category.assoc, serreCubeFace_one_connection_left_zero, ← Category.assoc, hn,
    Category.assoc]

end SerrePositivity.KST.SConstruction
