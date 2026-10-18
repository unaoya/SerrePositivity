module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleUnit

/-!
概要：KST §3.1 の包含に対応する係数 dg 圏の標準単位矢。
方針：目標代数の単位を包含 Hom に送り、左右の局所作用との全次数自然性を確認する。
規約：任意の同型の存在ではなく、図式に備わる指定の矢を使う。
使われ方：canonical な図式加群の cartesian 比較射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open DifferentialGraded

variable {R : Type u} [CommRing R]

/-- 概要：係数遷移後の乗法で第二因子の単位を掛けると元の係数射になる。
方針：tensor の交換法則、目標の右単位律、unitor の自然性を使う。
規約：KST §3.1。使われ方：標準単位矢との局所作用の比較。 -/
@[reassoc] theorem diagramAlgebraMul_unit_right {A B : Mon (Complex R)} (f : A ⟶ B) :
    A.X ◁ MonObj.one (X := B.X) ≫ diagramAlgebraMul f = (ρ_ A.X).hom ≫ f.hom := by
  unfold diagramAlgebraMul
  rw [tensorHom_id, whisker_exchange_assoc, MonObj.mul_one, rightUnitor_naturality]

/-- 概要：目標単位と係数射を掛けると左 unitor に続く係数射になる。
方針：tensor を分けて目標の左単位律と unitor の自然性を使う。
規約：KST §3.1。使われ方：標準単位矢の全次数自然性。 -/
@[reassoc] theorem diagramAlgebraMul_unit_left_map {A B : Mon (Complex R)} (f : A ⟶ B) :
    (MonObj.one (X := B.X) ⊗ₘ f.hom) ≫ MonObj.mul = (λ_ A.X).hom ≫ f.hom := by
  rw [tensorHom_def, Category.assoc, ← whisker_exchange_assoc,
    MonObj.one_mul, leftUnitor_naturality]

variable {J : Type v} [Preorder J] [DecidableLE J]

/-- 概要：包含に対応する係数 dg 圏の標準単位矢。
方針：目標代数の単位を包含の Hom に送る。
規約：KST §3.1。使われ方：図式加群の canonical な遷移射。 -/
def diagramModuleTransitionUnit (F : J ⥤ Mon (Complex R)) {i j : J} (h : i ≤ j) :
    𝟙_ (Complex R) ⟶ diagramModuleHom F i j :=
  MonObj.one (X := (F.obj j).X) ≫ diagramModuleHomInclusion F h

/-- 概要：標準単位矢の左側の局所作用の合成公式。
方針：包含上の Hom 合成公式を使い、右単位を掛ける係数乗法を計算する。
規約：KST §3.1。使われ方：標準単位矢の全次数自然性の一辺。 -/
theorem diagramModuleTransitionUnit_left_action (F : J ⥤ Mon (Complex R)) {i j : J}
    (h : i ≤ j) :
    (diagramModuleHomInclusion F (le_refl i) ⊗ₘ diagramModuleTransitionUnit F h) ≫
      diagramModuleComp F i i j =
    (ρ_ (F.obj i).X).hom ≫ (F.map (homOfLE h)).hom ≫ diagramModuleHomInclusion F h := by
  unfold diagramModuleTransitionUnit
  rw [← whiskerLeft_comp_tensorHom_assoc, diagramModuleComp_on_le]
  simpa only [diagramAlgebraMul, Category.assoc] using
    diagramAlgebraMul_unit_right_assoc (F.map (homOfLE h)) (diagramModuleHomInclusion F h)

/-- 概要：標準単位矢の右側の局所作用の合成公式。
方針：二つの tensor を分けて包含上の合成公式と目標の左単位律を使う。
規約：KST §3.1。使われ方：標準単位矢の全次数自然性の他辺。 -/
theorem diagramModuleTransitionUnit_right_action (F : J ⥤ Mon (Complex R)) {i j : J}
    (h : i ≤ j) :
    (diagramModuleTransitionUnit F h ⊗ₘ
      ((F.map (homOfLE h)).hom ≫ diagramModuleHomInclusion F (le_refl j))) ≫
        diagramModuleComp F i j j =
    (λ_ (F.obj i).X).hom ≫ (F.map (homOfLE h)).hom ≫ diagramModuleHomInclusion F h := by
  unfold diagramModuleTransitionUnit
  rw [← tensorHom_comp_tensorHom_assoc, diagramModuleComp_on_le]
  rw [show F.map (homOfLE (le_refl j)) = 𝟙 (F.obj j) from CategoryTheory.Functor.map_id F j]
  simp only [Mon.id_hom', id_tensorHom_id, Category.id_comp]
  exact diagramAlgebraMul_unit_left_map_assoc (F.map (homOfLE h)) (diagramModuleHomInclusion F h)

/-- 概要：標準単位矢は局所係数の全 Hom 作用に関して自然。
方針：左右の作用を unitor と係数射へ戻し、単位と Hom の braiding を簡約する。
規約：KST §3.1、パラメータは単位複体で全次数の自然性を述べる。
使われ方：canonical な比較射の dg 自然性フィールド。 -/
theorem diagramModuleTransitionUnit_natural (F : J ⥤ Mon (Complex R)) {i j : J}
    (h : i ≤ j) :
    (β_ (𝟙_ (Complex R)) (F.obj i).X).hom ≫
      (diagramModuleHomInclusion F (le_refl i) ⊗ₘ diagramModuleTransitionUnit F h) ≫
        diagramModuleComp F i i j =
    (diagramModuleTransitionUnit F h ⊗ₘ
      ((F.map (homOfLE h)).hom ≫ diagramModuleHomInclusion F (le_refl j))) ≫
        diagramModuleComp F i j j := by
  rw [diagramModuleTransitionUnit_left_action, diagramModuleTransitionUnit_right_action,
    braiding_tensorUnit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.KST.DerivedBlowup
