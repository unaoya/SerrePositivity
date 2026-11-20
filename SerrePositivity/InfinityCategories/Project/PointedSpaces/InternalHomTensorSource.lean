module


public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor

/-!
概要：反復 curry の同型の二つの源に関する自然性。
方針：二重評価で前合成と結合子の自然性を比較する。
規約：閉モノイダル圏の通常の射の等式。
使われ方：Goerss–Jardine I §7、HA §1.4.2。パラメータを含む二重 loop の交換の比較。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomTensor
end SerrePositivity.KST.Spectra.InternalHomTensor
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource
open _root_.SerrePositivity.KST.Spectra.InternalHomTensor

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 概要：テンソルの第一因子の制限は反復内部 Hom の内側の源の制限に対応する。
方針：二重に uncurry し、評価の前合成の式と結合子の自然性を使う。
規約：源の射 i に同型性を要求しない。
使われ方：HA §1.4.2。loop の次数射と反復 curry の可換式。 -/
@[reassoc]
theorem natural_pre_left {A' A : C} (i : A' ⟶ A) (B Y : C) :
    (MonoidalClosed.pre (i ▷ B)).app Y ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A' B Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Y).hom ≫ (ihom B).map ((MonoidalClosed.pre i).app Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso_eq_ihomCurryIso, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso_eq_ihomCurryIso]
  apply uncurry_injective
  apply uncurry_injective
  simp only [ihomCurryIso_hom]
  rw [uncurry_natural_left, uncurry_natural_right, uncurry_natural_left,
    uncurry_pre_app, uncurry_uncurry_ihomCurry, uncurry_uncurry_ihomCurry]
  rw [associator_inv_naturality_right_assoc, id_tensor_pre_app_comp_ev]
  exact (associator_inv_naturality_left_assoc i B ((ihom (A ⊗ B)).obj Y)
    ((ihom.ev (A ⊗ B)).app Y)).symm

/-- 概要：テンソルの第二因子の制限は反復内部 Hom の外側の源の制限に対応する。
方針：二重評価で結合子の中央因子の自然性を使う。
規約：源の射 j は任意。
使われ方：Goerss–Jardine I §7。パラメータの移動と二つの円の制限の整合性。 -/
@[reassoc]
theorem natural_pre_right (A : C) {B' B : C} (j : B' ⟶ B) (Y : C) :
    (MonoidalClosed.pre (A ◁ j)).app Y ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B' Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso A B Y).hom ≫ (MonoidalClosed.pre j).app ((ihom A).obj Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso_eq_ihomCurryIso, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso_eq_ihomCurryIso]
  apply uncurry_injective
  apply uncurry_injective
  simp only [ihomCurryIso_hom]
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_natural_left, uncurry_natural_left,
    uncurry_uncurry_ihomCurry, uncurry_uncurry_ihomCurry]
  rw [associator_inv_naturality_right_assoc, id_tensor_pre_app_comp_ev]
  exact (associator_inv_naturality_middle_assoc A j ((ihom (A ⊗ B)).obj Y)
    ((ihom.ev (A ⊗ B)).app Y)).symm

end

end SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorSource

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
