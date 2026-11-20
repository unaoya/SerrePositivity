module


public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
概要：閉モノイダル圏の左テンソルが写像対象に誘導する射。
方針：結合子と評価の curry を用い、合成を評価後に検査する。
規約：特定の単体集合の商の定義を展開しない一般の圏論。
使われ方：HTT A.3.3、BF 1978 §2。suspension の豊穣合成の保存。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.TensorMapping
end SerrePositivity.KST.Spectra.TensorMapping
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping
open _root_.SerrePositivity.KST.Spectra.TensorMapping

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 概要：左テンソルによる写像対象への作用。
方針：結合子の後で評価し curry する。
規約：K を左からテンソルする。
使われ方：HTT A.3.3。suspension の写像空間への作用。 -/
def map (K X Y : C) : (ihom X).obj Y ⟶ (ihom (K ⊗ X)).obj (K ⊗ Y) :=
  curry ((α_ K X ((ihom X).obj Y)).hom ≫ K ◁ ((ihom.ev X).app Y))

/-- 概要：左テンソルの写像対象への作用の評価計算。
方針：curry と uncurry の逆関係を使う。
規約：全て C 内の射。
使われ方：HTT A.3.3、BF 1978 §2。合成の保存。 -/
@[reassoc]
theorem evaluation (K X Y : C) :
    (K ⊗ X) ◁ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X Y ≫ (ihom.ev (K ⊗ X)).app (K ⊗ Y) =
      (α_ K X ((ihom X).obj Y)).hom ≫ K ◁ ((ihom.ev X).app Y) :=
  uncurry_curry _

/-- 概要：左テンソルの写像対象への作用は豊穣合成を保つ。
方針：両辺を uncurry し、結合子の自然性と評価を用いる。
規約：任意の閉モノイダル圏。
使われ方：HTT A.3.3、BF 1978 §2。スペクトルの合成の整合性。 -/
theorem comp (K X Y Z : C) :
    MonoidalClosed.comp X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X Z =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K Y Z) ≫ MonoidalClosed.comp (K ⊗ X) (K ⊗ Y) (K ⊗ Z) := by
  apply uncurry_injective
  simp only [uncurry_natural_left]
  conv_lhs =>
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map, uncurry_curry, associator_naturality_right_assoc, ← whiskerLeft_comp,
      comp_eq, whiskerLeft_curry_ihom_ev_app, compTranspose_eq]
  conv_rhs =>
    rw [comp_eq, uncurry_curry, compTranspose_eq, tensorHom_def, whiskerLeft_comp]
  simp only [Category.assoc, whiskerLeft_comp]
  rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc,
    whisker_exchange_assoc, ← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.evaluation]
  dsimp only [Functor.id_obj]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.evaluation]
  simp

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
