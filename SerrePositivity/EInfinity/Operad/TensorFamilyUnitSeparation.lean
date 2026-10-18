module

public import SerrePositivity.EInfinity.Operad.TensorUnitFamilyHead
public import SerrePositivity.EInfinity.Operad.SchurComposition

/-!
# 単位係数を持つ有限テンソル対の分離

概要：Berger–Moerdijk §1 の全合成の右単位則で、分離した単位係数列の縮約を計算する。
方針：有限族の先頭から帰納し、二対の分離の単位則と単位族の縮約の先頭の式を使う。
規約：入力の列の順序は変更しない。
使われ方：Schur 作用を生成元の包含へ制限したときに単位係数を除く。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

private lemma separationUnit {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] (X Y : C) :
    tensorμ (𝟙_ C) X (𝟙_ C) Y ≫ ((λ_ (𝟙_ C)).hom ▷ (X ⊗ Y)) ≫
      (λ_ (X ⊗ Y)).hom = (λ_ X).hom ⊗ₘ (λ_ Y).hom := by
  simp only [tensorμ, tensorHom_def, braiding_tensorUnit_right,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：単位係数列を分離して縮約すると各入力の左単位子の有限テンソルになる（Berger–Moerdijk §1）。
方針：分離の再帰と二対の単位則を用い、残る尾に帰納仮定を適用する。
規約：空の族も含む。
使われ方：生成元への Schur 作用の計算で係数の単位族を取り除く。 -/
lemma tensorFamilyTensorIso_unit_left (n : ℕ) (V : Fin n → Complex A) :
    (tensorFamilyTensorIso n (fun _ => 𝟙_ (Complex A)) V).hom ≫
      ((tensorUnitFamilyIso A n).hom ⊗ₘ 𝟙 (tensorFamily n V)) ≫
      (λ_ (tensorFamily n V)).hom = tensorFamilyMap n (fun j => (λ_ (V j)).hom) := by
  induction n with
  | zero =>
    simp only [tensorFamilyTensorIso, tensorUnitFamilyIso, tensorFamily,
      tensorFamilyMap, Iso.symm_hom, Iso.refl_hom, tensorHom_id,
      id_whiskerRight, Category.id_comp, Iso.inv_hom_id]
  | succ n ih =>
    rw [tensorFamilyTensorIso, tensorUnitFamilyIso_succ_head]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, tensorHom_id,
      comp_whiskerRight, Category.assoc]
    have hn := tensorμ_natural_right (𝟙_ (Complex A)) (V 0)
      (tensorUnitFamilyIso A n).hom (𝟙 (tensorFamily n (fun j => V j.succ)))
    simp only [whiskerLeft_id, tensorHom_id] at hn
    erw [← reassoc_of% hn, separationUnit]
    rw [tensorHom_def']
    simp only [← whiskerLeft_comp_assoc]
    have hi := ih (fun j => V j.succ)
    simp only [tensorHom_id] at hi
    rw [hi]
    simp only [tensorFamilyMap, tensorHom_def']

end SerrePositivity.EInfinity
