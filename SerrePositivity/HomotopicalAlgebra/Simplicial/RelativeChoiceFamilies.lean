module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceSpace
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterComposition

/-!
# 中断した任意モデル源への一般化：RelativeChoiceFamilies

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The universal property of actual relative extension families。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0537][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0537
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The universal property of actual relative extension families

Families with their entire fixed boundary are exactly maps to the
pullback choice space. No model structure or Kan condition is needed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.RelativeChoiceSpace
variable {A B K T U : SSet.{v}} (i : A ⟶ B) (b : A ⟶ K)

lemma family_boundary_const (s : T ⟶ obj i b) :
    i ▷ T ≫ family i b s = ParameterComposition.const T b := by
  rw [family_fixed_boundary]
  ext n x
  rfl

lemma family_ofExtension_const (e : B ⟶ K) (he : i ≫ e = b) :
    family i b (ofExtension i b e he) =
      ParameterComposition.const (SSet.stdSimplex.obj (SimplexCategory.mk 0)) e := by
  rw [family_ofExtension]
  ext n x
  rfl

lemma uncurry_constant_name :
    uncurry (SSet.stdSimplex.isTerminalObj₀.from T ≫ name b) =
      ParameterComposition.const T b := by
  rw [name, ← Category.assoc, uncurry_natural_left]
  dsimp only [curry']
  rw [uncurry_curry]
  ext n x
  rfl

def ofFamily (h : B ⊗ T ⟶ K) (hh : i ▷ T ≫ h = ParameterComposition.const T b) :
    T ⟶ obj i b :=
  pullback.lift (curry h) (SSet.stdSimplex.isTerminalObj₀.from T) (by
    apply uncurry_injective
    change uncurry (curry h ≫ (pre i).app K) = _
    rw [uncurry_pre_app, uncurry_curry, hh, uncurry_constant_name])

lemma ofFamily_family (h : B ⊗ T ⟶ K)
    (hh : i ▷ T ≫ h = ParameterComposition.const T b) :
    family i b (ofFamily i b h hh) = h := by
  rw [family, ofFamily, pullback.lift_fst, uncurry_curry]

lemma family_injective : Function.Injective (family i b (K := T)) := by
  intro s t h
  apply pullback.hom_ext
  · exact uncurry_injective h
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

lemma family_ofFamily (s : T ⟶ obj i b) :
    ofFamily i b (family i b s) (family_boundary_const i b s) = s := by
  apply family_injective i b
  exact ofFamily_family i b _ _

def familyEquiv : (T ⟶ obj i b) ≃
    {h : B ⊗ T ⟶ K // i ▷ T ≫ h = ParameterComposition.const T b} where
  toFun s := ⟨family i b s, family_boundary_const i b s⟩
  invFun h := ofFamily i b h.1 h.2
  left_inv := family_ofFamily i b
  right_inv h := Subtype.ext (ofFamily_family i b h.1 h.2)

lemma ofFamily_naturality (j : U ⟶ T) (h : B ⊗ T ⟶ K)
    (hh : i ▷ T ≫ h = ParameterComposition.const T b)
    (hj : i ▷ U ≫ (B ◁ j ≫ h) = ParameterComposition.const U b) :
    j ≫ ofFamily i b h hh = ofFamily i b (B ◁ j ≫ h) hj := by
  apply family_injective i b
  rw [family_naturality, ofFamily_family, ofFamily_family]

end SerrePositivity.SimplicialModel.RelativeChoiceSpace
