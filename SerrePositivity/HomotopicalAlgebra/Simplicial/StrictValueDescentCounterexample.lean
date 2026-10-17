module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.StrictValueObstruction
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# 中断した任意モデル源への一般化：StrictValueDescentCounterexample

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A localized strict diagram with small Kan values that has no fixed-value strict lift。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0580][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0580
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A localized strict diagram with small Kan values that has no fixed-value strict lift

A constant point diagram gives a strict replacement after changing values.
Thus the obstruction concerns fixed values, not the existence of a strict replacement.
-/

@[expose] public section
universe v vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.StrictValueObstruction
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev Base := Codiscrete Bool

def value (b : Base) : SSet.{v} := if b.as then complex else point

def valueToPoint (b : Base) : value.{v} b ⟶ point := by
  rcases b with ⟨b⟩
  cases b
  · exact 𝟙 _
  · exact toPoint

lemma valueToPoint_weakEquivalence (b : Base) :
    weakEquivalences SSet.{v} (valueToPoint.{v} b) := by
  rcases b with ⟨b⟩
  cases b
  · exact (weakEquivalences SSet.{v}).id_mem _
  · exact toPoint_trivialFibration.2

include hfib in
lemma value_kanComplex (b : Base) : SSet.KanComplex (value.{v} b) := by
  rcases b with ⟨b⟩
  cases b
  · exact point_kanComplex
  · exact complex_kanComplex hfib

include hcof in
/-- Even objectwise isomorphisms to the selected Kan values cannot give a strict lift. -/
lemma no_fixed_value_lift (F : Base ⥤ SSet.{v})
    (e : ∀ b, F.obj b ≅ value.{v} b) : False := by
  apply not_iso_point hcof
  exact ⟨(e ⟨true⟩).symm ≪≫ F.mapIso (Codiscrete.iso ⟨true⟩ ⟨false⟩) ≪≫ e ⟨false⟩⟩

/-- A strict alternative is allowed to change the selected values by weak equivalences. -/
abbrev repair : Base ⥤ SSet.{v} := (Functor.const Base).obj point

variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{v})]

def valueIso (b : Base) : L.obj (value.{v} b) ≅ L.obj point := by
  have : IsIso (L.map (valueToPoint.{v} b)) :=
    Localization.inverts L (weakEquivalences SSet.{v}) _ (valueToPoint_weakEquivalence b)
  exact asIso (L.map (valueToPoint.{v} b))

/-- A strict localized diagram retains exactly the original independently selected values. -/
def localized : Base ⥤ H where
  obj b := L.obj (value.{v} b)
  map {b c} _ := (valueIso L b).hom ≫ (valueIso L c).inv
  map_id b := (valueIso L b).hom_inv_id
  map_comp f g := by simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The changed-value strict diagram recovers the entire localized diagram naturally. -/
def repairComparison : localized L ⟶ repair.{v} ⋙ L where
  app b := (valueIso L b).hom
  naturality {b c} f := by
    change ((valueIso L b).hom ≫ (valueIso L c).inv) ≫ (valueIso L c).hom =
      (valueIso L b).hom ≫ L.map (𝟙 point)
    rw [Category.assoc, Iso.inv_hom_id, L.map_id]

instance repairComparison_isIso : IsIso (repairComparison L) := by
  have : ∀ b, IsIso ((repairComparison L).app b) :=
    fun b => inferInstanceAs (IsIso (valueIso L b).hom)
  exact NatIso.isIso_of_isIso_app _

abbrev repairComparisonIso : localized L ≅ repair.{v} ⋙ L := asIso (repairComparison L)

end SerrePositivity.SimplicialModel.StrictValueObstruction
