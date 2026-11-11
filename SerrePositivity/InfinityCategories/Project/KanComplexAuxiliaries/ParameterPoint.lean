module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
概要：二変数の作用の最初の変数を点で固定するパラメータ族。
方針：左単位子と点の左テンソルを用い、テンソル交換で自然性を確認する。
規約：一般のモノイダル圏の射。使われ方：Hom end の普遍点に対する前合成の族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.ParameterPoint
end SerrePositivity.KST.Spectra.ParameterPoint
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.ParameterPoint
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 単位からの点で左のパラメータを固定する射。 -/
def family {E : C} (p : 𝟙_ C ⟶ E) (A : C) : A ⟶ E ⊗ A :=
  (λ_ A).inv ≫ p ▷ A
/-- 点と自由パラメータの射による同時の移送は、点を固定した族と可換。 -/
@[reassoc]
lemma naturality {E E' A A' : C} (p : 𝟙_ C ⟶ E) (e : E ⟶ E') (a : A ⟶ A') :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family p A ≫ (e ⊗ₘ a) = a ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family (p ≫ e) A' := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family, tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc, ← whisker_exchange, leftUnitor_inv_naturality_assoc]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ParameterPoint.family := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ParameterPoint.naturality := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ParameterPoint.naturality_assoc := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.naturality_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.ParameterPoint.family.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.family.eq_1
