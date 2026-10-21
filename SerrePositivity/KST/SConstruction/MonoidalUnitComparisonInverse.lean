module
public import Mathlib.CategoryTheory.Monoidal.Category

/-! # 元の単位比較の逆向きの可換性
概要：同型による元の単位比較から、同じ逆射に対する単位の式を回収する。
方針：元の単位射の単射性と同型の逆律を使う。
規約：単位比較の射を変更しない。使われ方：Serre 関手の oplax 単位則。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 元の左単位の順方向の式から、同じ逆比較の式を得る。 -/
lemma monoidalLeftUnitComparison_inverse {R Y : C} (e : R ≅ Y) (d : R ⟶ (𝟙_ C) ⊗ Y)
    (h : e.hom = d ≫ (λ_ Y).hom) : (λ_ Y).inv = e.inv ≫ d := by
  apply (cancel_mono (λ_ Y).hom).mp
  rw [Iso.inv_hom_id, Category.assoc, ← h, Iso.inv_hom_id]

/-- 元の右単位の順方向の式から、同じ逆比較の式を得る。 -/
lemma monoidalRightUnitComparison_inverse {R Y : C} (e : R ≅ Y) (d : R ⟶ Y ⊗ (𝟙_ C))
    (h : e.hom = d ≫ (ρ_ Y).hom) : (ρ_ Y).inv = e.inv ≫ d := by
  apply (cancel_mono (ρ_ Y).hom).mp
  rw [Iso.inv_hom_id, Category.assoc, ← h, Iso.inv_hom_id]

end SerrePositivity.KST.SConstruction
