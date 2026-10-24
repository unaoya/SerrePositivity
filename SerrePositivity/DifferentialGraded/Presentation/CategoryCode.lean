module
public import SerrePositivity.DifferentialGraded.Presentation.ComplexCode
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.SetTheory.Cardinal.Ordinal
/-!
概要：κ の ordinal 初期区間と固定基底の商 Hom を持つ dg 圏の小さい提示型。
方針：Hom の複体コード・実単位・実合成と三法則を保持し、主 dg 圏に評価する。
規約：任意の dg 圏構造を大きい宇宙のフィールドとして保存しない。
使われ方：16時間試作の、出発圏・seed・延長ラベルを保持する厳密関手的模型。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u})

structure DGCategoryPresentationCode where
  ordinal : κ.ord.ToType
  hom : Set.Iio ordinal → Set.Iio ordinal → DGComplexPresentationCode R κ.ord.ToType
  unit : ∀ x, 𝟙_ (Complex R) ⟶ (hom x x).value R κ.ord.ToType
  comp : ∀ x y z, (hom x y).value R κ.ord.ToType ⊗ (hom y z).value R κ.ord.ToType ⟶
    (hom x z).value R κ.ord.ToType
  left : ∀ x y, (λ_ ((hom x y).value R κ.ord.ToType)).inv ≫ unit x ▷ _ ≫ comp x x y = 𝟙 _
  right : ∀ x y, (ρ_ ((hom x y).value R κ.ord.ToType)).inv ≫ _ ◁ unit y ≫ comp x y y = 𝟙 _
  assoc : ∀ w x y z, (α_ _ _ _).inv ≫ comp w x y ▷ _ ≫ comp w y z =
    _ ◁ comp x y z ≫ comp w x z

namespace DGCategoryPresentationCode

def Objects (c : DGCategoryPresentationCode R κ) : Type u := Set.Iio c.ordinal

instance enrichment (c : DGCategoryPresentationCode R κ) : DGCategory R (c.Objects R κ) :=
  ofHomObjects R _ (fun x y => (c.hom x y).value R κ.ord.ToType)
    c.unit c.comp c.left c.right c.assoc

lemma small : Small.{u} (DGCategoryPresentationCode R κ) := inferInstance

end DGCategoryPresentationCode
end SerrePositivity.DifferentialGraded
