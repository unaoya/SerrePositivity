module
public import SerrePositivity.DifferentialGraded.Presentation.CategoryCode
/-!
概要：固定基底の Hom 提示を任意の小さい対象型上に配置した圏データを保持する。
方針：元の提示コードと同じ単位・合成・三法則を保持し、対象の再添字と分離する。
規約：任意の Hom 複体や dg 圏構造を大きい宇宙のフィールドへ保存しない。
使われ方：二項・可算個の出発提示を非連結和へまとめる前の中間データ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (B X : Type u)

structure DGCategoryPresentationData where
  hom : X → X → DGComplexPresentationCode R B
  unit : ∀ x, 𝟙_ (Complex R) ⟶ (hom x x).value R B
  comp : ∀ x y z, (hom x y).value R B ⊗ (hom y z).value R B ⟶ (hom x z).value R B
  left : ∀ x y, (λ_ ((hom x y).value R B)).inv ≫ unit x ▷ _ ≫ comp x x y = 𝟙 _
  right : ∀ x y, (ρ_ ((hom x y).value R B)).inv ≫ _ ◁ unit y ≫ comp x y y = 𝟙 _
  assoc : ∀ w x y z, (α_ _ _ _).inv ≫ comp w x y ▷ _ ≫ comp w y z =
    _ ◁ comp x y z ≫ comp w x z

namespace DGCategoryPresentationData

@[instance_reducible] def enrichment (c : DGCategoryPresentationData R B X) : DGCategory R X :=
  ofHomObjects R X (fun x y => (c.hom x y).value R B)
    c.unit c.comp c.left c.right c.assoc

lemma small : Small.{u} (DGCategoryPresentationData R B X) := inferInstance

end DGCategoryPresentationData

namespace DGCategoryPresentationCode
variable (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)

def toData : DGCategoryPresentationData R κ.ord.ToType (c.Objects R κ) where
  hom := c.hom
  unit := c.unit
  comp := c.comp
  left := c.left
  right := c.right
  assoc := c.assoc

end DGCategoryPresentationCode
end SerrePositivity.DifferentialGraded
