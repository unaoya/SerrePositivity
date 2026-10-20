module

public import SerrePositivity.EInfinity.Hammock.RawHammock

/-!
# 元の未縮約 hammock の単体集合と余極限への元の射

概要：元の全語を保持する未縮約 hammock の全作用素を単体集合へ束ねる。
方針：各語の graph の元の全作用素と、同じ標準射を使う。
規約：縮約の選択や代表の一意性は仮定しない。
使われ方：縮約写像の全作用素での整合と余極限の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.RawHammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C)

/-- 元の全語の全単体を保持する未縮約 hammock の単体集合。 -/
def simplicialSet : SSet.{max u v} where
  obj n := RawHammock W X Y n
  map α := ↾fun r => map W X Y α r
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro r
    change (⟨r.1, (graph W r.1 X Y).map (𝟙 n) r.2⟩ : RawHammock W X Y n) = r
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro r
    change (⟨r.1, (graph W r.1 X Y).map (α ≫ β) r.2⟩ : RawHammock W X Y _) =
      ⟨r.1, (graph W r.1 X Y).map β ((graph W r.1 X Y).map α r.2)⟩
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- 元の語の同じ標準射からなる、元の余極限への単体的射。 -/
def augmentation : simplicialSet W X Y ⟶ colimitGraph W X Y where
  app _ := ↾fun r => value W X Y r
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro r
    exact value_map W X Y α r

lemma augmentation_app (n : SimplexCategoryᵒᵖ) (r : RawHammock W X Y n) :
    (augmentation W X Y).app n r = (graphInclusion W X Y r.1).app n r.2 := rfl

end SerrePositivity.EInfinity.Hammock.RawHammock
