module

public import SerrePositivity.EInfinity.Hammock.NormalForm
public import SerrePositivity.EInfinity.Hammock.RawSimplicialSet

/-!
# 元の縮約済み hammock の単体集合

概要：元の縮約済み対象に全作用素を作用させて再縮約し、単体集合を構成する。
方針：基本縮約の作用素による保存と正規形の一意性で恒等・合成を証明する。
規約：元の全語の余極限との同型は後続。全作用素で再縮約を行う。
使われ方：全語の余錐からの正規化と縮約 hammock の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C)

/-- 元の語と全射列を持つ、縮約済みの対象の単体集合。 -/
def reducedSimplicialSet : SSet.{max u v} where
  obj n := {r : RawHammock W X Y n // RawHammock.IsReduced W X Y r}
  map α := ↾fun r => ⟨normalForm W X Y _ (RawHammock.map W X Y α r.val),
    normalForm_reduced W X Y _ _⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro r
    apply Subtype.ext
    change normalForm W X Y n
      (⟨r.val.1, (graph W r.val.1 X Y).map (𝟙 n) r.val.2⟩ : RawHammock W X Y n) = r.val
    rw [CategoryTheory.Functor.map_id]
    exact normalForm_eq_self W X Y n r.property
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro r
    apply Subtype.ext
    change normalForm W X Y _ (RawHammock.map W X Y (α ≫ β) r.val) =
      normalForm W X Y _ (RawHammock.map W X Y β
        (normalForm W X Y _ (RawHammock.map W X Y α r.val)))
    rw [normalForm_map_normalForm]
    apply congrArg (normalForm W X Y _)
    dsimp only [RawHammock.map]
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- 元の全単体の有限縮約による正規化。 -/
def normalization : RawHammock.simplicialSet W X Y ⟶ reducedSimplicialSet W X Y where
  app n := ↾fun r => ⟨normalForm W X Y n r, normalForm_reduced W X Y n r⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro r
    apply Subtype.ext
    exact (normalForm_map_normalForm W X Y n α r).symm

lemma normalization_app (n : SimplexCategoryᵒᵖ) (r : RawHammock W X Y n) :
    ((normalization W X Y).app n r).val = normalForm W X Y n r := rfl

/-- 縮約済みの元の対象から、同じ全語の余極限への標準射。 -/
def reducedAugmentation : reducedSimplicialSet W X Y ⟶ colimitGraph W X Y where
  app _ := ↾fun r => RawHammock.value W X Y r.val
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro r
    change RawHammock.value W X Y
      (normalForm W X Y m (RawHammock.map W X Y α r.val)) =
      (colimitGraph W X Y).map α (RawHammock.value W X Y r.val)
    rw [normalForm_value]
    exact RawHammock.value_map W X Y α r.val

lemma normalization_augmentation :
    normalization W X Y ≫ reducedAugmentation W X Y = RawHammock.augmentation W X Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro r
  exact normalForm_value W X Y n r

end SerrePositivity.EInfinity.Hammock
