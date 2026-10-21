module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverWordNaturality
public import SerrePositivity.EInfinity.Hammock.WordComposition

/-!
# 元の値の fiber の全語の作用の単位と合成

概要：元の全部分圏への制限も厳密な語の作用の単位と合成を保つ。
方針：元の包含による関手の照合を元の語の作用の法則へ戻す。
規約：全部分圏の対象と全射の一致を使う。
使われ方：元の全語の圏値図式。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {Y : Paths Q}
  {β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y}

lemma valueFiberFunctor_ext {D : Type u'} [Category.{v'} D] {w : Word}
    (F G : D ⥤ ZigzagValueFiber A w Y β)
    (h : F ⋙ (zigzagValueProperty A w Y β).ι = G ⋙ (zigzagValueProperty A w Y β).ι) : F = G := by
  have ho : ∀ d, F.obj d = G.obj d := fun d =>
    ObjectProperty.FullSubcategory.ext (CategoryTheory.Functor.congr_obj h d)
  apply CategoryTheory.Functor.hext (F := F) (G := G) ho
  intro d e f
  exact valueFiber_hom_hext A (ho d) (ho e) (F.map f) (G.map f)
    (CategoryTheory.Functor.hcongr_hom h f)

lemma zigzagFiberWordAction_id (w : Word) :
    zigzagFiberWordAction A Y β (𝟙 w) = 𝟭 (ZigzagValueFiber A w Y β) := by
  apply valueFiberFunctor_ext A
  rw [zigzagFiberWordAction_inclusion, WordAction.functor_id,
    CategoryTheory.Functor.comp_id, CategoryTheory.Functor.id_comp]

lemma zigzagFiberWordAction_comp {a b c : Word} (f : a ⟶ b) (g : b ⟶ c) :
    zigzagFiberWordAction A Y β (f ≫ g) =
      zigzagFiberWordAction A Y β f ⋙ zigzagFiberWordAction A Y β g := by
  apply valueFiberFunctor_ext A
  calc
    _ = (zigzagValueProperty A a Y β).ι ⋙ WordAction.functor (f ≫ g) :=
      zigzagFiberWordAction_inclusion A Y β _
    _ = ((zigzagValueProperty A a Y β).ι ⋙ WordAction.functor f) ⋙
        WordAction.functor g := by rw [WordAction.functor_comp]; rfl
    _ = (zigzagFiberWordAction A Y β f ⋙ (zigzagValueProperty A b Y β).ι) ⋙
        WordAction.functor g := by rw [zigzagFiberWordAction_inclusion]
    _ = zigzagFiberWordAction A Y β f ⋙
        ((zigzagValueProperty A b Y β).ι ⋙ WordAction.functor g) := rfl
    _ = zigzagFiberWordAction A Y β f ⋙
        (zigzagFiberWordAction A Y β g ⋙ (zigzagValueProperty A c Y β).ι) := by
      rw [zigzagFiberWordAction_inclusion]
    _ = _ := rfl

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
