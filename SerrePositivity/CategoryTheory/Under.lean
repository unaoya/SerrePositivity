module

public import Mathlib.CategoryTheory.LiftingProperties.Over
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Under

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Under` を直接 import する。
-/

/-! ## Under（旧 SerrePositivity/CategoryTheory/LiftingProperties/Under.lean） -/

/-!
# Lifting properties in under categories

Dual of the Over construction in the pinned Mathlib
`CategoryTheory/LiftingProperties/Over.lean` (Joël Riou, Apache 2.0).
-/

@[expose] public section Under
universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {S : C}

/-- A lift of the underlying square gives a lift in `Under S`. -/
lemma CommSq.HasLift.under {X₁ X₂ X₃ X₄ : Under S}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    {sq : CommSq t l r b}
    [CommSq.HasLift (f := t.right) (i := l.right) (p := r.right) (g := b.right)
      (sq.map (Under.forget S))] : sq.HasLift := by
  let sq' := sq.map (Under.forget S)
  dsimp at sq'
  exact ⟨⟨{
    l := Under.homMk sq'.lift
      (by rw [← Under.w l, Category.assoc, sq'.fac_left, Under.w t])
  }⟩⟩

/-- An underlying lifting property suffices for the lifting property in
the under category. It is not asserted to be necessary. -/
lemma HasLiftingProperty.under {A B X Y : Under S} (i : A ⟶ B) (p : X ⟶ Y)
    [HasLiftingProperty i.right p.right] : HasLiftingProperty i p :=
  ⟨fun _ ↦ .under⟩

end CategoryTheory

end Under

/-! ## UnderFactorization（旧 SerrePositivity/CategoryTheory/MorphismProperty/UnderFactorization.lean） -/

/-!
# Factorizations in under categories

This is the dual of `MorphismProperty.HasFactorization.over` in the pinned
Mathlib `CategoryTheory/MorphismProperty/Comma.lean` (Joël Riou, Apache 2.0).
The factorization data itself is Mathlib's existing `MapFactorizationData`.
-/

@[expose] public section UnderFactorization
universe u v

open CategoryTheory

namespace CategoryTheory.MorphismProperty

/-- Lift a specified factorization of the underlying arrow to `Under S`.
The map from `S` to the intermediate object is the first factor composed
with the structure map of the source. -/
def MapFactorizationData.under {C : Type u} [Category.{v} C]
    {W₁ W₂ : MorphismProperty C} {S : C} {X Y : CategoryTheory.Under S}
    {f : X ⟶ Y} (hf : MapFactorizationData W₁ W₂ f.right) :
    MapFactorizationData W₁.under W₂.under f where
  Z := CategoryTheory.Under.mk (X.hom ≫ hf.i)
  i := CategoryTheory.Under.homMk hf.i
  p := CategoryTheory.Under.homMk hf.p (by simp [CategoryTheory.Under.w f])
  fac := by ext; exact hf.fac
  hi := hf.hi
  hp := hf.hp

/-- Factorizations of any two morphism classes induce factorizations in
the under category, without any model-category hypothesis. -/
instance HasFactorization.under {C : Type u} [Category.{v} C]
    (W₁ W₂ : MorphismProperty C) [W₁.HasFactorization W₂] (S : C) :
    (W₁.under (X := S)).HasFactorization W₂.under where
  nonempty_mapFactorizationData f :=
    ⟨(factorizationData W₁ W₂ f.right).under⟩

end CategoryTheory.MorphismProperty

end UnderFactorization
