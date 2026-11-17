module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraRelativeInput
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cofibrant 代数の厳密な二項余積

## 概要
HA §3.2.4.7 の導来余積のため、固定右因子との厳密な余積を模型で扱う。

## 方針
余積の射の四角形は pushout である。cofibration と trivial cofibration の保存から
Ken Brown の補題で cofibrant 入力間の弱同値を保存する。

## 規約
保存条件だけを述べ、固定右因子との余積が通常の左随伴であるとは仮定しない。

## 使われ方
CAlg の指定された余積関手と、テンソルとの自然比較の源。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity
open CategoryTheory Limits _root_.HomotopicalAlgebra

section Ordinary
variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

/-- The ordinary coproduct with a fixed right factor, with the specified coproduct maps. -/
def modelCoprodWith (B : C) : C ⥤ C where
  obj X := X ⨿ B
  map f := coprod.map f (𝟙 B)
  map_id _ := coprod.map_id_id
  map_comp f g := coprod.map_comp_id f g

variable [ModelCategory C]

/-- Fixed-factor coproducts preserve both Quillen cofibration classes. -/
instance modelCoprodWith_isLeftQuillen (B : C) :
    SerrePositivity.Quillen.IsLeftQuillen (modelCoprodWith B) where
  map_cofibrations := by
    intro X Y f hf
    change cofibrations C (coprod.map f (𝟙 B))
    exact (cofibrations C).of_isPushout (IsPushout.of_coprod_inl_with_id f B) hf
  map_trivialCofibrations := by
    intro X Y f hf
    change trivialCofibrations C (coprod.map f (𝟙 B))
    exact (trivialCofibrations C).of_isPushout (IsPushout.of_coprod_inl_with_id f B) hf

/-- Coproducts of cofibrant objects are cofibrant, for the actual specified inclusions. -/
lemma modelCoprodWith_cofibrant (X B : C) [IsCofibrant X] [IsCofibrant B] :
    IsCofibrant (X ⨿ B) :=
  isCofibrant_of_cofibration (coprod.inl : X ⟶ X ⨿ B)

/-- Fixed-factor coproducts preserve weak equivalences between cofibrant left inputs. -/
lemma modelCoprodWith_map_weakEquivalence (B : C) {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (coprod.map f (𝟙 B)) :=
  SerrePositivity.Quillen.map_weakEquivalence_of_cofibrant (modelCoprodWith B) f

end Ordinary

namespace BarrattEccles
variable (A : Type u) [CommRing A]

/-- The strict fixed-factor coproduct functor on the chosen cofibrant algebra input. -/
def cofibrantAlgebraCoprodWith (B : CofibrantAlgebra A) :
    CofibrantAlgebra A ⥤ CofibrantAlgebra A := by
  let := modelCategory A
  refine ObjectProperty.lift _
    (cofibrantAlgebraInclusion A ⋙ modelCoprodWith ((cofibrantAlgebraInclusion A).obj B)) ?_
  intro X
  have := cofibrantAlgebra_isCofibrant A X
  have := cofibrantAlgebra_isCofibrant A B
  exact modelCoprodWith_cofibrant _ _

end BarrattEccles
end SerrePositivity.EInfinity
