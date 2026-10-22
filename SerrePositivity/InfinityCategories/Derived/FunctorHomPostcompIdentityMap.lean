module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra
/-!
概要：元の kernel 合成子の右変数自然性を、同じ通常比較と raw 経路で照合する。
方針：元の指定比較と射の値を保持し、全関手圏の実作用と可換四角形を使う。
規約：後続 kernel の平坦性・射の可逆性は要求しない。使われ方：模型変更の整合性。
-/
@[expose] public section
noncomputable section
universe w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHomPostcomp_identity {X Y Z : SSet.{w}} (f : X ⟶ Y) (q : Y ⟶ Z) :
    functorHomPostcomp f f q (𝟙 (HomotopyCategory.mk (functorVertex f))) =
      𝟙 (HomotopyCategory.mk (functorVertex (f ≫ q))) :=
  (SSet.mapHomotopyCategory ((ihom X).map q)).map_id _
end SerrePositivity.InfinityCategories
