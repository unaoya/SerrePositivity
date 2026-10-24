module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.NatTransWhiskering
public import SerrePositivity.InfinityCategories.F1B.KanExtension.UniversalProperty

/-!
概要：nerve の左右 Kan の Hom 比較写像を通常の自然変換で表示する。
方針：自然変換の垂直合成と左 whiskering の保存を使う。
規約：元の指定変換を保つ式。
使われ方：B5 の Kan の大域的普遍性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：左 Kan の比較写像は通常の指定単位の合成を表す。
方針：左 whiskering と垂直合成の保存を使う。
規約：同じ指定単位で比較する。
使われ方：比較写像の全単射性の移送。 -/
lemma nerve_leftKanHomMap {K C D : Type u}
    [Category.{u} K] [Category.{u} C] [Category.{u} D]
    (L : K ⥤ C) {F₀ : K ⥤ D} {F G : C ⥤ D} (β : F₀ ⟶ L ⋙ F) (η : F ⟶ G) :
    leftKanHomMap (F₀ := nerveMap F₀) (F := nerveMap F) (nerveMap L)
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHom (F := F₀) (G := L ⋙ F) β) (nerveMap G)
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHom (F := F) (G := G) η) =
        SerrePositivity.InfinityCategories.F1B.nerveNatTransHom (F := F₀) (G := L ⋙ G) (β ≫ Functor.whiskerLeft L η) := by
  dsimp only [leftKanHomMap]
  rw [SerrePositivity.InfinityCategories.F1B.nerveNatTransHom_whiskerLeft, ← SerrePositivity.InfinityCategories.F1B.nerveNatTransHom_comp]

/-- 概要：右 Kan の比較写像は通常の指定余単位の合成を表す。
方針：前合成の表示と垂直合成の保存を使う。
規約：順序は前合成した射の後に余単位。
使われ方：右 Kan の大域的普遍性の移送。 -/
lemma nerve_rightKanHomMap {K C D : Type u}
    [Category.{u} K] [Category.{u} C] [Category.{u} D]
    (L : K ⥤ C) {F₀ : K ⥤ D} {F G : C ⥤ D} (α : L ⋙ F ⟶ F₀) (η : G ⟶ F) :
    rightKanHomMap (F₀ := nerveMap F₀) (F := nerveMap F) (nerveMap L)
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHom (F := L ⋙ F) (G := F₀) α) (nerveMap G)
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHom (F := G) (G := F) η) =
        SerrePositivity.InfinityCategories.F1B.nerveNatTransHom (F := L ⋙ G) (G := F₀) (Functor.whiskerLeft L η ≫ α) := by
  dsimp only [rightKanHomMap]
  rw [SerrePositivity.InfinityCategories.F1B.nerveNatTransHom_whiskerLeft, ← SerrePositivity.InfinityCategories.F1B.nerveNatTransHom_comp]

end SerrePositivity.InfinityCategories.F1B
