module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstFiberErasure
public import SerrePositivity.EInfinity.Hammock.UnmarkedColumnCutSquare
public import SerrePositivity.EInfinity.SimplicialLocalization.UnmarkedFirstCutPrefix

/-!
# 元の語の圧縮による最初の非指定生成矢の保持

概要：最小非指定列とその像の切断は、同じ元の Total 生成矢を持つ。
方針：元の列の文字列が像の文字列の接頭列であることと切断の消去式を使う。
規約：元の自由圏の生成射を保持し、像の後置部分に条件を置かない。
使われ方：prefix と残りの全語への整合と積分解。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} (f : a ⟶ b) (S : Zigzag W.paths a X Y)
  (h : ∃ i, column W S i ≠ [])

lemma firstFiber_generator
    (P : FirstCut W (S.arrow (firstColumn W S h)))
    (Q : FirstCut W ((WordAction.obj f S).arrow (f.orderHom (firstColumn W S h)))) :
    (⟨Q.source, Q.target, Q.arrow⟩ : Quiver.Total C) = ⟨P.source, P.target, P.arrow⟩ := by
  obtain ⟨tail, ht⟩ := firstFiber_erasure_prefix W f S h
  exact firstCut_generator_of_erasure_prefix W Q P tail ht

lemma firstFiber_columnFirstCut :
    let P := columnFirstCut W S (firstColumn W S h) (firstColumn_nonempty W S h)
    let Q := columnFirstCut W (WordAction.obj f S) (f.orderHom (firstColumn W S h))
      (column_wordAction_nonempty W f S _ (firstColumn_nonempty W S h))
    (⟨Q.source, Q.target, Q.arrow⟩ : Quiver.Total C) = ⟨P.source, P.target, P.arrow⟩ :=
  firstFiber_generator W f S h _ _

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
