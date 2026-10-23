module

public import SerrePositivity.InfinityCategories.F1.Diagrams.OverPullbackMorphism
public import SerrePositivity.InfinityCategories.F1B.KanPrecompositionSquareExtension

/-!
概要：底上の射とパラメータの制限による二つの逆像の可換四角形を pullback と同定する。
方針：逆像の射影の pullback を貼り合わせて打ち消す。
規約：二つの底上の射は任意。
使われ方：相対指数の制限の持ち上げ問題を二部分上の図式の貼り合わせに移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：固定底上の射の pullback の比較は元の射の底変換。
方針：元と標的の標準 pullback を横に打ち消す。
規約：パラメータ z は任意の底上の対象。
使われ方：元の射が単射なら逆像の比較も単射となる。 -/
lemma kanOverPullbackMap_isPullback {C : SSet.{u}} {K L : Over C} (i : K ⟶ L) (z : Over C) :
    IsPullback (overPullbackMap i z) (pullback.snd z.hom K.hom)
      (pullback.snd z.hom L.hom) i.left := by
  have h : IsPullback (overPullbackMap i z ≫ pullback.fst z.hom L.hom)
      (pullback.snd z.hom K.hom) z.hom (i.left ≫ L.hom) := by
    rw [overPullbackMap_fst, i.w]
    exact IsPullback.of_hasPullback _ _
  exact h.of_right (overPullbackMap_snd i z) (IsPullback.of_hasPullback _ _)

/-- 概要：単射な底上の射は任意の逆像の比較で単射を誘導する。
方針：比較の pullback 表示を使う。
規約：元の射の単射性は左成分について課す。
使われ方：二部分を貼り合わせた包含の単射性。 -/
instance kanOverPullbackMap_mono {C : SSet.{u}} {K L : Over C} (i : K ⟶ L) [Mono i.left]
    (z : Over C) : Mono (overPullbackMap i z) :=
  (kanOverPullbackMap_isPullback i z).mono_fst_of_mono

/-- 概要：底上の射の比較のパラメータに関する自然性の四角形は pullback。
方針：両側の逆像の第一射影の pullback 表示を縦に打ち消す。
規約：比較射の単射性は不要。
使われ方：ホーンの逆像と制限先の逆像の交わりの指定。 -/
lemma kanOverPullbackMap_naturality_isPullback {C : SSet.{u}} {K L A B : Over C}
    (i : K ⟶ L) (u : A ⟶ B) :
    IsPullback ((overPullbackUnderlying K.hom).map u) (overPullbackMap i A)
      (overPullbackMap i B) ((overPullbackUnderlying L.hom).map u) := by
  have h : IsPullback ((overPullbackUnderlying K.hom).map u)
      (overPullbackMap i A ≫ pullback.fst A.hom L.hom)
      (overPullbackMap i B ≫ pullback.fst B.hom L.hom) u.left := by
    rw [overPullbackMap_fst, overPullbackMap_fst]
    exact overPullbackProjection_isPullback K.hom u
  exact h.of_bot (overPullbackMap_naturality i u) (overPullbackProjection_isPullback L.hom u)

end SerrePositivity.InfinityCategories.F1B
