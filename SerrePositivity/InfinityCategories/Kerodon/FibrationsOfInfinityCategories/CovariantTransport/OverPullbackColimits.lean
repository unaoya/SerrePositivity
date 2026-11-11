module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.SSetPullbackColimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：固定した底上の単体集合への pullback の単射と余極限の保存。
方針：標準の Over.pullback の第一射影の正方形を pullback と表示し、次数ごとの余極限の定理を使う。
規約：単体の宇宙で小さい通常の図式を扱う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底の各単体への pullback による比較判定。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：固定した底上の対象に沿う pullback の基礎の単体集合の関手。
方針：Over.pullback の後で構造射を忘れる。
規約：対象 a の像は pullback a.hom p。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底の図式の各対象上の比較。 -/
noncomputable def overPullbackUnderlying {M S : SSet.{u}} (p : M ⟶ S) : Over S ⥤ SSet.{u} :=
  Over.pullback p ⋙ Over.forget M

/-- 概要：pullback の誘導射は第一射影と可換。
方針：標準の pullback の持ち上げの第一射影を計算する。
規約：第一成分は可変の底上の対象。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、pullback の自然な射影。 -/
lemma overPullbackUnderlying_map_fst {M S : SSet.{u}} (p : M ⟶ S)
    {a b : Over S} (u : a ⟶ b) :
    (overPullbackUnderlying p).map u ≫ pullback.fst b.hom p = pullback.fst a.hom p ≫ u.left := by
  exact pullback.lift_fst _ _ _

/-- 概要：pullback の誘導射は固定した対象への第二射影を保つ。
方針：標準の pullback の持ち上げの第二射影を計算する。
規約：固定した対象 M への射は変えない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、射影の正方形の pullback 性。 -/
lemma overPullbackUnderlying_map_snd {M S : SSet.{u}} (p : M ⟶ S)
    {a b : Over S} (u : a ⟶ b) :
    (overPullbackUnderlying p).map u ≫ pullback.snd b.hom p = pullback.snd a.hom p := by
  exact pullback.lift_snd _ _ _

/-- 概要：pullback の第一射影は基礎の対象への自然変換。
方針：誘導射の第一射影の式を使う。
規約：終域は Over の忘却関手。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底の余極限の pullback。 -/
noncomputable def overPullbackProjection {M S : SSet.{u}} (p : M ⟶ S) :
    overPullbackUnderlying p ⟶ Over.forget S where
  app a := pullback.fst a.hom p
  naturality _ _ u := overPullbackUnderlying_map_fst p u

/-- 概要：pullback 関手の第一射影の自然性の正方形は pullback。
方針：固定した対象への第二射影の二つの pullback を貼り合わせて打ち消す。
規約：底上の射 u は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、pullback の単射および余極限の保存。 -/
lemma overPullbackProjection_isPullback {M S : SSet.{u}} (p : M ⟶ S)
    {a b : Over S} (u : a ⟶ b) :
    IsPullback ((overPullbackUnderlying p).map u) (pullback.fst a.hom p)
      (pullback.fst b.hom p) u.left := by
  have hp : IsPullback ((overPullbackUnderlying p).map u ≫ pullback.snd b.hom p)
      (pullback.fst a.hom p) p (u.left ≫ b.hom) := by
    rw [overPullbackUnderlying_map_snd, u.w]
    exact (IsPullback.of_hasPullback a.hom p).flip
  exact hp.of_right (overPullbackUnderlying_map_fst p u) (IsPullback.of_hasPullback b.hom p).flip

/-- 概要：固定した対象への pullback は単射を保つ。
方針：自然な第一射影の正方形の pullback 性を使う。
規約：射の単射性は Over 圏での単射性。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底のセルと骨格の比較の条件。 -/
instance overPullbackUnderlying_preservesMonomorphisms {M S : SSet.{u}} (p : M ⟶ S) :
    (overPullbackUnderlying p).PreservesMonomorphisms where
  preserves u _ := (overPullbackProjection_isPullback p u).mono_fst_of_mono

/-- 概要：固定した対象への pullback は小さい余極限 cocone を保つ。
方針：忘却後の底の余極限の各脚を pullback した cocone として表示する。
規約：形の連結性は要求しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、各単体での比較から全体への貼り合わせ。 -/
noncomputable def overPullbackUnderlying_isColimit {M S : SSet.{u}} (p : M ⟶ S)
    {J : Type v} [Category.{w} J] [Small.{u} J] {D : J ⥤ Over S}
    (c : Cocone D) (hc : IsColimit c) : IsColimit ((overPullbackUnderlying p).mapCocone c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.sset_isColimit_of_pullback ((Over.forget S).mapCocone c)
    (isColimitOfPreserves (Over.forget S) hc) ((overPullbackUnderlying p).mapCocone c)
    (Functor.whiskerLeft D (overPullbackProjection p)) ((overPullbackProjection p).app c.pt)
  intro j
  exact overPullbackProjection_isPullback p (c.ι.app j)

/-- 概要：固定した対象への pullback の基礎の関手は小さい余極限を保つ。
方針：任意の余極限 cocone の pullback の表示を使う。
規約：単体の宇宙 u で小さい添字を許す。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルの族と骨格列の局所比較判定。 -/
instance overPullbackUnderlying_preservesColimitsOfShape {M S : SSet.{u}} (p : M ⟶ S)
    (J : Type v) [Category.{w} J] [Small.{u} J] :
    PreservesColimitsOfShape J (overPullbackUnderlying p) where
  preservesColimit := { preserves := fun hc ↦ ⟨overPullbackUnderlying_isColimit p _ hc⟩ }

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
