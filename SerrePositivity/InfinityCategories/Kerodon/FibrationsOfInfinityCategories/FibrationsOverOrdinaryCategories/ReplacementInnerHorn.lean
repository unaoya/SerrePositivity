module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ReplacementInitialSubcomplex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTail
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
概要：有限鎖上の replacement の内ホーンの逆像は inner anodyne。
方針：零から始まらない全単体を内ホーンが含むことを使い、係数との直積の pushout として付加する。
規約：係数の充填性は不要で、モデル構造も使わない。
使われ方：Kerodon Lemma 5.3.6.3（Tag 025A）、left fibration の平坦性の strict な模型。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：始対象以外から始まる単体を含む inner anodyne な部分底の逆像は inner anodyne。
方針：始対象の係数との直積の inner anodyne 性を pushout で移す。
規約：図式は任意の単体集合値。
使われ方：内ホーンの逆像のセル付加。 -/
lemma replacementInitialSubcomplex_innerAnodyne {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c : C} (hc : IsInitial c) (A : (nerve C).Subcomplex)
    (hA : ∀ (d : SimplexCategoryᵒᵖ) (σ : (nerve C).obj d), σ.obj 0 ≠ c → σ ∈ A.obj d)
    (hi : innerAnodyneExtensions A.ι) :
    innerAnodyneExtensions (A.preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).ι :=
  MorphismProperty.of_isPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementInitialSubcomplex_isPushout F hc A hA)
    (hi.whiskerRight (F.obj c))

/-- 概要：有限鎖の nerve に表示した内ホーン。
方針：標準単体と有限鎖の nerve の同型で逆像を取る。
規約：周囲の底は universe u の有限鎖。
使われ方：replacement の内ホーンの逆像の幾何学。 -/
def replacementNerveHorn (n : ℕ) (k : Fin (n + 1)) :
    (nerve (ULift.{u} (Fin (n + 1)))).Subcomplex :=
  (horn n k).preimage (stdSimplex.isoNerve n).inv

/-- 概要：先頭を欠かないホーンは零以外から始まる有限鎖の単体を全て含む。
方針：その単体は零頂点を避けることを単調性から示す。
規約：最後のホーンでも成立し、k が正であることだけを使う。
使われ方：内ホーンに対する replacement の pushout 被覆条件。 -/
lemma replacementNerveHorn_contains_noninitial (n : ℕ) (k : Fin (n + 1)) (h0 : 0 < k)
    (d : SimplexCategoryᵒᵖ) (σ : (nerve (ULift.{u} (Fin (n + 1)))).obj d)
    (hs : σ.obj 0 ≠ ULift.up 0) : σ ∈ (replacementNerveHorn n k).obj d := by
  rcases d with ⟨⟨d⟩⟩
  apply (mem_horn_iff_notMem_range _ k).2
  refine ⟨0, (ne_of_gt h0).symm, ?_⟩
  rintro ⟨i, hi⟩
  change (σ.obj i).down = 0 at hi
  have h : σ.obj 0 ≤ σ.obj i := leOfHom (σ.map (homOfLE (Fin.zero_le i)))
  change (σ.obj 0).down ≤ (σ.obj i).down at h
  rw [hi] at h
  exact hs (ULift.ext (le_antisymm h (Fin.zero_le _)))

/-- 概要：有限鎖の nerve 上に移した内ホーンの包含も inner anodyne。
方針：部分複体の逆像同型で元のホーン包含へ移す。
規約：両端を同型で変更しているだけである。
使われ方：replacement の逆像へ inner anodyne 性を移す。 -/
lemma replacementNerveHorn_innerAnodyne (n : ℕ) (k : Fin (n + 1))
    (h0 : 0 < k) (hn : k < Fin.last n) :
    innerAnodyneExtensions (replacementNerveHorn.{u} n k).ι := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso (horn n k) (stdSimplex.isoNerve.{u} n).symm
  exact (innerAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk e (stdSimplex.isoNerve n).symm (by rfl))).2
      (innerAnodyneExtensions.horn_ι h0 hn)

/-- 概要：有限鎖上の任意の replacement の内ホーンの逆像の包含は inner anodyne。
方針：内ホーンを含む部分と始対象の係数部分の pushout 分解を使う。
規約：係数の Kan 性や矢の同値性を要求しない。
使われ方：Kerodon Lemma 5.3.6.3（Tag 025A） (2)、left fibration の平坦性への入力。 -/
lemma replacementNerveHorn_preimage_innerAnodyne (n : ℕ) (k : Fin (n + 1))
    (h0 : 0 < k) (hn : k < Fin.last n) (F : ULift.{u} (Fin (n + 1)) ⥤ SSet.{u}) :
    innerAnodyneExtensions
      ((replacementNerveHorn n k).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).ι :=
  replacementInitialSubcomplex_innerAnodyne F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial n)
    (replacementNerveHorn n k) (replacementNerveHorn_contains_noninitial n k h0)
    (replacementNerveHorn_innerAnodyne n k h0 hn)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
