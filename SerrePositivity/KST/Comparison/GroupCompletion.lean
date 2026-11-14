module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.DGAlgebra
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 単体的モノイドの bar 分類空間

概要：群状単体的モノイドの bar 分類空間を二重単体的 nerve の対角として構成する。
方針：各次数のモノイドを一対象圏へ送り、nerve を取って対角に制限する。
規約：Segal 1974 Proposition 1.5 の入力。群完備化定理そのものはまだ含まない。
使われ方：KST Lemma 2.13 の BĜL と、plus 構成の定義域。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：単体的モノイドの各次数で一対象圏の nerve を取る。
方針：Mathlib の MonCat.toCat と nerveFunctor を合成する。
規約：KST Lemma 2.13、Segal 1974 Proposition 1.5 の二重単体的 bar。
使われ方：分類空間の対角模型。
-/
def bisimplicialBar (M : SimplicialObject MonCat.{u}) : SimplicialObject SSet.{u} :=
  M ⋙ MonCat.toCat ⋙ nerveFunctor

/--
概要：単体的モノイドの bar 分類空間 B M。
方針：二重単体的 bar の二つの単体次数を対角に制限する。
規約：群であることを要求しない。KST Lemma 2.13 の BĜL の模型。
使われ方：群状モノイドの delooping と群完備化。
-/
def monoidBar (M : SimplicialObject MonCat.{u}) : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (bisimplicialBar M)

/--
概要：単体的モノイドの射から bar 分類空間の射を作る。
方針：一対象圏の nerve による自然変換を対角に制限する。
規約：全ての面・退化との自然性を保持する。Segal 1974 Proposition 1.5。
使われ方：KST Lemma 2.13 の比較写像の自然性。
-/
def monoidBarMap {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N) :
    monoidBar M ⟶ monoidBar N :=
  Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
    (Functor.uncurry.map (Functor.whiskerRight f (MonCat.toCat ⋙ nerveFunctor)))

/--
概要：bar への作用は恒等射を保つ。
方針：whiskering と uncurry の恒等射の保存を使う。
規約：KST Lemma 2.13 の関手性。
使われ方：bar 分類空間の関手。
-/
@[simp] theorem monoidBarMap_id (M : SimplicialObject MonCat.{u}) :
    monoidBarMap (𝟙 M) = 𝟙 (monoidBar M) := by
  simp only [monoidBarMap, bisimplicialBar, monoidBar, Functor.whiskerRight_id']
  rw [Functor.uncurry.map_id]
  rfl

/--
概要：bar への作用は合成を保つ。
方針：whiskering と uncurry の合成の保存を使う。
規約：KST Lemma 2.13 の関手性。
使われ方：群完備化写像の自然性。
-/
theorem monoidBarMap_comp {M N P : SimplicialObject MonCat.{u}} (f : M ⟶ N) (g : N ⟶ P) :
    monoidBarMap (f ≫ g) = monoidBarMap f ≫ monoidBarMap g := by
  simp [monoidBarMap]

/--
概要：bar 分類空間の唯一の零次単体を基点に取る。
方針：一対象圏の唯一の対象から長さ零の composable arrows を作る。
規約：KST Lemma 2.13 の連結分類空間の基点。
使われ方：BĜL のホモトピー群。
-/
def monoidBarBasepoint (M : SimplicialObject MonCat.{u}) : (monoidBar M) _⦋0⦌ :=
  ComposableArrows.mk₀ (SingleObj.star (M.obj (op ⦋0⦌)))

/--
概要：bar 分類空間は零次単体を一つだけ持つ。
方針：一対象圏の唯一の対象で長さ零の図式を決める。
規約：モノイドの群状性は不要。KST Lemma 2.13 の連結性の前段。
使われ方：分類空間の連結性。
-/
instance monoidBarVertexSubsingleton (M : SimplicialObject MonCat.{u}) :
    Subsingleton ((monoidBar M) _⦋0⦌) where
  allEq a b := by
    apply ComposableArrows.ext₀
    change (a.obj 0 : SingleObj (M.obj (op ⦋0⦌))) = b.obj 0
    exact Quiver.SingleObj.ext (α := M.obj (op ⦋0⦌))

/--
概要：任意の単体的モノイドの bar 分類空間は連結である。
方針：全ての成分が唯一の零次単体で代表される。
規約：KST Lemma 2.13、Segal 1974 Proposition 1.5。
使われ方：plus 構成の連結な入力と分類空間の π₁ の比較。
-/
instance monoidBarConnected (M : SimplicialObject MonCat.{u}) : (monoidBar M).IsConnected where
  allEq a b := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => exact congrArg π₀.mk (Subsingleton.elim _ _)
  nonempty := ⟨monoidBarBasepoint M⟩

/--
概要：単体的環 A の ĜL_r の bar 分類空間。
方針：π₀ で可逆な行列の単体的モノイドに bar を適用する。
規約：KST 式 (2.2) と Lemma 2.13。rank の安定化前の模型。
使われ方：安定 BĜL とその plus 構成の構成要素。
-/
def hatGLBar (A : SimplicialObject RingCat.{u}) (r : ℕ) : SSet.{u} :=
  monoidBar (hatGLMonoidObject A r)

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.2.6.14" (partial := component) "仮定：離散群 G を定数単体的モノイドとして与える（HA と一致する離散群）。結論：各次数の一対象圏の nerve の対角とその唯一の零単体を使うので、通常の BG とその基点を得る（原典の通常の分類空間という対象の構成に一致）。HA の E₁ 代数の普遍的 Bar との比較宣言は含まれない。"] _root_.SerrePositivity.KST.Comparison.monoidBar
attribute [cite HA "5.2.6.14" (partial := component) "仮定：離散群 G を定数単体的モノイドとして与える（HA と一致する離散群）。結論：各次数の一対象圏の nerve の対角とその唯一の零単体を使うので、通常の BG とその基点を得る（原典の通常の分類空間という対象の構成に一致）。HA の E₁ 代数の普遍的 Bar との比較宣言は含まれない。"] _root_.SerrePositivity.KST.Comparison.monoidBarBasepoint
