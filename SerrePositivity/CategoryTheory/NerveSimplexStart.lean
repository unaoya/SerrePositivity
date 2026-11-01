module

public import SerrePositivity.CategoryTheory.NerveSimplexEndpoint

/-!
# nerveの単体圏から先頭頂点を反変に評価する関手を構成する

## 概要
nerveの単体圏から先頭頂点を反変に評価する関手を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
単体を表す合成可能射列の先頭または終端を評価する。
単体圏の射と射列の制限を照合し、関手の法則とaugmentationの式を確認する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0016][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../formalization-plans/archive/k-theory-generalization-inventory.md#m0016
[plan]: ../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Contravariant first endpoint on the actual nerve simplex category
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.NerveSimplexStart
variable {D : Type u} [Category.{v} D]

abbrev start (s : Index D) : D := (chain s).obj 0

/-- The actual initialSegment from the larger chain's first vertex to the reindexed first vertex. -/
def initialSegment {n m : ℕ} (c : Fin (n + 1) ⥤ D) (d : Fin (m + 1) ⥤ D)
    (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (h : (SimplexCategory.toCat.map θ).toFunctor ⋙ d = c) : d.obj 0 ⟶ c.obj 0 :=
  d.map (homOfLE (Fin.zero_le (θ.toOrderHom 0))) ≫
    eqToHom (congrArg (fun q : Fin (n + 1) ⥤ D => q.obj 0) h)

lemma prefix_comp {n m k : ℕ} (c : Fin (n + 1) ⥤ D) (d : Fin (m + 1) ⥤ D)
    (e : Fin (k + 1) ⥤ D) (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (ψ : SimplexCategory.mk m ⟶ SimplexCategory.mk k)
    (hθ : (SimplexCategory.toCat.map θ).toFunctor ⋙ d = c)
    (hψ : (SimplexCategory.toCat.map ψ).toFunctor ⋙ e = d)
    (h : (SimplexCategory.toCat.map (θ ≫ ψ)).toFunctor ⋙ e = c) :
    initialSegment c e (θ ≫ ψ) h = initialSegment d e ψ hψ ≫ initialSegment c d θ hθ := by
  subst c
  subst d
  simp only [initialSegment, eqToHom_refl, Category.comp_id]
  exact e.map_comp _ _

def startMap {s t : Index D} (f : s ⟶ t) : start t ⟶ start s :=
  initialSegment (chain s) (chain t) (operator f) (chain_eq f)

lemma startMap_id (s : Index D) : startMap (𝟙 s) = 𝟙 (start s) := by
  simp [startMap, initialSegment]

lemma startMap_comp {s t r : Index D} (f : s ⟶ t) (g : t ⟶ r) :
    startMap (f ≫ g) = startMap g ≫ startMap f :=
  prefix_comp (chain s) (chain t) (chain r) (operator f) (operator g)
    (chain_eq f) (chain_eq g) (chain_eq (f ≫ g))

/-- nerveの単体圏から先頭頂点を反変に評価する関手を構成する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
単体を表す合成可能射列の先頭または終端を評価する。
単体圏の射と射列の制限を照合し、関手の法則とaugmentationの式を確認する。
-/
def functor (D : Type u) [Category.{v} D] : Index D ⥤ Dᵒᵖ where
  obj s := Opposite.op (start s)
  map f := (startMap f).op
  map_id s := congrArg Quiver.Hom.op (startMap_id s)
  map_comp f g := congrArg Quiver.Hom.op (startMap_comp f g)

lemma reindexArrow_start {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    startMap (reindexArrow c θ) = c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0))) := by
  simp only [startMap, initialSegment, eqToHom_refl, Category.comp_id]

end SerrePositivity.NerveSimplexStart
