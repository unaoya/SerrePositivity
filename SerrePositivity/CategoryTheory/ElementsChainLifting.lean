module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 要素の圏への射列の持ち上げ

## 概要
関手の要素の圏の射列を基底の射列と始点のラベルから復元する。
任意モデル源の厳密化から独立して利用できる一般道具である。

## 方針（定義・証明）
関手によるラベルの移送を各頂点で計算し、再添字と自然変換との交換を示す。
既存の構成を同じ公開名と証明のまま一般層に切り出す。

## 規約と注意
宇宙と仮定は各宣言に明示したものを用いる。
専用の比較図式・正規化充填・選択の整合性は仮定しない。

## 使われ方
一般入口GeneralToolsおよび共有Foundationsから利用する。
旧パスの互換importを通して中断中の厳密化からも利用する。
今後のS-構成・ホモトピー比較・局所化の基礎として使える。
詳細はformalization-plans/k-theory-generalization-inventory.mdの配置実施記録を参照。
-/

@[expose] public section
universe uD vD w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.LabelledChain
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ Type w)
  {n : ℕ} (c : ComposableArrows D n) (x : F.obj (c.obj 0))

lemma eqToHom_hom {a b : F.Elements} (h : a = b) :
    (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
  cases h
  rfl

/-- 基底の射列と始点のラベルから要素の圏の射列を作る。
ラベルは指定した関手で前へ移送し、関手の合成則で射の整合性を示す。 -/
def lift : ComposableArrows F.Elements n where
  obj i := F.elementsMk (c.obj i) (F.map (c.map (homOfLE (Fin.zero_le i))) x)
  map {i j} h := Functor.Elements.homMk (c.map h) (by
    change F.map (c.map h) (F.map (c.map (homOfLE (Fin.zero_le i))) x) = _
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← c.map_comp]
    rfl)
  map_id i := by
    apply Functor.Elements.hom_ext
    exact c.map_id i
  map_comp h k := by
    apply Functor.Elements.hom_ext
    exact c.map_comp h k

lemma reindex {m : ℕ} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (SimplexCategory.toCat.map θ).toFunctor ⋙ lift F c x =
      lift F ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        (F.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))) x) := by
  refine CategoryTheory.Functor.ext (fun i => Functor.Elements.ext _ _ rfl ?_) ?_
  · change F.map (𝟙 _) (F.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom i)))) x) = _
    rw [F.map_id, types_id_apply]
    change F.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom i)))) x =
      F.map (c.map (homOfLE (θ.toOrderHom.monotone (Fin.zero_le i))))
        (F.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))) x)
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← c.map_comp]
    rfl
  · intro i j h
    apply Functor.Elements.hom_ext
    simp [lift, eqToHom_hom]

lemma map {G : D ⥤ Type w} (a : F ⟶ G) :
    lift F c x ⋙ a.mapElements = lift G c (a.app (c.obj 0) x) := by
  refine CategoryTheory.Functor.ext (fun i => Functor.Elements.ext _ _ rfl ?_) ?_
  · change G.map (𝟙 _) (a.app (c.obj i) (F.map (c.map (homOfLE (Fin.zero_le i))) x)) = _
    rw [G.map_id, types_id_apply]
    exact congrArg (fun f => f x) (a.naturality (c.map (homOfLE (Fin.zero_le i))))
  · intro i j h
    apply Functor.Elements.hom_ext
    simp [lift, eqToHom_hom]

/-- A labelled chain is exactly the lift of its actual underlying chain and first label. -/
lemma reconstruct {n : ℕ} (e : ComposableArrows F.Elements n) :
    lift F (e ⋙ Functor.Elements.π F) (e.obj 0).val = e := by
  refine CategoryTheory.Functor.ext (fun i => Functor.Elements.ext _ _ rfl ?_) ?_
  · change F.map (𝟙 _) (F.map (e.map (homOfLE (Fin.zero_le i))).hom (e.obj 0).val) = _
    rw [F.map_id, types_id_apply]
    exact (e.map (homOfLE (Fin.zero_le i))).map_val
  · intro i j h
    apply Functor.Elements.hom_ext
    simp [lift, eqToHom_hom]

lemma lift_heq {c d : ComposableArrows D n} (h : c = d)
    {x : F.obj (c.obj 0)} {y : F.obj (d.obj 0)} (hx : HEq x y) :
    HEq (lift F c x) (lift F d y) := by
  subst d
  cases hx
  rfl

lemma ext_of_first {n : ℕ} {c d : ComposableArrows F.Elements n}
    (h : c ⋙ Functor.Elements.π F = d ⋙ Functor.Elements.π F)
    (hx : HEq (c.obj 0).val (d.obj 0).val) : c = d :=
  (reconstruct F c).symm.trans ((eq_of_heq (lift_heq F h hx)).trans (reconstruct F d))

end SerrePositivity.LabelledChain
