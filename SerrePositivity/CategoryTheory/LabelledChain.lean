module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 中断した任意モデル源への一般化：LabelledChain

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Lifting a whole chain from its original first label。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0010][inventory]を参照する。

[inventory]: ../../formalization-plans/k-theory-generalization-inventory.md#m0010
[plan]: ../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Lifting a whole chain from its original first label

All labels are transported by the actual prefix maps. Reindexing uses the
transported label at the new first vertex, and maps of value diagrams
transport the same whole labelled chain.
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
