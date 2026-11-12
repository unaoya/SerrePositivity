module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Fintype.Card

/-!
# 同じ列の像を持つ元の語の包含の一意性

概要：同じ終域で同じ列の像を持つ包含は、元の語の等式を除いて同じ写像。
方針：像の順序同型と有限順序の同型の一意性で、元の方向を回収する。
規約：元の語と元の射の等式であり、圏の同値だけでは代用しない。
使われ方：異なる順序の列削除の元の全射列の一致。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

lemma eqToHom_apply {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (h : a = b) (i : Fin a.length) :
    (eqToHom h : a ⟶ b).orderHom i = Fin.cast (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.length h) i := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (eqToHom_apply)


lemma embedding_eq_of_range {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (h : Set.range f.orderHom = Set.range g.orderHom) :
    ∃ hab : a = b, eqToHom hab ≫ g = f := by
  let ef := (f.orderHom.monotone.strictMono_of_injective hf).orderIso f.orderHom
  let eg := (g.orderHom.monotone.strictMono_of_injective hg).orderIso g.orderHom
  let e : Fin a.length ≃o Fin b.length :=
    ef.trans ((Set.orderIsoOfEq _ _ h).trans eg.symm)
  have hn : a.length = b.length := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
  have hfg (i : Fin a.length) : g.orderHom (Fin.cast hn i) = f.orderHom i := by
    have he : e i = Fin.cast hn i := Fin.ext (Fin.coe_orderIso_apply e i)
    have hh : g.orderHom (e i) = f.orderHom i := by
      change (eg (eg.symm ((Set.orderIsoOfEq _ _ h) (ef i)))).val = f.orderHom i
      rw [eg.apply_symm_apply]
      rfl
    rw [he] at hh
    exact hh
  have hab : a = b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext a b hn (fun i =>
    (f.direction_eq i).symm.trans
      ((congrArg c.direction (hfg i).symm).trans (g.direction_eq (Fin.cast hn i))))
  refine ⟨hab, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
  intro i
  change g.orderHom ((eqToHom hab : a ⟶ b).orderHom i) = f.orderHom i
  rw [eqToHom_apply]
  exact hfg i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (embedding_eq_of_range)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
