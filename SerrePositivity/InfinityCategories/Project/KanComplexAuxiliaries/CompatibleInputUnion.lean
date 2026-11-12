module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# 中断した任意モデル源への一般化：CompatibleInputUnion

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Glue compatible input prescriptions, with arbitrarily large index type。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0374][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0374
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Glue compatible input prescriptions, with arbitrarily large index type

The union lies inside the given small input simplicial set, so its value
universe does not grow with the index type. Agreement whenever two inputs
coincide makes the prescribed output descend to this union. No individual
input family is assumed monic.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion
variable {J : Type u} {B E : SSet.{v}} (S : J → SSet.{v})
  (b : ∀ j, S j ⟶ B) (a : ∀ j, S j ⟶ E)

def Compatible : Prop := ∀ j k m (x : (S j).obj m) (y : (S k).obj m),
  (b j).app m x = (b k).app m y → (a j).app m x = (a k).app m y

abbrev inputs : B.Subcomplex := ⨆ j, SSet.Subcomplex.range (b j)

lemma mem_inputs (m : SimplexCategoryᵒᵖ) (x : B.obj m) :
    x ∈ (inputs S b).obj m ↔ ∃ j, ∃ y : (S j).obj m, (b j).app m y = x := by
  simp only [inputs, Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion, Set.mem_range]

def toInputs (j : J) : S j ⟶ (inputs S b).toSSet :=
  SSet.Subcomplex.lift (b j) (le_iSup (fun k => SSet.Subcomplex.range (b k)) j)

lemma toInputs_inclusion (j : J) : toInputs S b j ≫ (inputs S b).ι = b j := rfl

lemma hom_ext {D : SSet.{v}} {f g : (inputs S b).toSSet ⟶ D}
    (h : ∀ j, toInputs S b j ≫ f = toInputs S b j ≫ g) : f = g := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨j, y, hy⟩ := (mem_inputs S b m x.val).mp x.property
  have hx : (toInputs S b j).app m y = x := Subtype.ext hy
  simpa only [NatTrans.comp_app, types_comp_apply, hx] using
    types_congr_hom (congr_app (h j) m) y

def witness (m : SimplexCategoryᵒᵖ) (x : ((inputs S b).toSSet).obj m) :
    Σ j, { y : (S j).obj m // (b j).app m y = x.val } :=
  let h := (mem_inputs S b m x.val).mp x.property
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

def value (m : SimplexCategoryᵒᵖ) (x : ((inputs S b).toSSet).obj m) : E.obj m :=
  (a (witness S b m x).1).app m (witness S b m x).2.val

variable (h : Compatible S b a)

include h in
lemma value_eq (j : J) (m : SimplexCategoryᵒᵖ) (y : (S j).obj m)
    (x : ((inputs S b).toSSet).obj m) (hx : (b j).app m y = x.val) :
    value S b a m x = (a j).app m y :=
  h (witness S b m x).1 j m (witness S b m x).2.val y
    ((witness S b m x).2.property.trans hx.symm)

def lift : (inputs S b).toSSet ⟶ E where
  app m := ↾fun x => value S b a m x
  naturality {m q} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    let w := witness S b m x
    have hb : (b w.1).app q ((S w.1).map θ w.2.val) =
        (((inputs S b).toSSet).map θ x).val :=
      (types_congr_hom ((b w.1).naturality θ) w.2.val).trans
        (congrArg (B.map θ) w.2.property)
    exact (value_eq S b a h w.1 q ((S w.1).map θ w.2.val) _ hb).trans
      (types_congr_hom ((a w.1).naturality θ) w.2.val)

lemma toInputs_lift (j : J) : toInputs S b j ≫ lift S b a h = a j := by
  apply NatTrans.ext
  funext m
  exact ConcreteCategory.hom_ext _ _ (fun x => value_eq S b a h j m x _ rfl)

variable (p : E ⟶ B) (hp : ∀ j, a j ≫ p = b j)

include hp in
lemma lift_over : lift S b a h ≫ p = (inputs S b).ι := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  let w := witness S b m x
  change p.app m ((a w.1).app m w.2.val) = x.val
  exact (types_congr_hom (congr_app (hp w.1) m) w.2.val).trans w.2.property

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion
