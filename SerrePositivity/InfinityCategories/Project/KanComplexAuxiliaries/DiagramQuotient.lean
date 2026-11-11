module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Logic.Small.Basic

/-!
# 中断した任意モデル源への一般化：DiagramQuotient

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類C）。
対象：Quotients of entire simplicial diagrams by stable degreewise congruences。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0390][inventory]を参照する。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0390
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Quotients of entire simplicial diagrams by stable degreewise congruences

Both base action and simplicial operators descend through the same relation.
The base may be large. No homotopical assertion about the quotient is assumed.
-/

@[expose] public section
universe v w uD vD
noncomputable section
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{w})

structure Congruence where
  rel : ∀ d n, Setoid ((F.obj d).obj n)
  simplicial : ∀ d {n m} (θ : n ⟶ m) {x y},
    (rel d n).r x y → (rel d m).r ((F.obj d).map θ x) ((F.obj d).map θ y)
  base : ∀ {d e} (f : d ⟶ e) n {x y},
    (rel d n).r x y → (rel e n).r ((F.map f).app n x) ((F.map f).app n y)

/-- Erasing all degreewise labels is stable, but need not preserve homotopy types. -/
def total : Congruence F where
  rel _ _ := ⊤
  simplicial _ {_ _} _ {_ _} _ := trivial
  base {_ _} _ _ {_ _} _ := trivial

variable {F} (R : Congruence F)

def value (d : D) : SSet.{w} where
  obj n := Quotient (R.rel d n)
  map θ := ↾(Quotient.map ((F.obj d).map θ) (fun _ _ h => R.simplicial d θ h))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact congrArg (Quotient.mk (R.rel d n)) (types_congr_hom ((F.obj d).map_id n) x)
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact congrArg (Quotient.mk _)
      (types_congr_hom ((F.obj d).map_comp θ φ) x)

def action {d e : D} (f : d ⟶ e) : value R d ⟶ value R e where
  app n := ↾(Quotient.map ((F.map f).app n) (fun _ _ h => R.base f n h))
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact congrArg (Quotient.mk _) (types_congr_hom ((F.map f).naturality θ) x)

def functor : D ⥤ SSet.{w} where
  obj := value R
  map := action R
  map_id d := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact congrArg (Quotient.mk _)
      (types_congr_hom (congr_app (F.map_id d) n) x)
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact congrArg (Quotient.mk _)
      (types_congr_hom (congr_app (F.map_comp f g) n) x)

def projection : F ⟶ functor R where
  app _ :=
    { app _ := ↾(Quotient.mk _)
      naturality {_ _} _ := rfl }
  naturality {_ _} _ := rfl

lemma projection_surjective (d : D) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective (((projection R).app d).app n) := Quotient.mk_surjective

instance total_subsingleton (d : D) (n : SimplexCategoryᵒᵖ) :
    Subsingleton ((value (total F) d).obj n) := by
  constructor
  intro a b
  refine Quotient.inductionOn a (fun x => ?_)
  refine Quotient.inductionOn b (fun y => ?_)
  exact Quotient.sound trivial

section Kernel
variable {G : D ⥤ SSet.{w}} (a : F ⟶ G)

/-- Equality of labels in a whole natural simplicial diagram is a stable congruence. -/
def kernel : Congruence F where
  rel d n := Setoid.ker ((a.app d).app n)
  simplicial d {n m} θ {x y} h := by
    change (a.app d).app m ((F.obj d).map θ x) =
      (a.app d).app m ((F.obj d).map θ y)
    have hx := types_congr_hom ((a.app d).naturality θ) x
    have hy := types_congr_hom ((a.app d).naturality θ) y
    exact hx.trans ((congrArg ((G.obj d).map θ) h).trans hy.symm)
  base {d e} f n {x y} h := by
    change (a.app e).app n ((F.map f).app n x) =
      (a.app e).app n ((F.map f).app n y)
    have hx := types_congr_hom (congr_app (a.naturality f) n) x
    have hy := types_congr_hom (congr_app (a.naturality f) n) y
    exact hx.trans ((congrArg ((G.map f).app n) h).trans hy.symm)

def descend (ha : ∀ d n {x y}, (R.rel d n).r x y →
    (a.app d).app n x = (a.app d).app n y) : functor R ⟶ G where
  app d :=
    { app n := ↾(Quotient.lift ((a.app d).app n) (fun _ _ h => ha d n h))
      naturality {n m} θ := by
        apply ConcreteCategory.hom_ext
        intro q
        refine Quotient.inductionOn q (fun x => ?_)
        exact types_congr_hom ((a.app d).naturality θ) x }
  naturality {d e} f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    exact types_congr_hom (congr_app (a.naturality f) n) x

lemma projection_descend (ha : ∀ d n {x y}, (R.rel d n).r x y →
    (a.app d).app n x = (a.app d).app n y) : projection R ≫ descend R a ha = a := rfl

def kernelComparison : functor (kernel a) ⟶ G :=
  descend (kernel a) a (fun _ _ {_ _} h => h)

lemma kernel_factorization : projection (kernel a) ≫ kernelComparison a = a := rfl

lemma kernelComparison_injective (d : D) (n : SimplexCategoryᵒᵖ) :
    Function.Injective (((kernelComparison a).app d).app n) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Quotient.exists_rep x
  obtain ⟨y, rfl⟩ := Quotient.exists_rep y
  exact Quotient.sound hxy

lemma kernelComparison_surjective (d : D) (n : SimplexCategoryᵒᵖ)
    (ha : Function.Surjective ((a.app d).app n)) :
    Function.Surjective (((kernelComparison a).app d).app n) := by
  intro z
  obtain ⟨x, hx⟩ := ha z
  exact ⟨Quotient.mk _ x, hx⟩

lemma kernelComparison_isIso
    (ha : ∀ d n, Function.Surjective ((a.app d).app n)) :
    IsIso (kernelComparison a) := by
  have (d : D) (n : SimplexCategoryᵒᵖ) :
      IsIso (((kernelComparison a).app d).app n) :=
    (CategoryTheory.isIso_iff_bijective _).mpr
      ⟨kernelComparison_injective a d n, kernelComparison_surjective a d n (ha d n)⟩
  have (d : D) : IsIso ((kernelComparison a).app d) := NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

include a in
lemma kernel_small (d : D) (n : SimplexCategoryᵒᵖ)
    [Small.{v} ((G.obj d).obj n)] : Small.{v} (Quotient ((kernel a).rel d n)) :=
  small_of_injective (kernelComparison_injective a d n)

end Kernel

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient
