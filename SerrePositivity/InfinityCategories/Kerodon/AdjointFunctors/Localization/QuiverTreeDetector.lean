module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeEvaluation
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# 木の外の生成辺を検出する群値表現

概要：木の辺を単位へ、木の外の辺を整数群の非単位元へ送る。
方針：元の自由 groupoid の普遍性で生成辺のラベルを延長する。
規約：必要な薄さや木性をこの構成に仮定しない。
使われ方：全生成辺が木のどちらかの向きに属することの証明。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeDetector
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))

def edgeInTree {x y : Q} (f : x ⟶ y) : Prop := f.toPos ∈ T x y ∨ f.toNeg ∈ T y x

def edgeLabel {x y : Q} (f : x ⟶ y) : Multiplicative ℤ := by
  classical
  exact if edgeInTree T f then 1 else Multiplicative.ofAdd 1

def detectorPrefunctor : Q ⥤q SingleObj (Multiplicative ℤ) where
  obj _ := SingleObj.star _
  map f := edgeLabel T f

def detector : Quiver.FreeGroupoid Q ⥤ SingleObj (Multiplicative ℤ) :=
  Quiver.FreeGroupoid.lift (detectorPrefunctor T)

def labelValue {x y : Quiver.FreeGroupoid Q} (f : x ⟶ y) : Multiplicative ℤ :=
  (detector T).map f

lemma labelValue_generator {x y : Q} (f : x ⟶ y) :
    labelValue T ((Quiver.FreeGroupoid.of Q).map f) = edgeLabel T f := by
  change edgeLabel T f * 1 = edgeLabel T f
  exact mul_one _

lemma labelValue_id (x : Quiver.FreeGroupoid Q) : labelValue T (𝟙 x) = 1 :=
  (detector T).map_id x

lemma labelValue_comp {x y z : Quiver.FreeGroupoid Q} (f : x ⟶ y) (g : y ⟶ z) :
    labelValue T (f ≫ g) = labelValue T g * labelValue T f :=
  (detector T).map_comp f g

lemma labelValue_inv {x y : Quiver.FreeGroupoid Q} (f : x ⟶ y) :
    labelValue T (inv f) = (labelValue T f)⁻¹ :=
  ((detector T).map_inv f).trans (SingleObj.inv_as_inv _ _)

lemma edgeLabel_of_mem {x y : Q} (f : x ⟶ y) (hf : edgeInTree T f) : edgeLabel T f = 1 := by
  classical
  exact ite_eq_left hf

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeDetector
