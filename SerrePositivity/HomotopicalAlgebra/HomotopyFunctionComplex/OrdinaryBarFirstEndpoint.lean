module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge
public import SerrePositivity.CategoryTheory.NerveSimplexFirstFunctor

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFirstEndpoint

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Identifying the first bar-valued endpoint on all original chains。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0164][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0164
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Identifying the first bar-valued endpoint on all original chains

The comma chain is recovered using naturality of the standard simplex
augmentation. Original Hom labels are retained throughout.
-/

@[expose] public section
universe v u uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

lemma chain_ext {n : SimplexCategoryᵒᵖ} (c d : (OrdinaryBarEvaluation.bar R).obj n)
    (h : c ⋙ OrdinaryBarEvaluation.forgetElements R n =
      d ⋙ OrdinaryBarEvaluation.forgetElements R n) (h₀ : c.obj 0 = d.obj 0) : c = d := by
  let E := BarConstruction.elementsComma OrdinaryResolutionPairs.projection
    OrdinaryResolutionPairs.raw ((RightResolutionMapping.projection (C := C)).obj R) n
  let G := (BarConstruction.commaValues OrdinaryResolutionPairs.projection
    OrdinaryResolutionPairs.raw ((RightResolutionMapping.projection (C := C)).obj R)).flip.obj n
  have hv : ∀ {e e' : G.Elements}, e = e' → HEq e.val e'.val := by
    intro e e' he
    cases he
    rfl
  have he : c ⋙ E = d ⋙ E := LabelledChain.ext_of_first G h
    (hv (congrArg E.obj h₀))
  let Q := BarConstruction.commaElements OrdinaryResolutionPairs.projection
    OrdinaryResolutionPairs.raw ((RightResolutionMapping.projection (C := C)).obj R) n
  calc
    c = (c ⋙ E) ⋙ Q := by apply CategoryTheory.Functor.ext (fun _ => rfl)
    _ = (d ⋙ E) ⋙ Q := congrArg (fun e => e ⋙ Q) he
    _ = d := by apply CategoryTheory.Functor.ext (fun _ => rfl)

lemma forgetLabels_eq : OrdinaryBarNerveBridge.firstComposite R ≫
    OrdinaryBarCommaCone.forgetLabels R =
      OrdinaryBarNerveBridge.simplexAugmentation R ≫ OrdinaryBarCommaCone.forgetLabels R := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  have hn := congrArg (fun a => a.app n x.down)
    (SimplexNerveAugmentation.naturality (OrdinaryBarEvaluation.bar R)
      (OrdinaryBarCommaCone.forgetLabels R))
  calc
    _ = x.down ⋙ OrdinaryBarTotalCone.commaFirst R := by
      apply CategoryTheory.Functor.ext (fun _ => rfl)
    _ = _ := (NerveSimplexFirstFunctor.chain_augmentation (OrdinaryBarCenters.Comma R)
      (x.down ⋙ (OrdinaryBarCommaCone.forgetLabels R).mapElements)).trans hn

lemma first_object_eq (n : SimplexCategoryᵒᵖ)
    (x : (SSet.uliftFunctor.{max u v, max u v}.obj
      (nerve (OrdinaryBarTotalCone.Index R))).obj n) :
    (((OrdinaryBarNerveBridge.firstComposite R).app n x).obj 0) =
      (((OrdinaryBarNerveBridge.simplexAugmentation R).app n x).obj 0) := by
  let δ := x.down ⋙ Functor.Elements.π (OrdinaryBarEvaluation.bar R)
  let α := SimplexChainParameter.parameter δ
  let t := (x.down.obj 0).val
  let P := (((BarConstruction.commaLevels OrdinaryResolutionPairs.projection
    OrdinaryResolutionPairs.raw).map α.op).app
      ((RightResolutionMapping.projection (C := C)).obj R)).toFunctor
  change (((BarConstruction.TotalNerve.simplex
    (BarConstruction.commaValues OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw
      ((RightResolutionMapping.projection (C := C)).obj R))
    (x.down ⋙ OrdinaryBarTotalCone.first R)) ⋙
      BarConstruction.commaElements OrdinaryResolutionPairs.projection OrdinaryResolutionPairs.raw
        ((RightResolutionMapping.projection (C := C)).obj R) n).obj 0) = P.obj (t.obj _)
  rw [Functor.comp_obj, BarConstruction.TotalNerve.first_vertex]
  change P.obj (t.obj 0) = P.obj (t.obj (α.toOrderHom 0))
  rw [SimplexChainParameter.parameter_zero]

lemma firstComposite_eq : OrdinaryBarNerveBridge.firstComposite R =
    OrdinaryBarNerveBridge.simplexAugmentation R := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply chain_ext R _ _
  · exact congrArg (fun a => a.app n x) (forgetLabels_eq R)
  · exact first_object_eq R n x

variable (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

def homotopy : SSet.Homotopy (OrdinaryBarNerveBridge.simplexAugmentation R)
    (OrdinaryBarNerveBridge.evaluatedComposite R a b) := by
  rw [← firstComposite_eq R]
  exact OrdinaryBarNerveBridge.homotopy R a b

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma image_eq : L.map (OrdinaryBarNerveBridge.simplexAugmentation R) =
    L.map (OrdinaryBarNerveBridge.evaluatedComposite R a b) :=
  AnodyneHomotopy.map_homotopy_eq L hL (homotopy R a b)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint
