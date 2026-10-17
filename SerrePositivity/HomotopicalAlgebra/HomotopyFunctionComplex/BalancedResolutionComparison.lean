module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping

/-!
# 中断した任意モデル源への一般化：BalancedResolutionComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A natural small Kan span between the left and right framed double Hom。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0060][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0060
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A natural small Kan span between the left and right framed double Hom

Both legs are actual maps in the original simplicial model. The common
middle is the Kan replacement of the same raw double Hom.
-/

@[expose] public section
universe v u vH uH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.BalancedResolutionComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev rawRight : BiresolutionRawMapping.functor (C := C) ⟶
    BiresolutionRightMapping.functor hcof hfib :=
  BiresolutionRightMapping.rawFlipIso.hom ≫ BiresolutionRightMapping.comparison hcof hfib

lemma rawRight_weakEquivalence (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((rawRight hcof hfib).app X) :=
  (weakEquivalences SSet.{v}).comp_mem _ _ ((weakEquivalences SSet.{v}).of_isIso _)
    (BiresolutionRightMapping.comparison_weakEquivalence hcof hfib X)

abbrev middle : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  BiresolutionRawMapping.functor ⋙ KanReplacement.functor hcof hfib
abbrev rightFunctor : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  BiresolutionRightMapping.functor hcof hfib ⋙ KanReplacement.functor hcof hfib

def left : middle (C := C) hcof hfib ⟶ RightResolutionMapping.kanFunctor hcof hfib :=
  Functor.whiskerRight (BiresolutionRawMapping.comparison hcof hfib)
    (KanReplacement.functor hcof hfib)

def right : middle (C := C) hcof hfib ⟶ rightFunctor hcof hfib :=
  Functor.whiskerRight (rawRight hcof hfib) (KanReplacement.functor hcof hfib)

lemma left_weakEquivalence (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((left hcof hfib).app X) :=
  KanReplacement.map_weakEquivalence hcof hfib _
    (BiresolutionRawMapping.comparison_weakEquivalence hcof hfib X)

lemma right_weakEquivalence (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((right hcof hfib).app X) :=
  KanReplacement.map_weakEquivalence hcof hfib _ (rawRight_weakEquivalence hcof hfib X)

lemma middle_kanComplex (X : RightResolutionMapping.Index C) :
    SSet.KanComplex ((middle hcof hfib).obj X) := KanReplacement.kanComplex hcof hfib _

lemma right_kanComplex (X : RightResolutionMapping.Index C) :
    SSet.KanComplex ((rightFunctor hcof hfib).obj X) := KanReplacement.kanComplex hcof hfib _

lemma left_piZero_bijective (X : RightResolutionMapping.Index C) :
    Function.Bijective (SSet.mapπ₀ ((left hcof hfib).app X)) := by
  have : IsFibrant ((middle hcof hfib).obj X) := KanReplacement.isFibrant hcof hfib _
  have : IsFibrant ((RightResolutionMapping.kanFunctor hcof hfib).obj X) :=
    KanReplacement.isFibrant hcof hfib _
  have : WeakEquivalence ((left hcof hfib).app X) := ⟨left_weakEquivalence hcof hfib X⟩
  exact piZero_bijective_of_weakEquivalence_of_fibrant hcof _

lemma right_piZero_bijective (X : RightResolutionMapping.Index C) :
    Function.Bijective (SSet.mapπ₀ ((right hcof hfib).app X)) := by
  have : IsFibrant ((middle hcof hfib).obj X) := KanReplacement.isFibrant hcof hfib _
  have : IsFibrant ((rightFunctor hcof hfib).obj X) :=
    KanReplacement.isFibrant hcof hfib _
  have : WeakEquivalence ((right hcof hfib).app X) := ⟨right_weakEquivalence hcof hfib X⟩
  exact piZero_bijective_of_weakEquivalence_of_fibrant hcof _

def rightPiZeroEquiv {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] (X : RightResolutionMapping.Index C) :
    SSet.π₀ ((rightFunctor hcof hfib).obj X) ≃
      (Q.obj ((RightResolutionMapping.projection (C := C)).obj X).1.unop ⟶
        Q.obj ((RightResolutionMapping.projection (C := C)).obj X).2) :=
  (Equiv.ofBijective _ (right_piZero_bijective hcof hfib X)).symm.trans
    ((Equiv.ofBijective _ (left_piZero_bijective hcof hfib X)).trans
      (RightResolutionMapping.piZeroEquiv hcof hfib Q X))

def localizedIso {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})] :
    RightResolutionMapping.kanFunctor (C := C) hcof hfib ⋙ L ≅
      rightFunctor hcof hfib ⋙ L := by
  have : IsIso (Functor.whiskerRight (left (C := C) hcof hfib) L) := by
    have (X : RightResolutionMapping.Index C) :
        IsIso ((Functor.whiskerRight (left hcof hfib) L).app X) :=
      Localization.inverts L _ _ (left_weakEquivalence hcof hfib X)
    exact NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight (right (C := C) hcof hfib) L) := by
    have (X : RightResolutionMapping.Index C) :
        IsIso ((Functor.whiskerRight (right hcof hfib) L).app X) :=
      Localization.inverts L _ _ (right_weakEquivalence hcof hfib X)
    exact NatIso.isIso_of_isIso_app _
  exact (asIso (Functor.whiskerRight (left hcof hfib) L)).symm ≪≫
    asIso (Functor.whiskerRight (right hcof hfib) L)

end SerrePositivity.HomotopyFunctionComplex.BalancedResolutionComparison
