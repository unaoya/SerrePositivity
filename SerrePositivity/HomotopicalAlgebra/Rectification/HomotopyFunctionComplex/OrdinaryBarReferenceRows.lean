module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarReference

/-!
# 中断した任意モデル源への一般化：OrdinaryBarReferenceRows

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Labelled reference-to-row comparison on the original small raw simplex category。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0207][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0207
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Labelled reference-to-row comparison on the original small raw simplex category

The row label is the actual small mixed augmentation of the raw label.
Every original degree and simplex operator is retained.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRows
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

abbrev raw : SSet.{v} :=
  OrdinaryResolutionPairs.raw.obj (OrdinaryResolutionPairs.forgetFrames.obj R)
abbrev augmentation : raw R ⟶ BarOutput.output R :=
  MixedResolutionComparison.comparison.app R

def referenceBase : (raw R).Elements ⥤ OrdinaryBarCenters.Comma R × SimplexCategoryᵒᵖ :=
  ((Functor.const _).obj (OrdinaryResolutionRows.reference R)).prod'
    (Functor.Elements.π (raw R))

def referenceLabels : (raw R).Elements ⥤
    (referenceBase R ⋙ OrdinaryBarTotalCone.values R).Elements where
  obj s := (referenceBase R ⋙ OrdinaryBarTotalCone.values R).elementsMk s s.val
  map {s t} f := Functor.Elements.homMk f (by
    change (raw R).map f.hom
      (((OrdinaryResolutionPairs.raw.map (𝟙 (OrdinaryResolutionPairs.forgetFrames.obj R))).app
        s.obj) s.val) = t.val
    rw [CategoryTheory.Functor.map_id]
    exact f.map_val)

abbrev referenceElements : (raw R).Elements ⥤ OrdinaryBarTotalCone.Total R :=
  referenceLabels R ⋙ Functor.Elements.precomp (referenceBase R) (OrdinaryBarTotalCone.values R)

abbrev rowElements : (raw R).Elements ⥤ OrdinaryBarTotalCone.Total R :=
  (augmentation R).mapElements ⋙ OrdinaryBarTotalEvaluation.rowElements R

def comparison : referenceElements R ⟶ rowElements R where
  app s := Functor.Elements.homMk
    ((OrdinaryResolutionRows.commaAugmentation R).app s.obj, 𝟙 s.obj) (by
      change ((OrdinaryResolutionPairs.raw.obj ((OrdinaryResolutionRows.rows R).obj s.obj)).map
        (𝟙 s.obj)) (((OrdinaryResolutionPairs.raw.map
          ((OrdinaryResolutionRows.augmentation R).app s.obj)).app s.obj) s.val) =
            (augmentation R).app s.obj s.val
      rw [CategoryTheory.Functor.map_id]
      rfl)
  naturality {s t} f := by
    apply Functor.Elements.hom_ext
    apply Prod.ext
    · exact (OrdinaryResolutionRows.commaAugmentation R).naturality f.hom
    · change f.hom ≫ 𝟙 t.obj = 𝟙 s.obj ≫ f.hom
      simp only [Category.comp_id, Category.id_comp]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRows
