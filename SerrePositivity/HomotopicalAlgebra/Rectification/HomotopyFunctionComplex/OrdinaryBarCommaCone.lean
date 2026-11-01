module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRowDiagram

/-!
# 中断した任意モデル源への一般化：OrdinaryBarCommaCone

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A whole cone inside the ordinary resolution comma category。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0148][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0148
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A whole cone inside the ordinary resolution comma category

The actual row comparisons give a natural transformation of comma-valued
functors. All row and prefix maps are retained, with no outer-frame lifts.
This is not a contraction of the simplicial bar.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarCommaCone
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

def first : (OrdinaryBarRowDiagram.Index R)ᵒᵖ ⥤ OrdinaryBarCenters.Comma R where
  obj s := NerveSimplexStart.start s.unop
  map f := NerveSimplexStart.startMap f.unop
  map_id s := NerveSimplexStart.startMap_id s.unop
  map_comp f g := NerveSimplexStart.startMap_comp g.unop f.unop

abbrev rows : (OrdinaryBarRowDiagram.Index R)ᵒᵖ ⥤ OrdinaryBarCenters.Comma R :=
  (OrdinaryBarRowDiagram.degrees R).op ⋙ OrdinaryResolutionRows.commaRows R

variable (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

def cone : first R ⟶ rows R where
  app s := CostructuredArrow.homMk
    (((OrdinaryBarRowDiagram.left R a).app s.unop).op,
      ((OrdinaryBarRowDiagram.right R b).app s.unop).op)
    (by
      change (NerveSimplexStart.start s.unop).hom ≫ 𝟙 _ = _
      exact Category.comp_id _)
  naturality {s t} f := by
    apply CostructuredArrow.hom_ext
    apply Prod.ext
    · exact congrArg Quiver.Hom.op ((OrdinaryBarRowDiagram.left R a).naturality f.unop).symm
    · exact congrArg Quiver.Hom.op ((OrdinaryBarRowDiagram.right R b).naturality f.unop).symm

lemma cone_recovery (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    ((cone R a b).app (op (ofChain (OrdinaryBarEvaluation.chain R n c)))).left =
      OrdinaryBarSimplexCone.arrow R a b n c := rfl

/-- Forget only labels to pull the whole comma cone back to the actual bar simplex category. -/
def forgetLabels : OrdinaryBarEvaluation.bar R ⟶ nerve (OrdinaryBarCenters.Comma R) where
  app n := ↾fun c => OrdinaryBarEvaluation.chain R n c
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    exact OrdinaryBarEvaluation.chain_operator R θ c

abbrev barIndices : (OrdinaryBarEvaluation.bar R).Elements ⥤
    (OrdinaryBarRowDiagram.Index R)ᵒᵖ :=
  (forgetLabels R).mapElements ⋙ opOp _

abbrev barCone : barIndices R ⋙ first R ⟶ barIndices R ⋙ rows R :=
  Functor.whiskerLeft (barIndices R) (cone R a b)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarCommaCone
