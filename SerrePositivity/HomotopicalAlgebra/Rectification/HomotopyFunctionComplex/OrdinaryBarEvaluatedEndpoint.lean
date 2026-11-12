module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint

/-!
# 中断した任意モデル源への一般化：OrdinaryBarEvaluatedEndpoint

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual small factorization and augmentation square for the other endpoint。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0160][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0160
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual small factorization and augmentation square for the other endpoint

The same small reference output is used, with explicit lift wrappers.
The homotopy starts at the standard bar simplex-nerve augmentation.
Invertibility of the augmentations or evaluation remains unproved here.
-/

@[expose] public section
universe v u uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

abbrev SmallNerve := SSet.uliftFunctor.{max u v, v}.obj
  (nerve (BarOutput.output R).Elements)

def evaluationNerveMap : SSet.uliftFunctor.{max u v, max u v}.obj
    (nerve (OrdinaryBarTotalCone.Index R)) ⟶ SmallNerve R where
  app _ := ↾fun c => ULift.up (c.down ⋙ OrdinaryBarTotalEvaluation.evaluationElements R a b)
  naturality {_ _} _ := rfl

def rowNerveMap : SmallNerve R ⟶ OrdinaryBarEvaluation.bar R where
  app n := ↾fun c => (OrdinaryBarNerveBridge.rawBridge R).app n
    (c.down ⋙ OrdinaryBarTotalEvaluation.rowElements R)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    exact congrArg (fun f => f (c.down ⋙ OrdinaryBarTotalEvaluation.rowElements R))
      ((OrdinaryBarNerveBridge.rawBridge R).naturality θ)

/-- Both source and target wrappers are explicit, including the original output wrapper. -/
def smallAugmentation : SmallNerve R ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (BarOutput.output R) where
  app n := ↾fun c => ULift.up ((SimplexNerveAugmentation.augmentation
    (BarOutput.output R)).app n c.down)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    apply ULift.ext
    exact congrArg (fun f => f c.down)
      ((SimplexNerveAugmentation.augmentation (BarOutput.output R)).naturality θ)

lemma evaluatedComposite_eq : OrdinaryBarNerveBridge.evaluatedComposite R a b =
    evaluationNerveMap R a b ≫ rowNerveMap R := rfl

lemma augmentation_square : OrdinaryBarNerveBridge.simplexAugmentation R ≫
    OrdinaryBarEvaluation.evaluation R a b = evaluationNerveMap R a b ≫ smallAugmentation R := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  apply ULift.ext
  let α := SimplexNerveAugmentation.parameter (OrdinaryBarEvaluation.bar R) c.down
  exact congrArg ULift.down (congrArg (fun f => f (c.down.obj 0).val)
    ((OrdinaryBarEvaluation.evaluation R a b).naturality α.op))

def homotopy : SSet.Homotopy (OrdinaryBarNerveBridge.simplexAugmentation R)
    (evaluationNerveMap R a b ≫ rowNerveMap R) := by
  rw [← evaluatedComposite_eq R a b]
  exact OrdinaryBarFirstEndpoint.homotopy R a b

variable {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma image_eq : L.map (OrdinaryBarNerveBridge.simplexAugmentation R) =
    L.map (evaluationNerveMap R a b) ≫ L.map (rowNerveMap R) :=
  (AnodyneHomotopy.map_homotopy_eq L hL (homotopy R a b)).trans (L.map_comp _ _)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint
