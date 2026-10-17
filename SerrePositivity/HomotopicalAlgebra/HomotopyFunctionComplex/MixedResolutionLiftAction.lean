module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction

/-!
# 中断した任意モデル源への一般化：MixedResolutionLiftAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Simultaneous actual resolution lifts in the two variables。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0128][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0128
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Simultaneous actual resolution lifts in the two variables

The family compatibility is derived from the original lift inclusions.
Both action orders agree before Kan replacement. Arbitrary monomorphic
boundary families extend while retaining the entire mixed action.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.MixedResolutionLiftAction
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ

def family (X X' : ResolutionObject C) (f : X.base ⟶ X'.base) {T : SSet.{v}}
    (s : T ⟶ ResolutionLiftSpace.obj X X' f) :
    CosimplicialMapFamily T (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj)
      X'.resolution.obj :=
  CosimplicialMapFamily.ofDoubleHom (s ≫ ResolutionLiftSpace.inclusion X X' f)

lemma family_point {X X' : ResolutionObject C} (k : X ⟶ X') {T : SSet.{v}}
    (d : T ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (family X X' k.base (d ≫ ResolutionLiftSpace.ofLift k)).app n x =
      (DiagonalFrame.augmentation (ResolutionLiftSpace.frame X).augmentation).app n.unop ≫
        k.diagram.app n.unop := by
  have hk : ResolutionLiftSpace.ofLift k ≫ ResolutionLiftSpace.inclusion X X' k.base =
      LiftSpace.point (ResolutionLiftSpace.frame X).obj
        (ResolutionLiftSpace.frame X).augmentation k.diagram :=
    LiftSpace.ofLift_inclusion _ _ _ _ k.diagram k.over
  change (((d ≫ ResolutionLiftSpace.ofLift k) ≫
    ResolutionLiftSpace.inclusion X X' k.base).app n x).app n.unop = _
  rw [Category.assoc, hk]
  rfl

variable (X X' : ResolutionObject C) (f : X.base ⟶ X'.base)
  (Y Y' : ResolutionObject Cᵒᵖ) (g : Y.base ⟶ Y'.base)

abbrev input : SSet.{v} := MixedDiagonalHom.obj X'.resolution.obj Y'.resolution.obj
abbrev output : SSet.{v} := MixedDiagonalHom.obj
  (DiagonalFrame.obj (ResolutionLiftSpace.frame X).obj)
  (DiagonalFrame.obj (ResolutionLiftSpace.frame Y).obj)

def action {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X X' f)
    (r : T ⟶ ResolutionLiftSpace.obj Y Y' g) (t : T ⟶ input X' Y') : T ⟶ output X Y :=
  MixedDiagonalHom.action (family X X' f s) (family Y Y' g r) t

lemma action_orders {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X X' f)
    (r : T ⟶ ResolutionLiftSpace.obj Y Y' g) (t : T ⟶ input X' Y') :
    MixedDiagonalHom.pre (family X X' f s) (MixedDiagonalHom.post (family Y Y' g r) t) =
      MixedDiagonalHom.post (family Y Y' g r) (MixedDiagonalHom.pre (family X X' f s) t) :=
  MixedDiagonalHom.pre_post _ _ _

lemma action_parameter {T U : SSet.{v}} (a : U ⟶ T)
    (s : T ⟶ ResolutionLiftSpace.obj X X' f) (r : T ⟶ ResolutionLiftSpace.obj Y Y' g)
    (t : T ⟶ input X' Y') :
    a ≫ action X X' f Y Y' g s r t = action X X' f Y Y' g (a ≫ s) (a ≫ r) (a ≫ t) := by
  ext n x
  rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma extends_action {K L : SSet.{v}} (i : K ⟶ L) [Mono i]
    (s : K ⟶ ResolutionLiftSpace.obj X X' f) (r : K ⟶ ResolutionLiftSpace.obj Y Y' g)
    (t : L ⟶ input X' Y') :
    ∃ (s' : L ⟶ ResolutionLiftSpace.obj X X' f) (r' : L ⟶ ResolutionLiftSpace.obj Y Y' g),
      i ≫ s' = s ∧ i ≫ r' = r ∧
        i ≫ action X X' f Y Y' g s' r' t = action X X' f Y Y' g s r (i ≫ t) := by
  obtain ⟨s', hs⟩ := ResolutionLiftSpace.extension hcof X X' f i s
  obtain ⟨r', hr⟩ := ResolutionLiftSpace.extension hcof Y Y' g i r
  refine ⟨s', r', hs, hr, ?_⟩
  rw [action_parameter, hs, hr]

variable (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

def kanAction {T : SSet.{v}} (s : T ⟶ ResolutionLiftSpace.obj X X' f)
    (r : T ⟶ ResolutionLiftSpace.obj Y Y' g) (t : T ⟶ input X' Y') :
    T ⟶ (SimplicialModel.KanReplacement.functor hcof hfib).obj (output X Y) :=
  action X X' f Y Y' g s r t ≫ (SimplicialModel.KanReplacement.unit hcof hfib).app _

include hcof in
lemma extends_kanAction {K L : SSet.{v}} (i : K ⟶ L) [Mono i]
    (s : K ⟶ ResolutionLiftSpace.obj X X' f) (r : K ⟶ ResolutionLiftSpace.obj Y Y' g)
    (t : L ⟶ input X' Y') :
    ∃ (s' : L ⟶ ResolutionLiftSpace.obj X X' f) (r' : L ⟶ ResolutionLiftSpace.obj Y Y' g),
      i ≫ s' = s ∧ i ≫ r' = r ∧
        i ≫ kanAction X X' f Y Y' g hcof hfib s' r' t =
          kanAction X X' f Y Y' g hcof hfib s r (i ≫ t) := by
  obtain ⟨s', r', hs, hr, ha⟩ := extends_action X X' f Y Y' g hcof i s r t
  exact ⟨s', r', hs, hr, (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (SimplicialModel.KanReplacement.unit hcof hfib).app _) ha))⟩

end SerrePositivity.HomotopyFunctionComplex.MixedResolutionLiftAction
