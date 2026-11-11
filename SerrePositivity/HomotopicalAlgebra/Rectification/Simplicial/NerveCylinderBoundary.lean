module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NervePushoutBoundary
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramTensor

/-!
# 中断した任意モデル源への一般化：NerveCylinderBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The union of the entire endpoint and vertex boundaries of a moving cylinder。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0468][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0468
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The union of the entire endpoint and vertex boundaries of a moving cylinder
-/

@[expose] public section
universe w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.NerveCylinderBoundary
variable {D : Type uD} [Category.{vD} D]
  (V K : D ⥤ SSet.{w}) (i : V ⟶ K) {A T : SSet.{w}} (j : A ⟶ T)

abbrev boundary : D ⥤ SSet.{w} := pushout (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j V)
abbrev endpointInclusion : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K A ⟶ boundary V K i j := pushout.inl _ _
abbrev vertexInclusion : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V T ⟶ boundary V K i j := pushout.inr _ _

def inclusion : boundary V K i j ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K T :=
  pushout.desc (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j K) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.commute V K i j)

@[reassoc]
lemma endpointInclusion_inclusion : endpointInclusion V K i j ≫ inclusion V K i j =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j K := pushout.inl_desc _ _ _

@[reassoc]
lemma vertexInclusion_inclusion : vertexInclusion V K i j ≫ inclusion V K i j =
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i T := pushout.inr_desc _ _ _

/-- The evaluated functor-category boundary is the actual simplicial pushout-product. -/
def pushoutProduct (d : D) :
    (curriedTensor SSet.{w}).PushoutObjObj (i.app d) j where
  pt := (boundary V K i j).obj d
  inl := (endpointInclusion V K i j).app d
  inr := (vertexInclusion V K i j).app d
  isPushout := NervePushoutBoundary.square
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V T) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j V) d
  ι := (inclusion V K i j).app d
  inl_ι := congr_app (endpointInclusion_inclusion V K i j) d
  inr_ι := congr_app (vertexInclusion_inclusion V K i j) d

lemma inclusion_mono (hi : ∀ d, Mono (i.app d)) [Mono j] (d : D) :
    Mono ((inclusion V K i j).app d) := by
  let _ := hi d
  exact simplicial_pushoutProduct_mono (i.app d) j (pushoutProduct V K i j d)

variable (F : D ⥤ SSet.{w})
  (b : NerveBiparameter.System (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product K A) F)
  (c : NerveBiparameter.System (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.product V T) F)
  (h : b ≫ NerveBiparameterMaps.restriction _ _ F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i A) =
    c ≫ NerveBiparameterMaps.restriction _ _ F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j V))

/-- Glue both prescribed whole coherent boundary systems before extending the cylinder. -/
def system : NerveBiparameter.System (boundary V K i j) F :=
  NervePushoutBoundary.glue _ _ _ F (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.horizontal V K i A) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertical j V) b c h

lemma system_endpoints : system V K i j F b c h ≫
    NerveBiparameterMaps.restriction _ _ F (endpointInclusion V K i j) = b :=
  NervePushoutBoundary.glue_left _ _ _ _ _ _ _ _ _

lemma system_vertices : system V K i j F b c h ≫
    NerveBiparameterMaps.restriction _ _ F (vertexInclusion V K i j) = c :=
  NervePushoutBoundary.glue_right _ _ _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.NerveCylinderBoundary
