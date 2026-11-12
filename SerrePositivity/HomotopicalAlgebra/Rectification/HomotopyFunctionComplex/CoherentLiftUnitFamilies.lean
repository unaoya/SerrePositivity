module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftBaseChange
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftEdges

/-!
# 中断した任意モデル源への一般化：CoherentLiftUnitFamilies

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual unit comparison families after their base transports。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0074][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0074
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual unit comparison families after their base transports

Identity resolution maps and identity outer frame maps give the original
chosen interpolation on both sides. This does not assert a unit law for
independently chosen lifts of identity maps.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftUnitComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)

abbrev postCast := ResolutionLiftSpace.baseChange (Category.comp_id f)
abbrev preCast := ResolutionLiftSpace.baseChange (Category.id_comp f)

lemma post_tuple_unit : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X Y Y f (𝟙 Y)) ≫
    CoherentLiftBaseChange.tuples (Category.comp_id f) = 𝟙 (CoherentLiftTuples.obj X Y f) := by
  ext n a
  funext j
  apply Subtype.ext
  exact Category.comp_id _

lemma pre_tuple_unit : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X X Y (𝟙 X) f) ≫
    CoherentLiftBaseChange.tuples (Category.id_comp f) = 𝟙 (CoherentLiftTuples.obj X Y f) := by
  ext n a
  funext j
  apply Subtype.ext
  exact Category.id_comp _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

lemma post_left_unit : postLeft hcof X Y Y f (𝟙 Y) ≫ postCast X Y f =
    CoherentLiftTuples.interpolation hcof X Y f :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => CoherentLiftTuples.interpolation hcof X Y f ≫ k)
      (ResolutionLiftFunctorLaws.post_identity X Y f)).trans (Category.comp_id _))

lemma pre_left_unit : preLeft hcof X X Y (𝟙 X) f (ResolutionLiftPrecomposition.identity X) ≫
    preCast X Y f = CoherentLiftTuples.interpolation hcof X Y f :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => CoherentLiftTuples.interpolation hcof X Y f ≫ k)
      (ResolutionLiftFunctorLaws.pre_identity X Y f)).trans (Category.comp_id _))

lemma post_right_unit : postRight hcof X Y Y f (𝟙 Y) ≫ postCast X Y f =
    CoherentLiftTuples.interpolation hcof X Y f := by
  have hi := congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X Y Y f (𝟙 Y)) ≫ k)
    (CoherentLiftBaseChange.interpolation hcof (Category.comp_id f))
  have ht := congrArg (fun k => k ≫ CoherentLiftTuples.interpolation hcof X Y f)
    (post_tuple_unit X Y f)
  have he : CoherentLiftTuples.interpolation hcof X Y (f ≫ ResolutionObject.Hom.base (𝟙 Y)) =
      CoherentLiftTuples.interpolation hcof X Y (f ≫ 𝟙 Y.base) := rfl
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X Y Y f (𝟙 Y)) ≫
        CoherentLiftTuples.interpolation hcof X Y (f ≫ 𝟙 Y.base) ≫ postCast X Y f := by
      simpa only [postRight, Category.assoc] using
        congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X Y Y f (𝟙 Y)) ≫ k ≫ postCast X Y f) he
    _ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X Y Y f (𝟙 Y)) ≫
        CoherentLiftBaseChange.tuples (Category.comp_id f) ≫
          CoherentLiftTuples.interpolation hcof X Y f := by
      simpa only [postCast, Category.assoc] using hi
    _ = (𝟙 _) ≫ CoherentLiftTuples.interpolation hcof X Y f := by
      simpa only [Category.assoc] using ht
    _ = _ := Category.id_comp _

lemma pre_right_unit : preRight hcof X X Y (𝟙 X) f ≫ preCast X Y f =
    CoherentLiftTuples.interpolation hcof X Y f := by
  have hi := congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X X Y (𝟙 X) f) ≫ k)
    (CoherentLiftBaseChange.interpolation hcof (Category.id_comp f))
  have ht := congrArg (fun k => k ≫ CoherentLiftTuples.interpolation hcof X Y f)
    (pre_tuple_unit X Y f)
  have he : CoherentLiftTuples.interpolation hcof X Y (ResolutionObject.Hom.base (𝟙 X) ≫ f) =
      CoherentLiftTuples.interpolation hcof X Y (𝟙 X.base ≫ f) := rfl
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X X Y (𝟙 X) f) ≫
        CoherentLiftTuples.interpolation hcof X Y (𝟙 X.base ≫ f) ≫ preCast X Y f := by
      simpa only [preRight, Category.assoc] using
        congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X X Y (𝟙 X) f) ≫ k ≫ preCast X Y f) he
    _ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X X Y (𝟙 X) f) ≫
        CoherentLiftBaseChange.tuples (Category.id_comp f) ≫
          CoherentLiftTuples.interpolation hcof X Y f := by
      simpa only [preCast, Category.assoc] using hi
    _ = (𝟙 _) ≫ CoherentLiftTuples.interpolation hcof X Y f := by
      simpa only [Category.assoc] using ht
    _ = _ := Category.id_comp _

include hcof in
lemma post_boundary_unit : postBoundary X Y Y f (𝟙 Y) ≫ postCast X Y f = vertexData X Y f := by
  calc
    _ = (vertexInclusion X Y f ≫ postLeft hcof X Y Y f (𝟙 Y)) ≫ postCast X Y f :=
      congrArg (fun k => k ≫ postCast X Y f) (postLeft_vertices hcof X Y Y f (𝟙 Y)).symm
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun k => vertexInclusion X Y f ≫ k) (post_left_unit X Y f hcof)).trans
        (CoherentLiftTuples.interpolation_vertices hcof X Y f))

include hcof in
lemma pre_boundary_unit : preBoundary X X Y (𝟙 X) f ≫ preCast X Y f = vertexData X Y f := by
  calc
    _ = (vertexInclusion X Y f ≫
        preLeft hcof X X Y (𝟙 X) f (ResolutionLiftPrecomposition.identity X)) ≫ preCast X Y f :=
      congrArg (fun k => k ≫ preCast X Y f)
        (preLeft_vertices hcof X X Y (𝟙 X) f (ResolutionLiftPrecomposition.identity X)).symm
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun k => vertexInclusion X Y f ≫ k) (pre_left_unit X Y f hcof)).trans
        (CoherentLiftTuples.interpolation_vertices hcof X Y f))

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftUnitComparison
