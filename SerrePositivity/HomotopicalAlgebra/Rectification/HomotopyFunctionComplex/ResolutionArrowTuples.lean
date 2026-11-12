module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowDiagram
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftTuples
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuplesFunctor

/-!
# 中断した任意モデル源への一般化：ResolutionArrowTuples

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The old strict lift tuple and vertex boundary diagrams over all centers。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0287][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0287
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The old strict lift tuple and vertex boundary diagrams over all centers
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.ResolutionArrowDiagram

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTuples
variable (C : Type u) [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

abbrev StrictLift (q : Index C) := CoherentLiftTuples.StrictLift (source C q).inner
  (target C q) (arrow C q)

def strictMap {q r : Index C} (f : q ⟶ r) (k : StrictLift C q) : StrictLift C r :=
  ⟨f.hom.1.unop.map ≫ k.val ≫ f.hom.2, by
    change f.hom.1.unop.map.base ≫ (k.val.base ≫ f.hom.2.base) = arrow C r
    rw [k.property, ← Category.assoc]
    exact equation C f⟩

def strictLifts : Index C ⥤ Type v where
  obj := StrictLift C
  map f := ↾(strictMap C f)
  map_id q := by
    ext k
    change (𝟙 _) ≫ k.val ≫ (𝟙 _) = k.val
    simp only [Category.id_comp, Category.comp_id]
  map_comp f g := by
    ext k
    change (_ ≫ _) ≫ k.val ≫ (_ ≫ _) = _ ≫ (_ ≫ k.val ≫ _) ≫ _
    simp only [Category.assoc]

abbrev tuples : Index C ⥤ SSet.{v} := strictLifts C ⋙ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.tupleFunctor
abbrev vertices : Index C ⥤ SSet.{v} := strictLifts C ⋙ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.vertexFunctor
abbrev inclusion : vertices C ⟶ tuples C := Functor.whiskerLeft (strictLifts C)
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.inclusionNatTrans

abbrev point (q : Index C) (k : StrictLift C q) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ (fibers C).obj q :=
  CoherentLiftTuples.point (source C q).inner (target C q) (arrow C q) k

lemma point_inclusion (q : Index C) (k : StrictLift C q) : point C q k ≫
    ResolutionLiftSpace.inclusion (source C q).inner (target C q) (arrow C q) =
    LiftSpace.point (ResolutionLiftSpace.frame (source C q).inner).obj
      (ResolutionLiftSpace.frame (source C q).inner).augmentation k.val.diagram := by
  have h (X Y : ResolutionObject C) (g : X.base ⟶ Y.base)
      (k : CoherentLiftTuples.StrictLift X Y g) : CoherentLiftTuples.point X Y g k ≫
        ResolutionLiftSpace.inclusion X Y g =
      LiftSpace.point (ResolutionLiftSpace.frame X).obj
        (ResolutionLiftSpace.frame X).augmentation k.val.diagram := by
    rcases k with ⟨k, rfl⟩
    exact LiftSpace.ofLift_inclusion _ _ _ _ k.diagram k.over
  exact h _ _ _ k

lemma point_naturality {q r : Index C} (f : q ⟶ r) (k : StrictLift C q) :
    point C q k ≫ (fibers C).map f = point C r (strictMap C f k) := by
  apply ResolutionLiftSpace.hom_ext
  · change (point C q k ≫ (fibers C).map f) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.inclusion (rawProjection C) (basepoint C)).app r =
      point C r (strictMap C f k) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FiberFunctor.inclusion (rawProjection C) (basepoint C)).app r
    rw [Category.assoc, map_inclusion, ← Category.assoc]
    change (point C q k ≫ ResolutionLiftSpace.inclusion _ _ _) ≫
        MixedChoiceFunctor.rawPairs.map f.hom =
      point C r (strictMap C f k) ≫ ResolutionLiftSpace.inclusion _ _ _
    apply (congrArg (fun z => z ≫ MixedChoiceFunctor.rawPairs.map f.hom)
      (point_inclusion C q k)).trans
    apply Eq.trans ?_ (point_inclusion C r (strictMap C f k)).symm
    have hp := LiftSpacePrecomposition.point
      (ResolutionLiftSpace.frame (source C r).inner).obj
      (ResolutionLiftSpace.frame (source C q).inner).obj
      (ResolutionLiftSpace.frame (source C r).inner).augmentation
      (ResolutionLiftSpace.frame (source C q).inner).augmentation
      f.hom.1.unop.map.diagram f.hom.1.unop.frame f.hom.1.unop.over
      (f.hom.1.unop.map.diagram ≫ k.val.diagram) k.val.diagram rfl
    change (LiftSpace.point _ _ k.val.diagram ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap f.hom.1.unop.frame).app _) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (ResolutionLiftSpace.frame (source C r).inner).obj).map
            f.hom.2.diagram = _
    rw [hp, LiftSpace.point_postcomp]
    exact congrArg (LiftSpace.point _ _) (Category.assoc _ _ _)
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The full old strict-vertex boundary is natural across every center change. -/
def vertexData : vertices C ⟶ fibers C where
  app q := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap (point C q)
  naturality {q r} f := by
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.verticesMap (strictMap C f) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap (point C r) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap (point C q) ≫ (fibers C).map f
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.verticesMap_pointsMap, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap_postcomp]
    exact congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap (funext (fun k => (point_naturality C f k).symm))

instance inclusion_mono (q : Index C) : Mono ((inclusion C).app q) :=
  inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion (StrictLift C q)))

end SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTuples
