module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.FixedBoundaryExtensions

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceSpace
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftPrecomposition

/-!
# 中断した任意モデル源への一般化：CoherentLiftRelative

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Relative comparisons of whole coherent lift families。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0071][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0071
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative comparisons of whole coherent lift families

All strict lift vertices stay fixed throughout the comparison parameter.
Precomposing or postcomposing a chosen interpolation is compared with
interpolating the composed strict lifts, relative to every strict vertex.
The space of such relative comparisons has fillers in all dimensions.
This does not yet constitute simultaneous composition-coherent descent
to a strict functor on the original model category.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev vertices (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) : SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.vertices (CoherentLiftTuples.StrictLift X Y f)

abbrev vertexInclusion (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    vertices X Y f ⟶ CoherentLiftTuples.obj X Y f :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion _

abbrev vertexData (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    vertices X Y f ⟶ ResolutionLiftSpace.obj X Y f :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap (CoherentLiftTuples.point X Y f)

/-- The actual space of all interpolations retaining all strict lift vertices. -/
abbrev obj (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) : SSet.{v} :=
  SimplicialModel.RelativeChoiceSpace.obj (vertexInclusion X Y f) (vertexData X Y f)

abbrev chosenPoint (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ obj X Y f :=
  SimplicialModel.RelativeChoiceSpace.ofExtension _ _ (CoherentLiftTuples.interpolation hcof X Y f)
    (CoherentLiftTuples.interpolation_vertices hcof X Y f)

include hcof hfib in
lemma projection_trivialFibration (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    trivialFibrations SSet.{v}
      (SimplicialModel.RelativeChoiceSpace.projection (vertexInclusion X Y f) (vertexData X Y f)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.projection_trivialFibration hcof hfib _ _
    (ResolutionLiftSpace.projection X Y f)
    (ResolutionLiftSpace.projection_trivialFibration hcof X Y f)

def postStrict (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W)
    (k : CoherentLiftTuples.StrictLift X Y f) : CoherentLiftTuples.StrictLift X W (f ≫ g.base) :=
  ⟨k.val ≫ g, by change k.val.base ≫ g.base = f ≫ g.base; rw [k.property]⟩

omit [ModelCategory SSet.{v}] in
lemma point_post (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W)
    (k : CoherentLiftTuples.StrictLift X Y f) :
    CoherentLiftTuples.point X Y f k ≫ ResolutionLiftPostcomposition.map X Y W f g =
      CoherentLiftTuples.point X W (f ≫ g.base) (postStrict X Y W f g k) := by
  rcases k with ⟨k, rfl⟩
  exact ResolutionLiftPostcomposition.ofLift k g

abbrev postBoundary (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    vertices X Y f ⟶ ResolutionLiftSpace.obj X W (f ≫ g.base) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap
    (fun k => CoherentLiftTuples.point X W (f ≫ g.base) (postStrict X Y W f g k))

abbrev postLeft (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    CoherentLiftTuples.obj X Y f ⟶ ResolutionLiftSpace.obj X W (f ≫ g.base) :=
  CoherentLiftTuples.interpolation hcof X Y f ≫ ResolutionLiftPostcomposition.map X Y W f g

abbrev postRight (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    CoherentLiftTuples.obj X Y f ⟶ ResolutionLiftSpace.obj X W (f ≫ g.base) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X Y W f g) ≫
    CoherentLiftTuples.interpolation hcof X W (f ≫ g.base)

lemma postLeft_vertices (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    vertexInclusion X Y f ≫ postLeft hcof X Y W f g = postBoundary X Y W f g := by
  rw [postLeft, ← Category.assoc, CoherentLiftTuples.interpolation_vertices,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap_postcomp]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap (funext (point_post X Y W f g))

lemma postRight_vertices (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    vertexInclusion X Y f ≫ postRight hcof X Y W f g = postBoundary X Y W f g := by
  rw [postRight, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion_map, Category.assoc,
    CoherentLiftTuples.interpolation_vertices, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.verticesMap_pointsMap]

/-- Relative comparison choices for postcomposition form another actual simplicial set. -/
abbrev postChoiceSpace (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) : SSet.{v} :=
  SimplicialModel.RelativeChoiceSpace.obj (vertexInclusion X Y f) (postBoundary X Y W f g)

include hcof hfib in
lemma postChoiceSpace_extension (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W)
    {K L : SSet.{v}} (j : K ⟶ L) [Mono j] (a : K ⟶ postChoiceSpace X Y W f g) :
    ∃ e : L ⟶ postChoiceSpace X Y W f g, j ≫ e = a :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.extension hcof hfib _ _
    (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base)) j a

include hfib in
/-- Postcomposition of a whole chosen interpolation is homotopic to the
chosen interpolation of postcomposed lifts, relative to every strict lift. -/
lemma post_relative_homotopy (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    ∃ H : CoherentLiftTuples.obj X Y f ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶
        ResolutionLiftSpace.obj X W (f ≫ g.base),
      CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ H =
        CoherentLiftTuples.obj X Y f ◁ SimplicialModel.RelativeChoiceSpace.pointUnitIso.hom ≫
          (ρ_ _).hom ≫ postLeft hcof X Y W f g ∧
      CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ H =
        CoherentLiftTuples.obj X Y f ◁ SimplicialModel.RelativeChoiceSpace.pointUnitIso.hom ≫
          (ρ_ _).hom ≫ postRight hcof X Y W f g ∧
      vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ≫ H =
        vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
          SimplicialModel.RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
            postBoundary X Y W f g :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.relative_homotopy hcof hfib _ _
    (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base)) _ _
    (postLeft_vertices hcof X Y W f g) (postRight_vertices hcof X Y W f g)

def preStrict (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (k : CoherentLiftTuples.StrictLift Y W g) : CoherentLiftTuples.StrictLift X W (f.base ≫ g) :=
  ⟨f ≫ k.val, by change f.base ≫ k.val.base = f.base ≫ g; rw [k.property]⟩

omit [ModelCategory SSet.{v}] in
lemma point_pre (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) (k : CoherentLiftTuples.StrictLift Y W g) :
    CoherentLiftTuples.point Y W g k ≫ ResolutionLiftPrecomposition.map X Y W f g φ =
      CoherentLiftTuples.point X W (f.base ≫ g) (preStrict X Y W f g k) := by
  rcases k with ⟨k, rfl⟩
  exact ResolutionLiftPrecomposition.ofLift f k φ

abbrev preBoundary (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) :
    vertices Y W g ⟶ ResolutionLiftSpace.obj X W (f.base ≫ g) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap
    (fun k => CoherentLiftTuples.point X W (f.base ≫ g) (preStrict X Y W f g k))

abbrev preLeft (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    CoherentLiftTuples.obj Y W g ⟶ ResolutionLiftSpace.obj X W (f.base ≫ g) :=
  CoherentLiftTuples.interpolation hcof Y W g ≫ ResolutionLiftPrecomposition.map X Y W f g φ

abbrev preRight (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) :
    CoherentLiftTuples.obj Y W g ⟶ ResolutionLiftSpace.obj X W (f.base ≫ g) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X Y W f g) ≫
    CoherentLiftTuples.interpolation hcof X W (f.base ≫ g)

lemma preLeft_vertices (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    vertexInclusion Y W g ≫ preLeft hcof X Y W f g φ = preBoundary X Y W f g := by
  rw [preLeft, ← Category.assoc, CoherentLiftTuples.interpolation_vertices,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap_postcomp]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap (funext (point_pre X Y W f g φ))

lemma preRight_vertices (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) :
    vertexInclusion Y W g ≫ preRight hcof X Y W f g = preBoundary X Y W f g := by
  rw [preRight, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion_map, Category.assoc,
    CoherentLiftTuples.interpolation_vertices, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.verticesMap_pointsMap]

abbrev preChoiceSpace (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) : SSet.{v} :=
  SimplicialModel.RelativeChoiceSpace.obj (vertexInclusion Y W g) (preBoundary X Y W f g)

include hcof hfib in
lemma preChoiceSpace_extension (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    {K L : SSet.{v}} (j : K ⟶ L) [Mono j] (a : K ⟶ preChoiceSpace X Y W f g) :
    ∃ e : L ⟶ preChoiceSpace X Y W f g, j ≫ e = a :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.extension hcof hfib _ _
    (ResolutionLiftSpace.projection X W (f.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f.base ≫ g)) j a

include hfib in
lemma pre_relative_homotopy (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    Nonempty (SimplicialModel.RelativeChoiceSpace.FixedBoundaryHomotopy
      (vertexInclusion Y W g) (preBoundary X Y W f g)
      (preLeft hcof X Y W f g φ) (preRight hcof X Y W f g)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.nonempty_fixedBoundaryHomotopy hcof hfib _ _
    (ResolutionLiftSpace.projection X W (f.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f.base ≫ g)) _ _
    (preLeft_vertices hcof X Y W f g φ) (preRight_vertices hcof X Y W f g)

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
