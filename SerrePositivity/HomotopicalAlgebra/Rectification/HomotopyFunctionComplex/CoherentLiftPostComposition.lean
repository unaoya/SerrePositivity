module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftBaseChange
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftEdges
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceBoundary

/-!
# 中断した任意モデル源への一般化：CoherentLiftPostComposition

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The prescribed composition triangle for two postcomposition comparisons。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0069][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0069
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The prescribed composition triangle for two postcomposition comparisons

The three edges are the previously selected comparisons, transported to
one fixed-boundary choice space. Their compatibility is proved from actual
composition laws and endpoint formulas, not required as new input data.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftPostComposition
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X Y W V : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) (h : W ⟶ V)

abbrev castMap := ResolutionLiftSpace.baseChange (Category.assoc f g.base h.base)
abbrev tailMap := ResolutionLiftPostcomposition.map X W V (f ≫ g.base) h ≫ castMap X Y W V f g h

lemma left_composite : postLeft hcof X Y W f g ≫ tailMap X Y W V f g h =
    postLeft hcof X Y V f (g ≫ h) := by
  change (_ ≫ _) ≫ (_ ≫ _) = _ ≫ _
  rw [Category.assoc, ResolutionLiftFunctorLaws.post_compose]

include hcof in
lemma boundary_composite : postBoundary X Y W f g ≫ tailMap X Y W V f g h =
    postBoundary X Y V f (g ≫ h) := by
  calc
    _ = (vertexInclusion X Y f ≫ postLeft hcof X Y W f g) ≫ tailMap X Y W V f g h :=
      congrArg (fun k => k ≫ tailMap X Y W V f g h) (postLeft_vertices hcof X Y W f g).symm
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun k => vertexInclusion X Y f ≫ k) (left_composite hcof X Y W V f g h)).trans
        (postLeft_vertices hcof X Y V f (g ≫ h)))

abbrev firstMap : postChoiceSpace X Y W f g ⟶ postChoiceSpace X Y V f (g ≫ h) :=
  RelativeChoiceSpace.postMap (vertexInclusion X Y f) _ _ (tailMap X Y W V f g h)
    (boundary_composite hcof X Y W V f g h)

abbrev middle := postRight hcof X Y W f g ≫ tailMap X Y W V f g h

lemma middle_vertices : vertexInclusion X Y f ≫ middle hcof X Y W V f g h =
    postBoundary X Y V f (g ≫ h) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ tailMap X Y W V f g h) (postRight_vertices hcof X Y W f g)).trans
      (boundary_composite hcof X Y W V f g h))

abbrev middlePoint := RelativeChoiceSpace.ofExtension (vertexInclusion X Y f)
  (postBoundary X Y V f (g ≫ h)) (middle hcof X Y W V f g h)
  (middle_vertices hcof X Y W V f g h)

abbrev firstEdge := postEdge hcof hfib X Y W f g ≫ firstMap hcof X Y W V f g h

lemma firstEdge_at_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ firstEdge hcof hfib X Y W V f g h =
    postLeftPoint hcof X Y V f (g ≫ h) := by
  rw [firstEdge, ← Category.assoc, postEdge_at_zero]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ RelativeChoiceSpace.postMap _ _ _ _ _ = _
  rw [RelativeChoiceSpace.postMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (left_composite hcof X Y W V f g h)

lemma firstEdge_at_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ firstEdge hcof hfib X Y W V f g h =
    middlePoint hcof X Y W V f g h := by
  rw [firstEdge, ← Category.assoc, postEdge_at_one]
  exact RelativeChoiceSpace.postMap_ofExtension _ _ _ _ _ _ _

abbrev tupleMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X Y W f g)
abbrev vertexMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.verticesMap (postStrict X Y W f g)

omit [ModelCategory SSet.{v}] in
lemma tuple_composite : tupleMap X Y W f g ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X W V (f ≫ g.base) h) ≫
    CoherentLiftBaseChange.tuples (Category.assoc f g.base h.base) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X Y V f (g ≫ h)) := by
  ext n a
  funext i
  apply Subtype.ext
  exact Category.assoc _ _ _

lemma right_composite : tupleMap X Y W f g ≫ postRight hcof X W V (f ≫ g.base) h ≫
    castMap X Y W V f g h = postRight hcof X Y V f (g ≫ h) := by
  have hi := congrArg (fun k => tupleMap X Y W f g ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X W V (f ≫ g.base) h) ≫ k)
      (CoherentLiftBaseChange.interpolation hcof (Category.assoc f g.base h.base))
  have ht := congrArg (fun k => k ≫ CoherentLiftTuples.interpolation hcof X V (f ≫ g.base ≫ h.base))
    (tuple_composite X Y W V f g h)
  have he : CoherentLiftTuples.interpolation hcof X V (f ≫ g.base ≫ h.base) =
      CoherentLiftTuples.interpolation hcof X V (f ≫ (g ≫ h).base) := rfl
  calc
    _ = tupleMap X Y W f g ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X W V (f ≫ g.base) h) ≫
        CoherentLiftBaseChange.tuples (Category.assoc f g.base h.base) ≫
          CoherentLiftTuples.interpolation hcof X V (f ≫ g.base ≫ h.base) := by
      simpa only [postRight, Category.assoc] using hi
    _ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X Y V f (g ≫ h)) ≫
        CoherentLiftTuples.interpolation hcof X V (f ≫ g.base ≫ h.base) := by
      simpa only [Category.assoc] using ht
    _ = _ := congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (postStrict X Y V f (g ≫ h)) ≫ k) he

lemma middle_composite : tupleMap X Y W f g ≫ postLeft hcof X W V (f ≫ g.base) h ≫
    castMap X Y W V f g h = middle hcof X Y W V f g h := by
  simp only [middle, postLeft, postRight, tailMap, Category.assoc]

omit [ModelCategory SSet.{v}] in
lemma vertex_square : vertexInclusion X Y f ≫ tupleMap X Y W f g =
    vertexMap X Y W f g ≫ vertexInclusion X W (f ≫ g.base) := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion_map _

include hcof in
lemma second_boundary : vertexMap X Y W f g ≫
    (postBoundary X W V (f ≫ g.base) h ≫ castMap X Y W V f g h) =
      postBoundary X Y V f (g ≫ h) := by
  calc
    _ = vertexMap X Y W f g ≫ (vertexInclusion X W (f ≫ g.base) ≫
        postRight hcof X W V (f ≫ g.base) h) ≫ castMap X Y W V f g h :=
      congrArg (fun k => vertexMap X Y W f g ≫ k ≫ castMap X Y W V f g h)
        (postRight_vertices hcof X W V (f ≫ g.base) h).symm
    _ = vertexInclusion X Y f ≫ tupleMap X Y W f g ≫
        postRight hcof X W V (f ≫ g.base) h ≫ castMap X Y W V f g h := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ postRight hcof X W V (f ≫ g.base) h ≫ castMap X Y W V f g h)
          (vertex_square X Y W f g).symm
    _ = _ := (congrArg (fun k => vertexInclusion X Y f ≫ k)
      (right_composite hcof X Y W V f g h)).trans (postRight_vertices hcof X Y V f (g ≫ h))

abbrev secondMap : postChoiceSpace X W V (f ≫ g.base) h ⟶ postChoiceSpace X Y V f (g ≫ h) :=
  RelativeChoiceSpace.postMap (vertexInclusion X W (f ≫ g.base)) _ _
      (castMap X Y W V f g h) rfl ≫
    RelativeChoiceSpace.preMap (vertexInclusion X W (f ≫ g.base)) _ (vertexInclusion X Y f) _
      (vertexMap X Y W f g) (tupleMap X Y W f g) (vertex_square X Y W f g)
      (second_boundary hcof X Y W V f g h)

abbrev secondEdge := postEdge hcof hfib X W V (f ≫ g.base) h ≫ secondMap hcof X Y W V f g h

lemma secondEdge_at_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ secondEdge hcof hfib X Y W V f g h =
    middlePoint hcof X Y W V f g h := by
  rw [secondEdge, ← Category.assoc, postEdge_at_zero]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, RelativeChoiceSpace.postMap_ofExtension,
    RelativeChoiceSpace.preMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (middle_composite hcof X Y W V f g h)

lemma secondEdge_at_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ secondEdge hcof hfib X Y W V f g h =
    postRightPoint hcof X Y V f (g ≫ h) := by
  rw [secondEdge, ← Category.assoc, postEdge_at_one]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, RelativeChoiceSpace.postMap_ofExtension,
    RelativeChoiceSpace.preMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (right_composite hcof X Y W V f g h)

abbrev faces : Fin 3 → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶
    postChoiceSpace X Y V f (g ≫ h)) :=
  ![secondEdge hcof hfib X Y W V f g h, postEdge hcof hfib X Y V f (g ≫ h),
    firstEdge hcof hfib X Y W V f g h]

/-- All three compatibility equations follow from the actual selected endpoints. -/
lemma faces_compatible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.StandardCompatible (faces hcof hfib X Y W V f g h) := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> norm_num at hjk
  · exact (secondEdge_at_one hcof hfib X Y W V f g h).trans
      (postEdge_at_one hcof hfib X Y V f (g ≫ h)).symm
  · exact (secondEdge_at_zero hcof hfib X Y W V f g h).trans
      (firstEdge_at_one hcof hfib X Y W V f g h).symm
  · exact (postEdge_at_zero hcof hfib X Y V f (g ≫ h)).trans
      (firstEdge_at_zero hcof hfib X Y W V f g h).symm

/-- A prescribed composition triangle retaining the previously selected edges. -/
def triangle : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶
    postChoiceSpace X Y V f (g ≫ h) :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib (vertexInclusion X Y f)
    (postBoundary X Y V f (g ≫ h)) (ResolutionLiftSpace.projection X V (f ≫ (g ≫ h).base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V (f ≫ (g ≫ h).base)) 0
    (faces hcof hfib X Y W V f g h) (faces_compatible hcof hfib X Y W V f g h)).choose

@[reassoc (attr := simp)]
lemma triangle_face (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ triangle hcof hfib X Y W V f g h = faces hcof hfib X Y W V f g h k :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib (vertexInclusion X Y f)
    (postBoundary X Y V f (g ≫ h)) (ResolutionLiftSpace.projection X V (f ≫ (g ≫ h).base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V (f ≫ (g ≫ h).base)) 0
    (faces hcof hfib X Y W V f g h) (faces_compatible hcof hfib X Y W V f g h)).choose_spec.1 k

lemma triangle_fixed_boundary :
    vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ≫
        RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f (g ≫ h))
          (triangle hcof hfib X Y W V f g h) =
      vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ postBoundary X Y V f (g ≫ h) :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib (vertexInclusion X Y f)
    (postBoundary X Y V f (g ≫ h)) (ResolutionLiftSpace.projection X V (f ≫ (g ≫ h).base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V (f ≫ (g ≫ h).base)) 0
    (faces hcof hfib X Y W V f g h) (faces_compatible hcof hfib X Y W V f g h)).choose_spec.2

lemma triangle_action_face (Z : C)
    (t : CoherentLiftTuples.obj X Y f ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom V.resolution.obj).obj Z) (k : Fin 3) :
    CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.δ k ≫
        KanLiftAction.parameterized hcof hfib X V (f ≫ (g ≫ h).base) Z
          (RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f (g ≫ h))
            (triangle hcof hfib X Y W V f g h)) t =
      KanLiftAction.parameterized hcof hfib X V (f ≫ (g ≫ h).base) Z
        (RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y V f (g ≫ h))
          (faces hcof hfib X Y W V f g h k))
        ((CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.δ k) ≫ t) := by
  rw [KanLiftAction.parameterized_naturality, ← RelativeChoiceSpace.family_naturality,
    triangle_face]

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftPostComposition
