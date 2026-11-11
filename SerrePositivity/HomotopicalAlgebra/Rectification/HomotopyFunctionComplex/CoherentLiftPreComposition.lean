module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftBaseChange
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftEdges
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceBoundary

/-!
# 中断した任意モデル源への一般化：CoherentLiftPreComposition

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The selected comparison triangle for two actual source frame maps。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0070][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0070
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The selected comparison triangle for two actual source frame maps

The two previously selected precomposition comparisons and the comparison
for their actual composite are transported to one relative choice space.
Their endpoint equations prove the boundary compatibility. No compatibility
of independently chosen outer lifts is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftPreComposition
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X Y W V : ResolutionObject C) (f : X ⟶ Y) (g : Y ⟶ W) (h : W.base ⟶ V.base)
  (φ : ResolutionLiftPrecomposition.FrameMap f) (ψ : ResolutionLiftPrecomposition.FrameMap g)

abbrev castMap := ResolutionLiftSpace.baseChange (Category.assoc f.base g.base h).symm
abbrev tailMap := ResolutionLiftPrecomposition.map X Y V f (g.base ≫ h) φ ≫ castMap X Y W V f g h

omit [ModelCategory SSet.{v}] in
lemma actual_composite : ResolutionLiftPrecomposition.map Y W V g h ψ ≫
    tailMap X Y W V f g h φ =
      ResolutionLiftPrecomposition.map X W V (f ≫ g) h
        (ResolutionLiftPrecomposition.compose φ ψ) := by
  have hc := congrArg (fun k => k ≫ castMap X Y W V f g h)
    (ResolutionLiftFunctorLaws.pre_compose X Y W V f g h φ ψ)
  calc
    _ = (ResolutionLiftPrecomposition.map Y W V g h ψ ≫
        ResolutionLiftPrecomposition.map X Y V f (g.base ≫ h) φ) ≫ castMap X Y W V f g h :=
      (Category.assoc _ _ _).symm
    _ = _ := hc.trans (by
      simp only [Category.assoc, castMap, ResolutionLiftSpace.baseChange_symm, Category.comp_id])

lemma left_composite : preLeft hcof Y W V g h ψ ≫ tailMap X Y W V f g h φ =
    preLeft hcof X W V (f ≫ g) h (ResolutionLiftPrecomposition.compose φ ψ) := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => CoherentLiftTuples.interpolation hcof W V h ≫ k)
      (actual_composite X Y W V f g h φ ψ))

include hcof ψ in
lemma boundary_composite : preBoundary Y W V g h ≫ tailMap X Y W V f g h φ =
    preBoundary X W V (f ≫ g) h := by
  calc
    _ = (vertexInclusion W V h ≫ preLeft hcof Y W V g h ψ) ≫ tailMap X Y W V f g h φ :=
      congrArg (fun k => k ≫ tailMap X Y W V f g h φ) (preLeft_vertices hcof Y W V g h ψ).symm
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun k => vertexInclusion W V h ≫ k) (left_composite hcof X Y W V f g h φ ψ)).trans
        (preLeft_vertices hcof X W V (f ≫ g) h (ResolutionLiftPrecomposition.compose φ ψ)))

abbrev firstMap : preChoiceSpace Y W V g h ⟶ preChoiceSpace X W V (f ≫ g) h :=
  RelativeChoiceSpace.postMap (vertexInclusion W V h) _ _ (tailMap X Y W V f g h φ)
    (boundary_composite hcof X Y W V f g h φ ψ)

abbrev middle := preRight hcof Y W V g h ≫ tailMap X Y W V f g h φ

include ψ in
lemma middle_vertices : vertexInclusion W V h ≫ middle hcof X Y W V f g h φ =
    preBoundary X W V (f ≫ g) h :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ tailMap X Y W V f g h φ) (preRight_vertices hcof Y W V g h)).trans
      (boundary_composite hcof X Y W V f g h φ ψ))

abbrev middlePoint := RelativeChoiceSpace.ofExtension (vertexInclusion W V h)
  (preBoundary X W V (f ≫ g) h) (middle hcof X Y W V f g h φ)
    (middle_vertices hcof X Y W V f g h φ ψ)

abbrev firstEdge := preEdge hcof hfib Y W V g h ψ ≫ firstMap hcof X Y W V f g h φ ψ

lemma firstEdge_at_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ firstEdge hcof hfib X Y W V f g h φ ψ =
    preLeftPoint hcof X W V (f ≫ g) h (ResolutionLiftPrecomposition.compose φ ψ) := by
  rw [firstEdge, ← Category.assoc, preEdge_at_zero]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ RelativeChoiceSpace.postMap _ _ _ _ _ = _
  rw [RelativeChoiceSpace.postMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (left_composite hcof X Y W V f g h φ ψ)

lemma firstEdge_at_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ firstEdge hcof hfib X Y W V f g h φ ψ =
    middlePoint hcof X Y W V f g h φ ψ := by
  rw [firstEdge, ← Category.assoc, preEdge_at_one]
  exact RelativeChoiceSpace.postMap_ofExtension _ _ _ _ _ _ _

abbrev tupleMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict Y W V g h)
abbrev vertexMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.verticesMap (preStrict Y W V g h)

omit [ModelCategory SSet.{v}] in
lemma tuple_composite : tupleMap Y W V g h ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X Y V f (g.base ≫ h)) ≫
    CoherentLiftBaseChange.tuples (Category.assoc f.base g.base h).symm =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X W V (f ≫ g) h) := by
  ext n a
  funext i
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

lemma right_composite : tupleMap Y W V g h ≫ preRight hcof X Y V f (g.base ≫ h) ≫
    castMap X Y W V f g h = preRight hcof X W V (f ≫ g) h := by
  have hi := congrArg (fun k => tupleMap Y W V g h ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X Y V f (g.base ≫ h)) ≫ k)
      (CoherentLiftBaseChange.interpolation hcof (Category.assoc f.base g.base h).symm)
  have ht := congrArg (fun k => k ≫
    CoherentLiftTuples.interpolation hcof X V ((f.base ≫ g.base) ≫ h))
      (tuple_composite X Y W V f g h)
  have he : CoherentLiftTuples.interpolation hcof X V ((f.base ≫ g.base) ≫ h) =
      CoherentLiftTuples.interpolation hcof X V ((f ≫ g).base ≫ h) := rfl
  calc
    _ = tupleMap Y W V g h ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X Y V f (g.base ≫ h)) ≫
        CoherentLiftBaseChange.tuples (Category.assoc f.base g.base h).symm ≫
          CoherentLiftTuples.interpolation hcof X V ((f.base ≫ g.base) ≫ h) := by
      simpa only [preRight, Category.assoc] using hi
    _ = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X W V (f ≫ g) h) ≫
        CoherentLiftTuples.interpolation hcof X V ((f.base ≫ g.base) ≫ h) := by
      simpa only [Category.assoc] using ht
    _ = _ := congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.map (preStrict X W V (f ≫ g) h) ≫ k) he

lemma middle_composite : tupleMap Y W V g h ≫ preLeft hcof X Y V f (g.base ≫ h) φ ≫
    castMap X Y W V f g h = middle hcof X Y W V f g h φ := by
  simp only [middle, preLeft, preRight, tailMap, Category.assoc]

omit [ModelCategory SSet.{v}] in
lemma vertex_square : vertexInclusion W V h ≫ tupleMap Y W V g h =
    vertexMap Y W V g h ≫ vertexInclusion Y V (g.base ≫ h) := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion_map _

include hcof in
lemma second_boundary : vertexMap Y W V g h ≫
    (preBoundary X Y V f (g.base ≫ h) ≫ castMap X Y W V f g h) =
      preBoundary X W V (f ≫ g) h := by
  calc
    _ = vertexMap Y W V g h ≫ (vertexInclusion Y V (g.base ≫ h) ≫
        preRight hcof X Y V f (g.base ≫ h)) ≫ castMap X Y W V f g h :=
      congrArg (fun k => vertexMap Y W V g h ≫ k ≫ castMap X Y W V f g h)
        (preRight_vertices hcof X Y V f (g.base ≫ h)).symm
    _ = vertexInclusion W V h ≫ tupleMap Y W V g h ≫
        preRight hcof X Y V f (g.base ≫ h) ≫ castMap X Y W V f g h := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ preRight hcof X Y V f (g.base ≫ h) ≫ castMap X Y W V f g h)
          (vertex_square Y W V g h).symm
    _ = _ := (congrArg (fun k => vertexInclusion W V h ≫ k)
      (right_composite hcof X Y W V f g h)).trans (preRight_vertices hcof X W V (f ≫ g) h)

abbrev secondMap : preChoiceSpace X Y V f (g.base ≫ h) ⟶ preChoiceSpace X W V (f ≫ g) h :=
  RelativeChoiceSpace.postMap (vertexInclusion Y V (g.base ≫ h)) _ _
      (castMap X Y W V f g h) rfl ≫
    RelativeChoiceSpace.preMap (vertexInclusion Y V (g.base ≫ h)) _ (vertexInclusion W V h) _
      (vertexMap Y W V g h) (tupleMap Y W V g h) (vertex_square Y W V g h)
      (second_boundary hcof X Y W V f g h)

abbrev secondEdge := preEdge hcof hfib X Y V f (g.base ≫ h) φ ≫ secondMap hcof X Y W V f g h

lemma secondEdge_at_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ secondEdge hcof hfib X Y W V f g h φ =
    middlePoint hcof X Y W V f g h φ ψ := by
  rw [secondEdge, ← Category.assoc, preEdge_at_zero]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, RelativeChoiceSpace.postMap_ofExtension,
    RelativeChoiceSpace.preMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (middle_composite hcof X Y W V f g h φ)

lemma secondEdge_at_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ secondEdge hcof hfib X Y W V f g h φ =
    preRightPoint hcof X W V (f ≫ g) h := by
  rw [secondEdge, ← Category.assoc, preEdge_at_one]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, RelativeChoiceSpace.postMap_ofExtension,
    RelativeChoiceSpace.preMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (right_composite hcof X Y W V f g h)

abbrev faces : Fin 3 → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶
    preChoiceSpace X W V (f ≫ g) h) :=
  ![secondEdge hcof hfib X Y W V f g h φ,
    preEdge hcof hfib X W V (f ≫ g) h (ResolutionLiftPrecomposition.compose φ ψ),
    firstEdge hcof hfib X Y W V f g h φ ψ]

lemma faces_compatible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.StandardCompatible (faces hcof hfib X Y W V f g h φ ψ) := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> norm_num at hjk
  · exact (secondEdge_at_one hcof hfib X Y W V f g h φ).trans
      (preEdge_at_one hcof hfib X W V (f ≫ g) h (ResolutionLiftPrecomposition.compose φ ψ)).symm
  · exact (secondEdge_at_zero hcof hfib X Y W V f g h φ ψ).trans
      (firstEdge_at_one hcof hfib X Y W V f g h φ ψ).symm
  · exact (preEdge_at_zero hcof hfib X W V (f ≫ g) h
      (ResolutionLiftPrecomposition.compose φ ψ)).trans
      (firstEdge_at_zero hcof hfib X Y W V f g h φ ψ).symm

def triangle : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶
    preChoiceSpace X W V (f ≫ g) h :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib (vertexInclusion W V h)
    (preBoundary X W V (f ≫ g) h) (ResolutionLiftSpace.projection X V ((f ≫ g).base ≫ h))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V ((f ≫ g).base ≫ h)) 0
    (faces hcof hfib X Y W V f g h φ ψ) (faces_compatible hcof hfib X Y W V f g h φ ψ)).choose

@[reassoc (attr := simp)]
lemma triangle_face (k : Fin 3) : SSet.stdSimplex.δ k ≫ triangle hcof hfib X Y W V f g h φ ψ =
    faces hcof hfib X Y W V f g h φ ψ k :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib (vertexInclusion W V h)
    (preBoundary X W V (f ≫ g) h) (ResolutionLiftSpace.projection X V ((f ≫ g).base ≫ h))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V ((f ≫ g).base ≫ h)) 0
    (faces hcof hfib X Y W V f g h φ ψ)
    (faces_compatible hcof hfib X Y W V f g h φ ψ)).choose_spec.1 k

lemma triangle_fixed_boundary :
    vertexInclusion W V h ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ≫
        RelativeChoiceSpace.family (vertexInclusion W V h) (preBoundary X W V (f ≫ g) h)
          (triangle hcof hfib X Y W V f g h φ ψ) =
      vertices W V h ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ preBoundary X W V (f ≫ g) h :=
  (RelativeChoiceSpace.fill_standard_faces hcof hfib (vertexInclusion W V h)
    (preBoundary X W V (f ≫ g) h) (ResolutionLiftSpace.projection X V ((f ≫ g).base ≫ h))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V ((f ≫ g).base ≫ h)) 0
    (faces hcof hfib X Y W V f g h φ ψ)
    (faces_compatible hcof hfib X Y W V f g h φ ψ)).choose_spec.2

lemma triangle_action_face (Z : C)
    (t : CoherentLiftTuples.obj W V h ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom V.resolution.obj).obj Z) (k : Fin 3) :
    CoherentLiftTuples.obj W V h ◁ SSet.stdSimplex.δ k ≫
        KanLiftAction.parameterized hcof hfib X V ((f ≫ g).base ≫ h) Z
          (RelativeChoiceSpace.family (vertexInclusion W V h) (preBoundary X W V (f ≫ g) h)
            (triangle hcof hfib X Y W V f g h φ ψ)) t =
      KanLiftAction.parameterized hcof hfib X V ((f ≫ g).base ≫ h) Z
        (RelativeChoiceSpace.family (vertexInclusion W V h) (preBoundary X W V (f ≫ g) h)
          (faces hcof hfib X Y W V f g h φ ψ k))
        ((CoherentLiftTuples.obj W V h ◁ SSet.stdSimplex.δ k) ≫ t) := by
  rw [KanLiftAction.parameterized_naturality, ← RelativeChoiceSpace.family_naturality,
    triangle_face]

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftPreComposition
