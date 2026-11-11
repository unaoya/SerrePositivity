module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftMixedFamilies
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SelectedTriangle

/-!
# 中断した任意モデル源への一般化：CoherentLiftMixedComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Mixed comparison square with its selected four edges retained。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0067][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0067
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Mixed comparison square with its selected four edges retained

Two triangles share one actual diagonal and keep the four previously
selected pre/post comparison edges after their actual transports. All
endpoints and the common fixed boundary are proved from interchange.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftMixedComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X Y W V : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) (h : W ⟶ V)
  (φ : ResolutionLiftPrecomposition.FrameMap f)

abbrev pointA := RelativeChoiceSpace.ofExtension (vertexInclusion Y W g) (boundary X Y W V f g h φ)
  (familyA hcof X Y W V f g h φ) (familyA_vertices hcof X Y W V f g h φ)
abbrev pointB := RelativeChoiceSpace.ofExtension (vertexInclusion Y W g) (boundary X Y W V f g h φ)
  (familyB hcof X Y W V f g h) (familyB_vertices hcof X Y W V f g h φ)
abbrev pointC := RelativeChoiceSpace.ofExtension (vertexInclusion Y W g) (boundary X Y W V f g h φ)
  (familyC hcof X Y W V f g h φ) (familyC_vertices hcof X Y W V f g h φ)
abbrev pointD := RelativeChoiceSpace.ofExtension (vertexInclusion Y W g) (boundary X Y W V f g h φ)
  (familyD hcof X Y W V f g h) (familyD_vertices hcof X Y W V f g h φ)

abbrev mapAB : preChoiceSpace X Y W f g ⟶ space X Y W V f g h φ :=
  RelativeChoiceSpace.postMap (vertexInclusion Y W g) _ _ (postTail X Y W V f g h)
    (pre_boundary_transport hcof X Y W V f g h φ)
abbrev edgeAB := preEdge hcof hfib X Y W f g φ ≫ mapAB hcof X Y W V f g h φ

lemma edgeAB_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ edgeAB hcof hfib X Y W V f g h φ =
    pointA hcof X Y W V f g h φ := by
  rw [edgeAB, ← Category.assoc, preEdge_at_zero]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ RelativeChoiceSpace.postMap _ _ _ _ _ = _
  rw [RelativeChoiceSpace.postMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (initial_interchange hcof X Y W V f g h φ)

lemma edgeAB_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ edgeAB hcof hfib X Y W V f g h φ =
    pointB hcof X Y W V f g h φ := by
  rw [edgeAB, ← Category.assoc, preEdge_at_one]
  exact RelativeChoiceSpace.postMap_ofExtension _ _ _ _ _ _ _

abbrev mapAC : postChoiceSpace Y W V g h ⟶ space X Y W V f g h φ :=
  RelativeChoiceSpace.postMap (vertexInclusion Y W g) _ _ (preTail X Y W V f g h φ) rfl
abbrev edgeAC := postEdge hcof hfib Y W V g h ≫ mapAC X Y W V f g h φ

lemma edgeAC_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ edgeAC hcof hfib X Y W V f g h φ =
    pointA hcof X Y W V f g h φ := by
  rw [edgeAC, ← Category.assoc, postEdge_at_zero]
  exact RelativeChoiceSpace.postMap_ofExtension _ _ _ _ _ _ _

lemma edgeAC_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ edgeAC hcof hfib X Y W V f g h φ =
    pointC hcof X Y W V f g h φ := by
  rw [edgeAC, ← Category.assoc, postEdge_at_one]
  exact RelativeChoiceSpace.postMap_ofExtension _ _ _ _ _ _ _

abbrev mapCD : preChoiceSpace X Y V f (g ≫ h.base) ⟶ space X Y W V f g h φ :=
  RelativeChoiceSpace.preMap (vertexInclusion Y V (g ≫ h.base)) _ (vertexInclusion Y W g) _
    (vertexPost Y W V g h) (tuplePost Y W V g h) (post_vertex_square Y W V g h)
      (post_boundary_transport hcof X Y W V f g h φ)
abbrev edgeCD := preEdge hcof hfib X Y V f (g ≫ h.base) φ ≫ mapCD hcof X Y W V f g h φ

lemma edgeCD_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ edgeCD hcof hfib X Y W V f g h φ =
    pointC hcof X Y W V f g h φ := by
  rw [edgeCD, ← Category.assoc, preEdge_at_zero]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ RelativeChoiceSpace.preMap _ _ _ _ _ _ _ _ = _
  rw [RelativeChoiceSpace.preMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (familyC_as_pre hcof X Y W V f g h φ)

lemma edgeCD_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ edgeCD hcof hfib X Y W V f g h φ =
    pointD hcof X Y W V f g h φ := by
  rw [edgeCD, ← Category.assoc, preEdge_at_one]
  exact RelativeChoiceSpace.preMap_ofExtension _ _ _ _ _ _ _ _ _ _

abbrev mapBD : postChoiceSpace X W V (f.base ≫ g) h ⟶ space X Y W V f g h φ :=
  RelativeChoiceSpace.postMap (vertexInclusion X W (f.base ≫ g)) _ _ (castMap X Y W V f g h) rfl ≫
    RelativeChoiceSpace.preMap (vertexInclusion X W (f.base ≫ g)) _ (vertexInclusion Y W g) _
      (vertexPre X Y W f g) (tuplePre X Y W f g) (pre_vertex_square X Y W f g)
        (mixed_boundary_transport hcof X Y W V f g h φ)
abbrev edgeBD := postEdge hcof hfib X W V (f.base ≫ g) h ≫ mapBD hcof X Y W V f g h φ

lemma edgeBD_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ edgeBD hcof hfib X Y W V f g h φ =
    pointB hcof X Y W V f g h φ := by
  rw [edgeBD, ← Category.assoc, postEdge_at_zero]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, RelativeChoiceSpace.postMap_ofExtension,
    RelativeChoiceSpace.preMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (familyB_as_post hcof X Y W V f g h)

lemma edgeBD_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ edgeBD hcof hfib X Y W V f g h φ =
    pointD hcof X Y W V f g h φ := by
  rw [edgeBD, ← Category.assoc, postEdge_at_one]
  change RelativeChoiceSpace.ofExtension _ _ _ _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, RelativeChoiceSpace.postMap_ofExtension,
    RelativeChoiceSpace.preMap_ofExtension]
  exact RelativeChoiceSpace.ofExtension_congr _ _ _ _ _ _ (final_interchange hcof X Y W V f g h)

def diagonal : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ space X Y W V f g h φ :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.interval hcof hfib (vertexInclusion Y W g) (boundary X Y W V f g h φ)
    (ResolutionLiftSpace.projection X V (f.base ≫ g ≫ h.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V (f.base ≫ g ≫ h.base))
    (pointA hcof X Y W V f g h φ) (pointD hcof X Y W V f g h φ)).choose

lemma diagonal_zero : SSet.stdSimplex.δ (1 : Fin 2) ≫ diagonal hcof hfib X Y W V f g h φ =
    pointA hcof X Y W V f g h φ :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.interval hcof hfib (vertexInclusion Y W g) (boundary X Y W V f g h φ)
    (ResolutionLiftSpace.projection X V (f.base ≫ g ≫ h.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V (f.base ≫ g ≫ h.base))
    (pointA hcof X Y W V f g h φ) (pointD hcof X Y W V f g h φ)).choose_spec.1

lemma diagonal_one : SSet.stdSimplex.δ (0 : Fin 2) ≫ diagonal hcof hfib X Y W V f g h φ =
    pointD hcof X Y W V f g h φ :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.interval hcof hfib (vertexInclusion Y W g) (boundary X Y W V f g h φ)
    (ResolutionLiftSpace.projection X V (f.base ≫ g ≫ h.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V (f.base ≫ g ≫ h.base))
    (pointA hcof X Y W V f g h φ) (pointD hcof X Y W V f g h φ)).choose_spec.2

def leftBoundary : SelectedTriangle.Boundary (space X Y W V f g h φ) where
  vertex0 := pointA hcof X Y W V f g h φ
  vertex1 := pointB hcof X Y W V f g h φ
  vertex2 := pointD hcof X Y W V f g h φ
  edge01 := edgeAB hcof hfib X Y W V f g h φ
  edge12 := edgeBD hcof hfib X Y W V f g h φ
  edge02 := diagonal hcof hfib X Y W V f g h φ
  edge01_zero := edgeAB_zero hcof hfib X Y W V f g h φ
  edge01_one := edgeAB_one hcof hfib X Y W V f g h φ
  edge12_zero := edgeBD_zero hcof hfib X Y W V f g h φ
  edge12_one := edgeBD_one hcof hfib X Y W V f g h φ
  edge02_zero := diagonal_zero hcof hfib X Y W V f g h φ
  edge02_one := diagonal_one hcof hfib X Y W V f g h φ

def rightBoundary : SelectedTriangle.Boundary (space X Y W V f g h φ) where
  vertex0 := pointA hcof X Y W V f g h φ
  vertex1 := pointC hcof X Y W V f g h φ
  vertex2 := pointD hcof X Y W V f g h φ
  edge01 := edgeAC hcof hfib X Y W V f g h φ
  edge12 := edgeCD hcof hfib X Y W V f g h φ
  edge02 := diagonal hcof hfib X Y W V f g h φ
  edge01_zero := edgeAC_zero hcof hfib X Y W V f g h φ
  edge01_one := edgeAC_one hcof hfib X Y W V f g h φ
  edge12_zero := edgeCD_zero hcof hfib X Y W V f g h φ
  edge12_one := edgeCD_one hcof hfib X Y W V f g h φ
  edge02_zero := diagonal_zero hcof hfib X Y W V f g h φ
  edge02_one := diagonal_one hcof hfib X Y W V f g h φ

abbrev data (left : Bool) := if left then leftBoundary hcof hfib X Y W V f g h φ
  else rightBoundary hcof hfib X Y W V f g h φ

def triangle (left : Bool) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ space X Y W V f g h φ :=
  SelectedTriangle.fill hcof hfib (vertexInclusion Y W g) (boundary X Y W V f g h φ)
    (ResolutionLiftSpace.projection X V (f.base ≫ g ≫ h.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V (f.base ≫ g ≫ h.base))
    (data hcof hfib X Y W V f g h φ left)

lemma triangle_face (left : Bool) (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ triangle hcof hfib X Y W V f g h φ left =
      (data hcof hfib X Y W V f g h φ left).faces k :=
  SelectedTriangle.fill_face hcof hfib _ _ _ _ _ k

lemma data_diagonal (left : Bool) : (data hcof hfib X Y W V f g h φ left).faces 1 =
    diagonal hcof hfib X Y W V f g h φ := by cases left <;> rfl

lemma triangle_diagonal (left : Bool) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle hcof hfib X Y W V f g h φ left =
      diagonal hcof hfib X Y W V f g h φ :=
  (triangle_face hcof hfib X Y W V f g h φ left 1).trans
    (data_diagonal hcof hfib X Y W V f g h φ left)

lemma shared_diagonal : SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle hcof hfib X Y W V f g h φ true =
    SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle hcof hfib X Y W V f g h φ false :=
  (triangle_diagonal hcof hfib X Y W V f g h φ true).trans
    (triangle_diagonal hcof hfib X Y W V f g h φ false).symm

lemma triangle_fixed_boundary (left : Bool) :
    vertexInclusion Y W g ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ≫
        RelativeChoiceSpace.family (vertexInclusion Y W g) (boundary X Y W V f g h φ)
          (triangle hcof hfib X Y W V f g h φ left) =
      vertices Y W g ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ boundary X Y W V f g h φ :=
  SelectedTriangle.fill_fixed_boundary hcof hfib _ _ _ _ _

lemma triangle_action_face (left : Bool) (Z : C)
    (t : CoherentLiftTuples.obj Y W g ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom V.resolution.obj).obj Z) (k : Fin 3) :
    CoherentLiftTuples.obj Y W g ◁ SSet.stdSimplex.δ k ≫
        KanLiftAction.parameterized hcof hfib X V (f.base ≫ g ≫ h.base) Z
          (RelativeChoiceSpace.family (vertexInclusion Y W g) (boundary X Y W V f g h φ)
            (triangle hcof hfib X Y W V f g h φ left)) t =
      KanLiftAction.parameterized hcof hfib X V (f.base ≫ g ≫ h.base) Z
        (RelativeChoiceSpace.family (vertexInclusion Y W g) (boundary X Y W V f g h φ)
          ((data hcof hfib X Y W V f g h φ left).faces k))
        ((CoherentLiftTuples.obj Y W g ◁ SSet.stdSimplex.δ k) ≫ t) := by
  rw [KanLiftAction.parameterized_naturality, ← RelativeChoiceSpace.family_naturality,
    triangle_face]

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftMixedComparison
