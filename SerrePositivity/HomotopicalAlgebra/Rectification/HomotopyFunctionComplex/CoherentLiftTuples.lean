module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.KanLiftCoherence

/-!
# 中断した任意モデル源への一般化：CoherentLiftTuples

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Simultaneous higher comparisons between strict lift choices。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0072][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0072
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Simultaneous higher comparisons between strict lift choices

For a fixed base map, all ordered tuples of strict lifts act coherently.
A single simplicial extension fixes every strict lift vertex and supplies
all higher comparisons, including faces and degeneracies. This compares
choices over one base map; compatibility with composition between distinct
lift spaces and the final strict source functor remain separate tasks.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftTuples
variable {C : Type u} [Category.{v} C] [ModelCategory C]

local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

/-- Strict lifts over a fixed base map form a type in the original Hom universe. -/
abbrev StrictLift (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) : Type v :=
  {g : X ⟶ Y // g.base = f}

abbrev obj (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) : SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.obj (StrictLift X Y f)

def point (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (g : StrictLift X Y f) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ ResolutionLiftSpace.obj X Y f := by
  rcases g with ⟨g, rfl⟩
  exact ResolutionLiftSpace.ofLift g

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

/-- Choose all comparison simplices simultaneously, retaining every strict lift vertex. -/
def interpolation (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    obj X Y f ⟶ ResolutionLiftSpace.obj X Y f :=
  (ResolutionLiftSpace.extension hcof X Y f
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion (StrictLift X Y f))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap (point X Y f))).choose

lemma interpolation_vertices (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion (StrictLift X Y f) ≫ interpolation hcof X Y f =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap (point X Y f) :=
  (ResolutionLiftSpace.extension hcof X Y f
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.inclusion (StrictLift X Y f))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.pointsMap (point X Y f))).choose_spec

abbrev simplex (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) {n : ℕ}
    (a : Fin (n + 1) → StrictLift X Y f) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ ResolutionLiftSpace.obj X Y f :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.simplex a ≫ interpolation hcof X Y f

/-- A single formula controls every face and every degeneracy, in all dimensions. -/
lemma simplex_naturality (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) {n m : ℕ}
    (a : Fin (n + 1) → StrictLift X Y f)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ simplex hcof X Y f a =
      simplex hcof X Y f (fun i => a (θ.toOrderHom i)) := by
  rw [simplex, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.simplex_naturality]

lemma simplex_vertex (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
    (a : StrictLift X Y f) :
    simplex hcof X Y f (fun _ : Fin 1 => a) = point X Y f a := by
  rw [simplex, ← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.vertex_inclusion, Category.assoc,
    interpolation_vertices, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.vertex_pointsMap]

/-- Repeating a strict vertex gives its actual degenerate simplex in every dimension. -/
lemma simplex_constant (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
    (a : StrictLift X Y f) (n : ℕ) :
    simplex hcof X Y f (fun _ : Fin (n + 1) => a) =
      SSet.stdSimplex.map ((SimplexCategory.mk n).const (SimplexCategory.mk 0) 0) ≫
        point X Y f a := by
  rw [← simplex_vertex hcof X Y f a]
  exact (simplex_naturality hcof X Y f (fun _ : Fin 1 => a) _).symm

variable (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- Action of an entire coherent tuple simplex on the original Hom. -/
abbrev action (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) {n : ℕ}
    (a : Fin (n + 1) → StrictLift X Y f) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⨯
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).obj Z ⟶ KanLiftAction.target hcof hfib X Z :=
  KanLiftAction.parameterized hcof hfib X Y f Z (prod.fst ≫ simplex hcof X Y f a) prod.snd

lemma action_naturality (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) {n m : ℕ}
    (a : Fin (n + 1) → StrictLift X Y f)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    prod.map (SSet.stdSimplex.map θ) (𝟙 _) ≫ action hcof hfib X Y f Z a =
      action hcof hfib X Y f Z (fun i => a (θ.toOrderHom i)) := by
  rw [action, KanLiftAction.parameterized_naturality]
  simp only [prod.map_fst_assoc, prod.map_snd, Category.comp_id, simplex_naturality]

lemma action_target_naturality (X Y : ResolutionObject C) (f : X.base ⟶ Y.base)
    {Z Z' : C} (h : Z ⟶ Z') {n : ℕ} (a : Fin (n + 1) → StrictLift X Y f) :
    prod.map (𝟙 _) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom Y.resolution.obj).map h) ≫
        action hcof hfib X Y f Z' a =
      action hcof hfib X Y f Z a ≫ (KanLiftAction.targetFunctor hcof hfib X).map h := by
  rw [action, KanLiftAction.parameterized_naturality]
  simp only [prod.map_fst_assoc, Category.id_comp, prod.map_snd]
  exact KanLiftAction.parameterized_target_naturality hcof hfib X Y f h _ _

lemma action_strict_vertex {X Y : ResolutionObject C} (g : X ⟶ Y) (Z : C) :
    action hcof hfib X Y g.base Z (fun _ : Fin 1 => (⟨g, rfl⟩ : StrictLift X Y g.base)) =
      prod.snd ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap g.diagram).app Z ≫
        KanLiftAction.comparison hcof hfib X Z := by
  rw [action, simplex_vertex]
  exact KanLiftAction.ofLift hcof hfib g Z prod.fst prod.snd

/-- Every constant tuple acts by the original strict map, without an additional homotopy. -/
lemma action_strict_constant {X Y : ResolutionObject C} (g : X ⟶ Y) (Z : C) (n : ℕ) :
    action hcof hfib X Y g.base Z
        (fun _ : Fin (n + 1) => (⟨g, rfl⟩ : StrictLift X Y g.base)) =
      prod.snd ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap g.diagram).app Z ≫
        KanLiftAction.comparison hcof hfib X Z := by
  rw [action, simplex_constant, ← Category.assoc]
  exact KanLiftAction.ofLift hcof hfib g Z
    (prod.fst ≫ SSet.stdSimplex.map ((SimplexCategory.mk n).const (SimplexCategory.mk 0) 0))
    prod.snd

lemma action_vertex (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C)
    (g : StrictLift X Y f) :
    action hcof hfib X Y f Z (fun _ : Fin 1 => g) =
      prod.snd ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap g.val.diagram).app Z ≫
        KanLiftAction.comparison hcof hfib X Z := by
  rcases g with ⟨g, rfl⟩
  exact action_strict_vertex hcof hfib g Z

/-- Every vertex restriction is the prescribed strict action, in any dimension. -/
lemma action_at_vertex (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) {n : ℕ}
    (a : Fin (n + 1) → StrictLift X Y f) (i : Fin (n + 1)) :
    prod.map (SSet.stdSimplex.map ((SimplexCategory.mk 0).const (SimplexCategory.mk n) i))
        (𝟙 _) ≫ action hcof hfib X Y f Z a =
      prod.snd ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (a i).val.diagram).app Z ≫
        KanLiftAction.comparison hcof hfib X Z := by
  rw [action_naturality]
  exact action_vertex hcof hfib X Y f Z (a i)

/-- The four strict expressions occurring in a triple composite.
They have the same base map, including the two partially composed choices. -/
def tripleCompositeVertices (X Y W V : ResolutionObject C)
    (f : X.base ⟶ Y.base) (g : Y.base ⟶ W.base) (h : W.base ⟶ V.base) :
    Fin 4 → StrictLift X V (f ≫ g ≫ h) :=
  ![⟨ResolutionObject.lift (f ≫ g ≫ h), rfl⟩,
    ⟨(ResolutionObject.lift (f ≫ g) : X ⟶ W) ≫
      (ResolutionObject.lift h : W ⟶ V), Category.assoc f g h⟩,
    ⟨(ResolutionObject.lift f : X ⟶ Y) ≫
      (ResolutionObject.lift (g ≫ h) : Y ⟶ V), rfl⟩,
    ⟨((ResolutionObject.lift f : X ⟶ Y) ≫
      (ResolutionObject.lift g : Y ⟶ W)) ≫ (ResolutionObject.lift h : W ⟶ V),
      Category.assoc f g h⟩]

/-- One actual tetrahedron, with all triangular faces supplied by the same
interpolation. It does not assert that its edges are horizontal composites
of separately selected lower-dimensional comparison homotopies. -/
abbrev tripleCompositeAction (X Y W V : ResolutionObject C)
    (f : X.base ⟶ Y.base) (g : Y.base ⟶ W.base) (h : W.base ⟶ V.base) (Z : C) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 3) ⨯
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom V.resolution.obj).obj Z ⟶ KanLiftAction.target hcof hfib X Z :=
  action hcof hfib X V (f ≫ g ≫ h) Z (tripleCompositeVertices X Y W V f g h)

lemma tripleCompositeAction_face (X Y W V : ResolutionObject C)
    (f : X.base ⟶ Y.base) (g : Y.base ⟶ W.base) (h : W.base ⟶ V.base) (Z : C)
    (i : Fin 4) :
    prod.map (SSet.stdSimplex.map (SimplexCategory.δ i)) (𝟙 _) ≫
        tripleCompositeAction hcof hfib X Y W V f g h Z =
      action hcof hfib X V (f ≫ g ≫ h) Z
        (fun j => tripleCompositeVertices X Y W V f g h ((SimplexCategory.δ i).toOrderHom j)) :=
  action_naturality hcof hfib X V (f ≫ g ≫ h) Z _ _

lemma tripleCompositeAction_last_vertex (X Y W V : ResolutionObject C)
    (f : X.base ⟶ Y.base) (g : Y.base ⟶ W.base) (h : W.base ⟶ V.base) (Z : C) :
    prod.map (SSet.stdSimplex.map ((SimplexCategory.mk 0).const (SimplexCategory.mk 3) 3))
        (𝟙 _) ≫ tripleCompositeAction hcof hfib X Y W V f g h Z =
      prod.snd ≫ KanLiftCoherence.chosenMap W V h Z ≫ KanLiftCoherence.chosenMap Y W g Z ≫
        KanLiftCoherence.chosenMap X Y f Z ≫ KanLiftAction.comparison hcof hfib X Z := by
  refine (action_at_vertex hcof hfib X V (f ≫ g ≫ h) Z _ 3).trans ?_
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap
        (tripleCompositeVertices X Y W V f g h 3).val.diagram).app Z =
      KanLiftCoherence.chosenMap W V h Z ≫ KanLiftCoherence.chosenMap Y W g Z ≫
        KanLiftCoherence.chosenMap X Y f Z := by
    ext n x
    change (((ResolutionObject.lift f : X ⟶ Y).diagram.app n.unop ≫
        (ResolutionObject.lift g : Y ⟶ W).diagram.app n.unop) ≫
        (ResolutionObject.lift h : W ⟶ V).diagram.app n.unop) ≫ x =
      (ResolutionObject.lift f : X ⟶ Y).diagram.app n.unop ≫
        ((ResolutionObject.lift g : Y ⟶ W).diagram.app n.unop ≫
          ((ResolutionObject.lift h : W ⟶ V).diagram.app n.unop ≫ x))
    simp only [Category.assoc]
  rw [hc]
  simp only [Category.assoc]

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftTuples
