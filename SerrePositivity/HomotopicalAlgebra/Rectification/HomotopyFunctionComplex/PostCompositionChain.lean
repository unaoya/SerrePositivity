module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftPostComposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TriangleBook

/-!
# 中断した任意モデル源への一般化：PostCompositionChain

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Simultaneous comparisons at all cuts of a finite composition chain。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0260][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0260
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Simultaneous comparisons at all cuts of a finite composition chain

Each prefix/suffix factorization uses the previously chosen comparison
triangle. All triangles share the same direct comparison edge and are
assembled into one actual simplicial parameter. Source factorization
choices and equality of source object/Hom universes are not assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.PostCompositionChain
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev choiceCast {X Y V : ResolutionObject C} (f : X.base ⟶ Y.base)
    {g h : Y ⟶ V} (e : g = h) : postChoiceSpace X Y V f g ⟶ postChoiceSpace X Y V f h :=
  eqToHom (congrArg (fun k => postChoiceSpace X Y V f k) e)

lemma triangle_direct {X Y W V : ResolutionObject C} (f : X.base ⟶ Y.base)
    (g : Y ⟶ W) (h : W ⟶ V) (k : Y ⟶ V) (e : g ≫ h = k) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫
      (CoherentLiftPostComposition.triangle hcof hfib X Y W V f g h ≫ choiceCast f e) =
        postEdge hcof hfib X Y V f k := by
  subst k
  rw [choiceCast, eqToHom_refl, Category.comp_id]
  exact CoherentLiftPostComposition.triangle_face hcof hfib X Y W V f g h 1

variable {n : ℕ} (F : Fin (n + 1) ⥤ ResolutionObject C)
  (X : ResolutionObject C) (f : X.base ⟶ (F.obj 0).base)

abbrev first : ResolutionObject C := F.obj 0
abbrev last : ResolutionObject C := F.obj (Fin.last n)

abbrev prefixMap (i : Fin (n + 1)) : first F ⟶ F.obj i :=
  F.map (homOfLE (Fin.zero_le i))

abbrev suffixMap (i : Fin (n + 1)) : F.obj i ⟶ last F :=
  F.map (homOfLE (Fin.le_last i))

abbrev total : first F ⟶ last F := F.map (homOfLE (Fin.zero_le (Fin.last n)))

omit [ModelCategory SSet.{v}] in
lemma prefix_suffix (i : Fin (n + 1)) : prefixMap F i ≫ suffixMap F i = total F := by
  rw [prefixMap, suffixMap, ← F.map_comp]
  rfl

abbrev choiceSpace : SSet.{v} := postChoiceSpace X (first F) (last F) f (total F)

/-- The selected triangle for the actual prefix and suffix, moved to the common space. -/
def cutTriangle (i : Fin (n + 1)) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ choiceSpace F X f :=
  CoherentLiftPostComposition.triangle hcof hfib X (first F) (F.obj i) (last F)
      f (prefixMap F i) (suffixMap F i) ≫ choiceCast f (prefix_suffix F i)

@[reassoc]
lemma cutTriangle_face (i : Fin (n + 1)) (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ cutTriangle hcof hfib F X f i =
      CoherentLiftPostComposition.faces hcof hfib X (first F) (F.obj i) (last F)
        f (prefixMap F i) (suffixMap F i) k ≫ choiceCast f (prefix_suffix F i) := by
  rw [cutTriangle, ← Category.assoc, CoherentLiftPostComposition.triangle_face]

@[reassoc]
lemma cutTriangle_direct (i : Fin (n + 1)) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ cutTriangle hcof hfib F X f i =
      postEdge hcof hfib X (first F) (last F) f (total F) :=
  triangle_direct hcof hfib f (prefixMap F i) (suffixMap F i) (total F) (prefix_suffix F i)

/-- All cut comparisons are contained in one parameter, including the endpoint cuts. -/
abbrev parameter (_F : Fin (n + 1) ⥤ ResolutionObject C) : SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj (ULift.{v} (Fin (n + 1)))

def comparison : parameter F ⟶ choiceSpace F X f :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc (postEdge hcof hfib X (first F) (last F) f (total F))
    (fun i : ULift.{v} (Fin (n + 1)) => cutTriangle hcof hfib F X f i.down)
    (fun i => cutTriangle_direct hcof hfib F X f i.down)

@[reassoc]
lemma comparison_cut (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle (ULift.{v} (Fin (n + 1))) ⟨i⟩ ≫ comparison hcof hfib F X f =
      cutTriangle hcof hfib F X f i :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle_desc _ _ _ (⟨i⟩ : ULift.{v} (Fin (n + 1)))

@[reassoc]
lemma comparison_direct :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge (ULift.{v} (Fin (n + 1))) ≫ comparison hcof hfib F X f =
      postEdge hcof hfib X (first F) (last F) f (total F) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge_desc _ _ _

lemma fixed_boundary :
    vertexInclusion X (first F) f ▷ parameter F ≫
        RelativeChoiceSpace.family (vertexInclusion X (first F) f)
          (postBoundary X (first F) (last F) f (total F)) (comparison hcof hfib F X f) =
      vertices X (first F) f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          postBoundary X (first F) (last F) f (total F) :=
  RelativeChoiceSpace.family_fixed_boundary _ _ _

lemma action_cut (i : Fin (n + 1)) (Z : C)
    (t : CoherentLiftTuples.obj X (first F) f ⊗ parameter F ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (last F).resolution.obj).obj Z) :
    CoherentLiftTuples.obj X (first F) f ◁
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle (ULift.{v} (Fin (n + 1))) ⟨i⟩ ≫
      KanLiftAction.parameterized hcof hfib X (last F) (f ≫ (total F).base) Z
        (RelativeChoiceSpace.family (vertexInclusion X (first F) f)
          (postBoundary X (first F) (last F) f (total F)) (comparison hcof hfib F X f)) t =
      KanLiftAction.parameterized hcof hfib X (last F) (f ≫ (total F).base) Z
        (RelativeChoiceSpace.family (vertexInclusion X (first F) f)
          (postBoundary X (first F) (last F) f (total F)) (cutTriangle hcof hfib F X f i))
        ((CoherentLiftTuples.obj X (first F) f ◁
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle (ULift.{v} (Fin (n + 1))) ⟨i⟩) ≫ t) := by
  rw [KanLiftAction.parameterized_naturality, ← RelativeChoiceSpace.family_naturality,
    comparison_cut]

end SerrePositivity.HomotopyFunctionComplex.PostCompositionChain
