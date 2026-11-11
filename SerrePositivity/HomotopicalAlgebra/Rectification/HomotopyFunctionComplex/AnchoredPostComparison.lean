module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.AnchoredChain
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.AnchoredChainNerve
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.PostCompositionChain
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanTriangleFamily

/-!
# 中断した任意モデル源への一般化：AnchoredPostComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual ordinal reindexing of composition chains and their comparisons。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0059][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0059
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual ordinal reindexing of composition chains and their comparisons

Surrounding arrows keep the external endpoints fixed, even when the first
or last internal vertex is omitted. The same selected factorization
triangle is retained under every ordinal map, including faces and degeneracies.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.AnchoredPostComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V : ResolutionObject C} (f : X.base ⟶ Y.base) {g : Y ⟶ V}

def factorTriangle (a : ArrowFactorization g) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶ postChoiceSpace X Y V f g :=
  CoherentLiftPostComposition.triangle hcof hfib X Y a.middle V f a.left a.right ≫
    PostCompositionChain.choiceCast f a.fac

@[reassoc]
lemma factorTriangle_direct (a : ArrowFactorization g) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ factorTriangle hcof hfib f a =
      postEdge hcof hfib X Y V f g :=
  PostCompositionChain.triangle_direct hcof hfib f a.left a.right g a.fac

variable {n m : ℕ} (c : AnchoredChain g n)

abbrev triangle (k : Fin (n + 1)) := factorTriangle hcof hfib f (c.cut k)

@[reassoc]
lemma triangle_direct (k : Fin (n + 1)) :
    SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle hcof hfib f c k = postEdge hcof hfib X Y V f g :=
  factorTriangle_direct hcof hfib f (c.cut k)

lemma triangle_reindex (θ : Fin (m + 1) →o Fin (n + 1)) (k : Fin (m + 1)) :
    triangle hcof hfib f (c.reindex θ) k = triangle hcof hfib f c (θ k) :=
  congrArg (factorTriangle hcof hfib f) (c.cut_reindex θ k)

abbrev parameter (_c : AnchoredChain g n) : SSet.{v} := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj (ULift.{v} (Fin (n + 1)))

def comparison : parameter c ⟶ postChoiceSpace X Y V f g :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc (postEdge hcof hfib X Y V f g)
    (fun k : ULift.{v} (Fin (n + 1)) => triangle hcof hfib f c k.down)
    (fun k => triangle_direct hcof hfib f c k.down)

@[reassoc]
lemma comparison_cut (k : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle (ULift.{v} (Fin (n + 1))) ⟨k⟩ ≫ comparison hcof hfib f c =
      triangle hcof hfib f c k :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle_desc _ _ _ (⟨k⟩ : ULift.{v} (Fin (n + 1)))

@[reassoc]
lemma comparison_direct :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge (ULift.{v} (Fin (n + 1))) ≫ comparison hcof hfib f c =
      postEdge hcof hfib X Y V f g := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge_desc _ _ _

abbrev ordinalMap (θ : Fin (m + 1) →o Fin (n + 1)) : parameter (c.reindex θ) ⟶ parameter c :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.reindex (fun k : ULift.{v} (Fin (m + 1)) => (⟨θ k.down⟩ : ULift.{v} (Fin (n + 1))))

/-- This changes the chain diagram itself, not merely its cut labels. -/
lemma comparison_reindex (θ : Fin (m + 1) →o Fin (n + 1)) :
    ordinalMap c θ ≫ comparison hcof hfib f c = comparison hcof hfib f (c.reindex θ) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.hom_ext
  · rintro ⟨k⟩
    change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.triangle (ULift.{v} (Fin (m + 1)))
      (⟨k⟩ : ULift.{v} (Fin (m + 1))) ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.reindex _ ≫ _) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.triangle_reindex]
    exact (comparison_cut hcof hfib f c (θ k)).trans
      ((triangle_reindex hcof hfib f c θ k).symm.trans
        (comparison_cut hcof hfib f (c.reindex θ) k).symm)
  · change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.sharedEdge _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.reindex _ ≫ _) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.sharedEdge_reindex]
    exact (comparison_direct hcof hfib f c).trans
      (comparison_direct hcof hfib f (c.reindex θ)).symm

abbrev kanComparison := KanTriangleFamily.extension hcof hfib (vertexInclusion X Y f)
  (postBoundary X Y V f g) (ResolutionLiftSpace.projection X V (f ≫ g.base))
  (ResolutionLiftSpace.projection_trivialFibration hcof X V (f ≫ g.base))
  (postEdge hcof hfib X Y V f g)
  (fun k : ULift.{v} (Fin (n + 1)) => triangle hcof hfib f c k.down)
  (fun k => triangle_direct hcof hfib f c k.down)

/-- The independent extension of the changed chain is the extension of its reindexed family. -/
lemma kanComparison_reindexed (θ : Fin (m + 1) →o Fin (n + 1)) :
    kanComparison hcof hfib f (c.reindex θ) =
      KanTriangleFamily.restricted hcof hfib (vertexInclusion X Y f)
        (postBoundary X Y V f g) (ResolutionLiftSpace.projection X V (f ≫ g.base))
        (ResolutionLiftSpace.projection_trivialFibration hcof X V (f ≫ g.base))
        (postEdge hcof hfib X Y V f g)
        (fun k : ULift.{v} (Fin (n + 1)) => triangle hcof hfib f c k.down)
        (fun k => triangle_direct hcof hfib f c k.down)
        (fun k : ULift.{v} (Fin (m + 1)) => (⟨θ k.down⟩ : ULift.{v} (Fin (n + 1)))) := by
  have ht : (fun k : ULift.{v} (Fin (m + 1)) => triangle hcof hfib f (c.reindex θ) k.down) =
      (fun k : ULift.{v} (Fin (m + 1)) => triangle hcof hfib f c (θ k.down)) :=
    funext (fun k => triangle_reindex hcof hfib f c θ k.down)
  unfold kanComparison KanTriangleFamily.restricted
  congr 1

abbrev reindexHomotopy (θ : Fin (m + 1) →o Fin (n + 1)) :=
  KanTriangleFamily.reindexHomotopy hcof hfib (vertexInclusion X Y f)
    (postBoundary X Y V f g) (ResolutionLiftSpace.projection X V (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X V (f ≫ g.base))
    (postEdge hcof hfib X Y V f g)
    (fun k : ULift.{v} (Fin (n + 1)) => triangle hcof hfib f c k.down)
    (fun k => triangle_direct hcof hfib f c k.down)
    (fun k : ULift.{v} (Fin (m + 1)) => (⟨θ k.down⟩ : ULift.{v} (Fin (n + 1))))


lemma reindexHomotopy_at_zero (θ : Fin (m + 1) →o Fin (n + 1)) :
    KanTriangleFamily.parameter hcof hfib (ULift.{v} (Fin (m + 1))) ◁
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫ (reindexHomotopy hcof hfib f c θ).hom =
      KanTriangleFamily.parameter hcof hfib (ULift.{v} (Fin (m + 1))) ◁
        RelativeChoiceSpace.pointUnitIso.hom ≫ (ρ_ _).hom ≫
          kanComparison hcof hfib f (c.reindex θ) :=
  (reindexHomotopy hcof hfib f c θ).at_zero.trans
    (congrArg (fun e => KanTriangleFamily.parameter hcof hfib (ULift.{v} (Fin (m + 1))) ◁
      RelativeChoiceSpace.pointUnitIso.hom ≫ (ρ_ _).hom ≫ e)
        (kanComparison_reindexed hcof hfib f c θ).symm)

lemma reindexHomotopy_at_one (θ : Fin (m + 1) →o Fin (n + 1)) :
    KanTriangleFamily.parameter hcof hfib (ULift.{v} (Fin (m + 1))) ◁
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫ (reindexHomotopy hcof hfib f c θ).hom =
      KanTriangleFamily.parameter hcof hfib (ULift.{v} (Fin (m + 1))) ◁
        RelativeChoiceSpace.pointUnitIso.hom ≫ (ρ_ _).hom ≫
          (KanTriangleFamily.reindex hcof hfib
            (fun k : ULift.{v} (Fin (m + 1)) => (⟨θ k.down⟩ : ULift.{v} (Fin (n + 1)))) ≫
              kanComparison hcof hfib f c) :=
  (reindexHomotopy hcof hfib f c θ).at_one

lemma reindexedBoundary (θ : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.desc (postEdge hcof hfib X Y V f g)
      (fun k : ULift.{v} (Fin (m + 1)) => triangle hcof hfib f c (θ k.down))
      (fun k => triangle_direct hcof hfib f c (θ k.down)) =
        comparison hcof hfib f (c.reindex θ) :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBookMaps.desc_reindex
    (fun k : ULift.{v} (Fin (m + 1)) => (⟨θ k.down⟩ : ULift.{v} (Fin (n + 1))))
    (postEdge hcof hfib X Y V f g)
    (fun k : ULift.{v} (Fin (n + 1)) => triangle hcof hfib f c k.down)
    (fun k => triangle_direct hcof hfib f c k.down)).symm.trans
      (comparison_reindex hcof hfib f c θ)

lemma reindexHomotopy_relative (θ : Fin (m + 1) →o Fin (n + 1)) :
    KanTriangleFamily.inclusion hcof hfib (ULift.{v} (Fin (m + 1))) ▷
      SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ≫ (reindexHomotopy hcof hfib f c θ).hom =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj (ULift.{v} (Fin (m + 1))) ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          comparison hcof hfib f (c.reindex θ) :=
  (reindexHomotopy hcof hfib f c θ).relative.trans
    (congrArg (fun e => _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TriangleBook.obj (ULift.{v} (Fin (m + 1))) ◁
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ _).hom ≫ e) (reindexedBoundary hcof hfib f c θ))

/-- The nerve identification retains each actual factorization comparison triangle. -/
lemma fromDiagram_triangle (F : Fin (n + 1) ⥤ ArrowFactorization g) (k : Fin (n + 1)) :
    triangle hcof hfib f (AnchoredChain.fromDiagram F) k =
      factorTriangle hcof hfib f (F.obj k) :=
  congrArg (factorTriangle hcof hfib f) (AnchoredChain.cutDiagram_fromDiagram_obj F k)

/-- Identity anchors recover exactly the earlier selected cut triangle. -/
lemma ofDiagram_triangle (F : Fin (n + 1) ⥤ ResolutionObject C) (X : ResolutionObject C)
    (f : X.base ⟶ (F.obj 0).base) (k : Fin (n + 1)) :
    triangle hcof hfib f (AnchoredChain.ofDiagram F) k =
      PostCompositionChain.cutTriangle hcof hfib F X f k := by
  have h : (AnchoredChain.ofDiagram F).cut k =
      (⟨F.obj k, PostCompositionChain.prefixMap F k, PostCompositionChain.suffixMap F k,
        PostCompositionChain.prefix_suffix F k⟩ :
          ArrowFactorization (PostCompositionChain.total F)) := by
    unfold AnchoredChain.cut AnchoredChain.before AnchoredChain.after AnchoredChain.ofDiagram
    congr 1 <;> simp
  have he : factorTriangle hcof hfib f
      (⟨F.obj k, PostCompositionChain.prefixMap F k, PostCompositionChain.suffixMap F k,
        PostCompositionChain.prefix_suffix F k⟩ :
          ArrowFactorization (PostCompositionChain.total F)) =
      PostCompositionChain.cutTriangle hcof hfib F X f k := rfl
  exact (congrArg (factorTriangle hcof hfib f) h).trans he

end SerrePositivity.HomotopyFunctionComplex.AnchoredPostComparison
