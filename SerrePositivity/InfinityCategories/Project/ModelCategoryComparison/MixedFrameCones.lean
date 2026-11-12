module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams
public import SerrePositivity.EInfinity.HomotopyWeight.KanConeComparison

/-!
# 両側の frame の重み付き錐の比較同型

概要：Hovey §5.4 の始域 frame と右 frame の重み付き錐を anodyne 反転後に比較する。
方針：混合 Hom の共通図式を Kan 置換し、二つの比較と二つの単位を反転する。
規約：元の重みと両側の錐は保持し、混合 Hom の Kan 性は要求しない。
使われ方：具体的な E 代数の一般 homotopy 極限の導来 Hom の比較。
-/

@[expose] public section

noncomputable section

universe u v uD vD

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory Limits HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.DiagramModel.WeightedCones _root_.SerrePositivity.EInfinity.HomotopyWeight

variable (K : Type v) [SmallCategory K] {C : Type u} [Category.{v} C] [ModelCategory C]
  (W : K ⥤ SSet.{v}) (hW : (boundaries K).rlp.llp (initial.to W))
  (A : SimplexCategory ⥤ C)

/-- 概要：両 frame の重み付き錐は anodyne 反転後に同型（Hovey §5.4）。
方針：同じ混合 Hom の Kan 置換への自然な四つの比較を合成する。
規約：元の始域の cofibrancy と各 frame の条件は明示し、単体集合モデルは不要。
使われ方：始域の図式 Map^h と右 frame による計算対象の Hom の比較。 -/
def mixedConeComparisonIso
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {X : C} [IsCofibrant X] (a : A ⟶ (Functor.const SimplexCategory).obj X)
    (ha : ∀ n, weakEquivalences C (a.app n))
    (F : K ⥤ C) (R : K ⥤ SimplexCategoryᵒᵖ ⥤ C)
    (b : F ⋙ Functor.const SimplexCategoryᵒᵖ ⟶ R)
    (hF : ∀ k, IsFibrant (F.obj k)) (hR : ∀ k n, IsFibrant ((R.obj k).obj n))
    (hb : ∀ k n, weakEquivalences C ((b.app k).app n))
    (hRcof : ∀ k, reedyLeft simplex (cofibrations Cᵒᵖ) (initial.to (R.obj k).rightOp))
    (hRconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
      weakEquivalences Cᵒᵖ ((R.obj k).rightOp.map f))
    {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.obj ((coneSpace K W).obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagram K A F)) ≅
      L.obj ((coneSpace K W).obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram K X R)) := by
  let S := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagram K A F
  let T := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram K X R
  let l := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison K A F R b
  let r := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison K A a R
  have hS : ∀ k, SSet.KanComplex (S.obj k) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagram_kanComplex K A hA hconst F hF
  have hT : ∀ k, SSet.KanComplex (T.obj k) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagram_kanComplex K X R hRcof hRconst
  exact kanConeComparisonIso K W hW L hL l r hS hT
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.leftDiagramComparison_isIso K A hA F R b hF hR hb)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams.rightDiagramComparison_isIso K A hA a ha R hRcof)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
