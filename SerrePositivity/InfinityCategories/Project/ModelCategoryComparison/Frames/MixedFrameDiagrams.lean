module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.MixedFrameComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor

/-!
# 両 frame の混合 Hom の図式と自然な二つの比較

概要：Hovey §5.4 の始域・終域 frame の共同比較を小図式全体に自然に構成する。
方針：各次元の前合成・後合成の式で図式の自然性を確認する。
規約：中間の混合 Hom の Kan 性は仮定しない。
使われ方：両 frame の重み付き錐の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams

open CategoryTheory Limits HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.SimplicialModel
open scoped SSet.modelCategoryQuillen

variable (K : Type v) [SmallCategory K] {C : Type u} [Category.{v} C]
  (A : SimplexCategory ⥤ C)

/-- 概要：始域 frame と元の終域図式の Hom 図式（Hovey §5.4）。
方針：元の図式に cosimplicial Hom を後合成する。
規約：各頂点で同じ始域 frame を使う。
使われ方：始域 frame の重み付き錐。 -/
abbrev leftDiagram (F : K ⥤ C) : K ⥤ SSet.{v} := F ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A

/-- 概要：始域 frame と右 frame 図式の混合 Hom（Hovey §5.4）。
方針：混合 Hom 関手を右 frame の図式に後合成する。
規約：全頂点・全射で同じ対角を取る。
使われ方：両側の frame の比較の共通図式。 -/
abbrev mixedDiagram (R : K ⥤ SimplexCategoryᵒᵖ ⥤ C) : K ⥤ SSet.{v} := R ⋙ _root_.SerrePositivity.EInfinity.FrameHom.MixedFrame.mixedFunctor A

/-- 概要：固定した始域と右 frame 図式の Hom（Hovey §5.4）。
方針：元の始域から各次元の右 frame への Hom を取る。
規約：射は元の圏の同じ射として表す。
使われ方：右 frame の重み付き錐。 -/
abbrev rightDiagram (X : C) (R : K ⥤ SimplexCategoryᵒᵖ ⥤ C) : K ⥤ SSet.{v} :=
  R ⋙ _root_.SerrePositivity.EInfinity.FrameHom.MixedFrame.rightHomFunctor X

/-- 概要：始域 frame の図式から混合 Hom 図式への自然変換（Hovey §5.4）。
方針：終域 frame の augmentation の自然性を各次元の後合成へ移す。
規約：元の図式のすべての射に厳密に自然。
使われ方：始域 frame の錐から共通図式の錐へ移る。 -/
def leftDiagramComparison (F : K ⥤ C) (R : K ⥤ SimplexCategoryᵒᵖ ⥤ C)
    (b : F ⋙ Functor.const SimplexCategoryᵒᵖ ⟶ R) :
    leftDiagram K A F ⟶ mixedDiagram K A R where
  app k := _root_.SerrePositivity.EInfinity.FrameHom.MixedFrame.leftComparison A (b.app k)
  naturality k l f := by
    ext n h
    change (h ≫ F.map f) ≫ (b.app l).app n = (h ≫ (b.app k).app n) ≫ (R.map f).app n
    have hb : F.map f ≫ (b.app l).app n = (b.app k).app n ≫ (R.map f).app n :=
      congr_app (b.naturality f) n
    rw [Category.assoc, hb, ← Category.assoc]

/-- 概要：右 frame の Hom 図式から混合 Hom 図式への自然変換（Hovey §5.4）。
方針：各次元の augmentation の前合成と図式射の後合成を交換する。
規約：元の始域と同じ右 frame 図式を使う。
使われ方：右 frame の錐から共通図式の錐へ移る。 -/
def rightDiagramComparison {X : C} (a : A ⟶ (Functor.const SimplexCategory).obj X)
    (R : K ⥤ SimplexCategoryᵒᵖ ⥤ C) : rightDiagram K X R ⟶ mixedDiagram K A R where
  app k := _root_.SerrePositivity.EInfinity.FrameHom.MixedFrame.rightComparison A a (R.obj k)
  naturality k l f := by
    ext n h
    change a.app n.unop ≫ (h ≫ (R.map f).app n) =
      (a.app n.unop ≫ h) ≫ (R.map f).app n
    exact (Category.assoc _ _ _).symm

variable [ModelCategory C]

/-- 概要：始域 frame の Hom 図式は Kan 値（Hovey §5）。
方針：始域 frame の Reedy cofibrancy と constancy、終域の fibrancy を使う。
規約：単体集合のモデル構造は不要。
使われ方：元の始域 frame の錐を Kan 置換後と比較する。 -/
lemma leftDiagram_kanComplex
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (F : K ⥤ C) (hF : ∀ k, IsFibrant (F.obj k)) (k : K) :
    SSet.KanComplex ((leftDiagram K A F).obj k) := by
  have := hF k
  exact cosimplicialHom_kanComplex A hA hconst (F.obj k)

/-- 概要：右 frame の Hom 図式は Kan 値（Hovey §5）。
方針：反対圏の frame Hom の Kan 性を元の射の同型で移す。
規約：元の始域の cofibrancy と各右 frame の条件を明示する。
使われ方：元の右 frame の錐を Kan 置換後と比較する。 -/
lemma rightDiagram_kanComplex (X : C) [IsCofibrant X]
    (R : K ⥤ SimplexCategoryᵒᵖ ⥤ C)
    (hR : ∀ k, reedyLeft simplex (cofibrations Cᵒᵖ) (initial.to (R.obj k).rightOp))
    (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
      weakEquivalences Cᵒᵖ ((R.obj k).rightOp.map f)) (k : K) :
    SSet.KanComplex ((rightDiagram K X R).obj k) := by
  have : IsFibrant (op X) := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.fibrantOp_of_cofibrant X
  have := cosimplicialHom_kanComplex (R.obj k).rightOp (hR k) (hconst k) (op X)
  exact isFibrant_of_fibration (_root_.SerrePositivity.EInfinity.FrameHom.MixedFrame.rightHomIso X (R.obj k)).hom

/-- 概要：始域 frame からの図式比較は各値で局所化同値（Hovey §5）。
方針：各値の終域の弱同値と二重 Hom の対角不変性を使う。
規約：比較は元の同じ自然変換。
使われ方：始域側の比較を重み付き錐へ移す。 -/
lemma leftDiagramComparison_isIso
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (F : K ⥤ C) (R : K ⥤ SimplexCategoryᵒᵖ ⥤ C)
    (b : F ⋙ Functor.const SimplexCategoryᵒᵖ ⟶ R)
    (hF : ∀ k, IsFibrant (F.obj k)) (hR : ∀ k n, IsFibrant ((R.obj k).obj n))
    (hb : ∀ k n, weakEquivalences C ((b.app k).app n)) (k : K) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((leftDiagramComparison K A F R b).app k)) := by
  have := hF k
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftComparison_isIso A hA (b.app k) (hR k) (hb k)

/-- 概要：右 frame からの図式比較は各値で局所化同値（Hovey §5）。
方針：反対圏の左比較と同次元の反転同型を使う。
規約：混合 Hom の Kan 性は要求しない。
使われ方：右側の比較を重み付き錐へ移す。 -/
lemma rightDiagramComparison_isIso
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    {X : C} [IsCofibrant X] (a : A ⟶ (Functor.const SimplexCategory).obj X)
    (ha : ∀ n, weakEquivalences C (a.app n)) (R : K ⥤ SimplexCategoryᵒᵖ ⥤ C)
    (hR : ∀ k, reedyLeft simplex (cofibrations Cᵒᵖ) (initial.to (R.obj k).rightOp)) (k : K) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((rightDiagramComparison K A a R).app k)) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightComparison_isIso A hA a ha (R.obj k) (hR k)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MixedFrameDiagrams
