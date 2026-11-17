module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.TargetInvariance
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence
public import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
# 両側の frame の混合 Hom への比較は局所化同値

概要：Hovey §5 の始域 frame と右 frame の Hom を同じ混合 Hom へ比較する。
方針：各行の frame Hom の不変性と二重単体集合の対角の局所化不変性を使う。
規約：単体集合の完全なモデル構造は要求せず、anodyne 局所化で読む。
使われ方：両側の frame の重み付き錐を自然に比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C)

private def rowsComparison {Z : C} {R : SimplexCategoryᵒᵖ ⥤ C}
    (b : (Functor.const SimplexCategoryᵒᵖ).obj Z ⟶ R) :
    (Functor.const SimplexCategoryᵒᵖ).obj ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z) ⟶
      R ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A where
  app n := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map (b.app n)
  naturality n m f := by
    ext s h
    change h ≫ b.app m = (h ≫ b.app n) ≫ R.map f
    have hb : b.app m = b.app n ≫ R.map f :=
      (Category.id_comp _).symm.trans (b.naturality f)
    rw [hb, Category.assoc]

private lemma leftComparison_eq {Z : C} {R : SimplexCategoryᵒᵖ ⥤ C}
    (b : (Functor.const SimplexCategoryᵒᵖ).obj Z ⟶ R) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.leftComparison A b = (DiagonalFrame.constantIso ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z)).inv ≫
      BisimplicialModel.diagonal.map (rowsComparison A b) := by
  ext n h
  rfl

private lemma rightComparison_eq {X : C} (a : A ⟶ (Functor.const SimplexCategory).obj X)
    (R : SimplexCategoryᵒᵖ ⥤ C) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightComparison A a R = (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightHomIso X R).hom ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.leftComparison (C := Cᵒᵖ) R.rightOp (Z := op X) (R := A.op) (NatTrans.op a) ≫
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.flipIso A R).inv := by
  ext n h
  rfl

variable [ModelCategory C]

/-- 概要：cofibrant 対象の反対対象は fibrant（Hovey §1.1）。
方針：初期対象からの cofibration を反転し、終対象への fibration にする。
規約：反対圏のモデルは元のモデルからの標準のもの。
使われ方：右 frame Hom の始域の条件を確認する。 -/
lemma fibrantOp_of_cofibrant (X : C) [IsCofibrant X] : IsFibrant (op X) :=
  (isFibrant_iff_of_isTerminal (initial.to X).op initialIsInitial.op).mpr inferInstance

/-- 概要：始域 frame Hom から混合 Hom への比較は局所化同値（Hovey §5）。
方針：終域の各値の弱同値を frame Hom で反転し、対角へ移す。
規約：元の終域と右 frame の各値の fibrancy を明示する。
使われ方：始域 frame の錐の側の共同比較。 -/
lemma leftComparison_isIso
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    {Z : C} [IsFibrant Z] {R : SimplexCategoryᵒᵖ ⥤ C}
    (b : (Functor.const SimplexCategoryᵒᵖ).obj Z ⟶ R)
    (hR : ∀ n, IsFibrant (R.obj n)) (hb : ∀ n, weakEquivalences C (b.app n)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.leftComparison A b)) := by
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map
      (BisimplicialModel.diagonal.map (rowsComparison A b))) := by
    apply BisimplicialModel.localized_diagonal_map
    intro n
    have := hR n
    have : IsFibrant (((Functor.const SimplexCategoryᵒᵖ).obj Z).obj n) :=
      inferInstanceAs (IsFibrant Z)
    have : WeakEquivalence (b.app n) := ⟨hb n⟩
    exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.target_weakEquivalence_isIso A hA AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) (b.app n)
  rw [leftComparison_eq, Functor.map_comp]
  infer_instance

/-- 概要：右 frame Hom から同じ混合 Hom への比較は局所化同値（Hovey §5）。
方針：反対圏の左比較へ移し、同次元の射の反転同型を合成する。
規約：元の始域は cofibrant、両 frame の Reedy cofibrancy を使う。
使われ方：右 frame の錐の側の共同比較。 -/
lemma rightComparison_isIso
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    {X : C} [IsCofibrant X] (a : A ⟶ (Functor.const SimplexCategory).obj X)
    (ha : ∀ n, weakEquivalences C (a.app n)) (R : SimplexCategoryᵒᵖ ⥤ C)
    (hR : reedyLeft simplex (cofibrations Cᵒᵖ) (initial.to R.rightOp)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.rightComparison A a R)) := by
  have : IsFibrant (op X) := fibrantOp_of_cofibrant X
  have hv (n : SimplexCategoryᵒᵖ) : IsFibrant (A.op.obj n) := by
    have := cosimplicialFrame_isCofibrant_obj A hA n.unop
    exact fibrantOp_of_cofibrant _
  have hw (n : SimplexCategoryᵒᵖ) : weakEquivalences Cᵒᵖ ((NatTrans.op a).app n) := by
    change weakEquivalences C (a.app n.unop)
    exact ha n.unop
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedFrame.leftComparison (C := Cᵒᵖ) R.rightOp (Z := op X) (R := A.op) (NatTrans.op a))) :=
    leftComparison_isIso (C := Cᵒᵖ) R.rightOp hR (Z := op X) (R := A.op) (NatTrans.op a) hv hw
  rw [rightComparison_eq, Functor.map_comp, Functor.map_comp]
  infer_instance

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
