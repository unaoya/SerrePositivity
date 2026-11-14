module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.SourceInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameComparison

/-!
# Frame の選択に関する自然な比較の反転

概要：Hovey §5 の frame の共通比較の二つの Hom 射は anodyne 反転後に同型になる。
方針：関手的な共通 cofibrant 比較の弱同値性と始域不変性を使う。
規約：単体集合の完全なモデル構造を仮定しない。
使われ方：E2a-5 の写像空間の frame の選択独立性と一般極限の frame 比較。
-/

@[expose] public section

noncomputable section

universe u v u' v'

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (q : CofibrantResolutionFamily (C := C) simplex) (p : CosimplicialFrameFamily (C := C))
  (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y))
  {D : Type u'} [Category.{v'} D] (L : SSet.{v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hR hL

/-- 概要：標準分解の Hom と共通 frame の Hom の比較は anodyne 反転後に同型（Hovey §5）。
方針：共通比較の Reedy cofibrancy と左射の各成分の弱同値性を使う。
規約：比較は元の両変数に自然な実際の単体集合の射。
使われ方：選んだ分解の Hom を別の frame と比較する。 -/
lemma comparison_left_isIso (X : Cᵒᵖ) (Y : C) :
    IsIso (L.map (((FrameComparison.homLeft cof q p R).app X).app Y)) := by
  have := hR Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.source_weakEquivalence_isIso L hL ((FrameComparison.left cof q p).app X.unop)
    (FrameComparison.commonObj_cofibrant cof q p X.unop) (q.cofibrant X.unop)
    (FrameComparison.left_weakEquivalence cof q p X.unop) (R.obj Y)

/-- 概要：別の frame の Hom と共通 frame の Hom の比較も anodyne 反転後に同型（Hovey §5）。
方針：共通比較の右射の弱同値性と始域不変性を使う。
規約：別の frame の augmentation は各成分の弱同値で足りる。
使われ方：自然な同型の zigzag による frame の選択独立性。 -/
lemma comparison_right_isIso (X : Cᵒᵖ) (Y : C) :
    IsIso (L.map (((FrameComparison.homRight cof q p R).app X).app Y)) := by
  have := hR Y
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.source_weakEquivalence_isIso L hL ((FrameComparison.right cof q p).app X.unop)
    (FrameComparison.commonObj_cofibrant cof q p X.unop) (p.cofibrant X.unop)
    (FrameComparison.right_weakEquivalence cof q p X.unop) (R.obj Y)

/-- 概要：二つの frame の Hom は anodyne 反転後に二変数で自然同型（Hovey §5）。
方針：共通 frame への二つの自然変換を成分ごとに反転して合成する。
規約：元の対象の両変数に自然で、成分ごとの任意の同型は選ばない。
使われ方：導来写像空間の frame の選択独立性。 -/
def frameChoiceIso :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom q.obj R ⋙ (Functor.whiskeringRight C SSet.{v} D).obj L ≅
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom p.obj R ⋙ (Functor.whiskeringRight C SSet.{v} D).obj L := by
  let post := (Functor.whiskeringRight C SSet.{v} D).obj L
  let left := Functor.whiskerRight (FrameComparison.homLeft cof q p R) post
  let right := Functor.whiskerRight (FrameComparison.homRight cof q p R) post
  have : ∀ X, IsIso (left.app X) := fun X => by
    have : ∀ Y, IsIso ((left.app X).app Y) :=
      fun Y => comparison_left_isIso cof q p R hR L hL X Y
    exact NatIso.isIso_of_isIso_app _
  have : IsIso left := NatIso.isIso_of_isIso_app _
  have : ∀ X, IsIso (right.app X) := fun X => by
    have : ∀ Y, IsIso ((right.app X).app Y) :=
      fun Y => comparison_right_isIso cof q p R hR L hL X Y
    exact NatIso.isIso_of_isIso_app _
  have : IsIso right := NatIso.isIso_of_isIso_app _
  exact (asIso left).trans (asIso right).symm

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
