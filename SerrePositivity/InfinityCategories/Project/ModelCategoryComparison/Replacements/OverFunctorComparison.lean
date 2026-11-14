module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.SourceInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor

/-!
# 任意の関手上の frame 族と選んだ resolution の自然比較

概要：Hovey §5 の弱い augmentation を持つ frame を関手上の選んだ resolution と比較する。
方針：実際の共通 cofibrant frame への二つの Hom 比較を anodyne 反転後に逆にする。
規約：パラメータ圏のモデル構造も単体集合のモデル構造も要求しない。
使われ方：定値 E 代数図式の具体的な frame と導来写像空間の比較。
-/

@[expose] public section

noncomputable section

universe u v uB vB uD vD

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory Limits HomotopicalAlgebra
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {B : Type uB} [Category.{vB} B]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (q : CofibrantResolutionFamily (C := C) simplex) (H : B ⥤ C)
  (P : B ⥤ SimplexCategory ⥤ C) (a : P ⟶ H ⋙ Functor.const SimplexCategory)
  {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL

/-- 概要：共通 frame への左 Hom 比較は anodyne 反転後に同型（Hovey §5）。
方針：augmentation の弱同値性から共通 frame の左射の弱同値性を使う。
規約：終域は fibrant、パラメータ圏にモデル構造は不要。
使われ方：元の関手上の選んだ resolution と具体的な frame の比較。 -/
lemma overFunctor_left_isIso (ha : ∀ X n, weakEquivalences C ((a.app X).app n))
    (X : Bᵒᵖ) (Y : C) [IsFibrant Y] :
    IsIso (L.map (((FrameOverFunctor.homLeft cof q H P a).app X).app Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.source_weakEquivalence_isIso L hL ((FrameOverFunctor.left cof q H P a).app X.unop)
    (FrameOverFunctor.commonObj_cofibrant cof q H P a X.unop) (q.cofibrant (H.obj X.unop))
    (FrameOverFunctor.left_weakEquivalence cof q H P a ha X.unop) Y

/-- 概要：共通 frame への右 Hom 比較は anodyne 反転後に同型（Hovey §5）。
方針：共通 frame の右射の弱同値性と両 frame の cofibrancy を使う。
規約：実際の二つの自然な比較射を保持する。
使われ方：具体的な frame の Hom を選んだ導来写像空間へ比較する。 -/
lemma overFunctor_right_isIso
    (hP : ∀ X, reedyLeft simplex (cofibrations C) (initial.to (P.obj X)))
    (X : Bᵒᵖ) (Y : C) [IsFibrant Y] :
    IsIso (L.map (((FrameOverFunctor.homRight cof q H P a).app X).app Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.source_weakEquivalence_isIso L hL ((FrameOverFunctor.right cof q H P a).app X.unop)
    (FrameOverFunctor.commonObj_cofibrant cof q H P a X.unop) (hP X.unop)
    (FrameOverFunctor.right_weakEquivalence cof q H P a X.unop) Y

/-- 概要：関手上の frame の選択比較は両変数で自然な同型（Hovey §5）。
方針：共通 frame の二つの自然変換を反転後に合成する。
規約：すべての終域が fibrant な元のモデル圏だけを使う。
使われ方：定値図式の具体的な frame と実際の図式の Map^h の比較。 -/
def overFunctorChoiceIso
    (ha : ∀ X n, weakEquivalences C ((a.app X).app n))
    (hP : ∀ X, reedyLeft simplex (cofibrations C) (initial.to (P.obj X)))
    (hfib : ∀ Y : C, IsFibrant Y) :
    FrameOverFunctor.hom (FrameOverFunctor.resolution q H) ⋙
        (Functor.whiskeringRight C SSet.{v} D).obj L ≅
      FrameOverFunctor.hom P ⋙ (Functor.whiskeringRight C SSet.{v} D).obj L := by
  let post := (Functor.whiskeringRight C SSet.{v} D).obj L
  let l := Functor.whiskerRight (FrameOverFunctor.homLeft cof q H P a) post
  let r := Functor.whiskerRight (FrameOverFunctor.homRight cof q H P a) post
  have : ∀ X, IsIso (l.app X) := by
    intro X
    have : ∀ Y, IsIso ((l.app X).app Y) := by
      intro Y
      have := hfib Y
      exact overFunctor_left_isIso cof q H P a L hL ha X Y
    exact NatIso.isIso_of_isIso_app _
  have : IsIso l := NatIso.isIso_of_isIso_app l
  have : ∀ X, IsIso (r.app X) := by
    intro X
    have : ∀ Y, IsIso ((r.app X).app Y) := by
      intro Y
      have := hfib Y
      exact overFunctor_right_isIso cof q H P a L hL hP X Y
    exact NatIso.isIso_of_isIso_app _
  have : IsIso r := NatIso.isIso_of_isIso_app r
  exact asIso l ≪≫ (asIso r).symm

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
