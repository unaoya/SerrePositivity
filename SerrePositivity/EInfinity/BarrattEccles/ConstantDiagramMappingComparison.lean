module

public import SerrePositivity.EInfinity.BarrattEccles.DiagramMappingSpace
public import SerrePositivity.EInfinity.BarrattEccles.ConstantDiagramFrameComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.OverFunctorComparison

/-!
# 定値図式の導来写像空間と構成した frame の自然比較

概要：BM 命題 4.1・Hovey §5 の図式 Map^h を具体的な定値図式 frame と比較する。
方針：元の定値図式上の共通 cofibrant frame への二つの射を反転する。
規約：全比較は原始域・終域図式に自然で、単体集合モデルを仮定しない。
使われ方：一般 homotopy 極限の右導来普遍性の重み付き Hom 比較。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]
  {D : Type w} [Category.{v} D] (L : SSet.{u} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

/-- 概要：定値図式の Map^h と具体的な frame Hom は両変数で自然に同型（Hovey §5）。
方針：全次元で弱同値な augmentation を持つ frame の自然比較を使う。
規約：同型は任意の anodyne を反転する関手の後で構成する。
使われ方：定値図式からの導来 Hom を具体的な錐へ移す。 -/
def constantDiagramFrameMappingComparisonIso :
    (Functor.const K : (operad A).Algebra ⥤ _).op ⋙ Diagram.mappingSpace A K ⋙
        (Functor.whiskeringRight (K ⥤ (operad A).Algebra) SSet.{u} D).obj L ≅
      (constantDiagramFrameFamily A K).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙
        (Functor.whiskeringRight (K ⥤ (operad A).Algebra) SSet.{u} D).obj L := by
  let := Diagram.projectiveModelCategory A K
  let cof := Diagram.mappingCofibrantFactorization A K
  let q := cosimplicialResolutionFamily cof
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.overFunctorChoiceIso cof q (Functor.const K) (constantDiagramFrameFamily A K)
    (constantDiagramFrameAugmentation A K) L hL
    (constantDiagramFrameComparison_weakEquivalence A K)
    (constantDiagramFrame_reedyCofibrant A K) (Diagram.isFibrant A K)

/-- 概要：定値図式の Map^h は始域 frame の重み付き錐と自然に同型（Hovey §5.4）。
方針：frame 選択の比較と実際のテンソル随伴 Hom 同型を合成する。
規約：終域図式の全射に自然で、元の始域代数に cofibrancy を要求しない。
使われ方：右 frame の錐との比較を導来 Hom の普遍性へ接続する。 -/
def constantDiagramSourceMappingComparisonIso (Y : (operad A).Algebra) :
    (Diagram.mappingSpace A K).obj (Opposite.op ((Functor.const K).obj Y)) ⋙ L ≅
      constantDiagramSourceHom A K Y ⋙ L :=
  (constantDiagramFrameMappingComparisonIso A K L hL).app (Opposite.op Y) ≪≫
    Functor.isoWhiskerRight (constantDiagramFrameHomIso A K Y) L

end SerrePositivity.EInfinity.BarrattEccles
