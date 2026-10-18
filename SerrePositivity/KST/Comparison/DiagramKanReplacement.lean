module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
public import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitWeakEquivalence

/-!
# 図式の射の関手的な成分ごとの Kan 分解

概要：単体集合の図式の射を、成分ごとに anodyne な射と Kan fibration に分解する。
方針：arrow 圏の図式に既存の関手的な anodyne–Kan 分解を適用する。
規約：Mather 1976 Lemma 21 の fibration への還元に対応する厳密な図式。
使われ方：span の三つの縦射を図式と整合したまま置換する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel
variable {D : Type v} [Category.{w} D] {F G : D ⥤ SSet.{u}}

/--
概要：図式の射の関手的な分解の中間図式。
方針：各成分を arrow としてまとめ、中間対象の関手を後合成する。
規約：図式の射の中間対象を個別に選ぶのではなく、既存の関手的な選択を使う。
使われ方：置換後の span の対象と二つの脚。
-/
def diagramKanMiddle (α : F ⟶ G) : D ⥤ SSet.{u} :=
  SerrePositivity.DiagramModel.arrowDiagram α ⋙ AnodyneKanReplacement.factorization.Z

/--
概要：元の図式から中間図式への単位。
方針：成分ごとの anodyne 分解の前半を、分解の自然性でまとめる。
規約：全ての成分は実際に選択された分解の射。
使われ方：置換前後の円筒の比較。
-/
def diagramKanUnit (α : F ⟶ G) : F ⟶ diagramKanMiddle α where
  app d := AnodyneKanReplacement.factorization.i.app (Arrow.mk (α.app d))
  naturality {_ _} f :=
    AnodyneKanReplacement.factorization.i.naturality
      ((SerrePositivity.DiagramModel.arrowDiagram α).map f)

/--
概要：中間図式から元の終域図式への射影。
方針：成分ごとの Kan 分解の後半を、分解の自然性でまとめる。
規約：元の図式の射と同じ終域を持つ。
使われ方：三つの縦射が Kan fibration である span への還元。
-/
def diagramKanProjection (α : F ⟶ G) : diagramKanMiddle α ⟶ G where
  app d := AnodyneKanReplacement.factorization.p.app (Arrow.mk (α.app d))
  naturality {_ _} f :=
    AnodyneKanReplacement.factorization.p.naturality
      ((SerrePositivity.DiagramModel.arrowDiagram α).map f)

/--
概要：図式の単位と射影の合成は元の射である。
方針：各成分で分解の因子化の式を使う。
規約：等式は自然変換として厳密に成立する。
使われ方：円筒の比較の合成の同定。
-/
theorem diagramKan_fac (α : F ⟶ G) : diagramKanUnit α ≫ diagramKanProjection α = α := by
  apply NatTrans.ext
  funext d
  exact AnodyneKanReplacement.factorization.fac_app (f := Arrow.mk (α.app d))

/--
概要：図式の単位の各成分は anodyne である。
方針：選択した関手的な分解の前半の性質を使う。
規約：成分ごとの性質であり、図式圏のモデル構造は仮定しない。
使われ方：三つの頂点と円筒の置換の局所化可逆性。
-/
theorem diagramKanUnit_anodyne (α : F ⟶ G) (d : D) :
    SSet.anodyneExtensions ((diagramKanUnit α).app d) :=
  (AnodyneKanReplacement.factorization.factorizationData (α.app d)).hi

/--
概要：図式の射影の各成分は Kan fibration である。
方針：選択した関手的な分解の後半の性質を使う。
規約：基底の図式の各対象の Kan 性を要求しない。
使われ方：span の三つの縦射の Kan 条件。
-/
theorem diagramKanProjection_rlp (α : F ⟶ G) (d : D) :
    SSet.modelCategoryQuillen.J.rlp ((diagramKanProjection α).app d) :=
  (AnodyneKanReplacement.factorization.factorizationData (α.app d)).hp

end SerrePositivity.KST.Comparison
