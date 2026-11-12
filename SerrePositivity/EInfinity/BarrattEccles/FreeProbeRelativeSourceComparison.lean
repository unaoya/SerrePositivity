module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeCAlgSource
public import SerrePositivity.EInfinity.BarrattEccles.CAlgVertexPresentation
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementColumn
public import SerrePositivity.EInfinity.SimplicialLocalization.WeakNerveInverts
/-!
概要：元の自由 probe の選択済み CAlg_R 頂点と同じ cofibrant 局所化源を比較する。
方針：元の cofibrant 置換 augmentation の頂点同型と既存の全源頂点比較を使う。
規約：選択済み自由頂点と元の置換比較を保持する。
使われ方：局所化源で証明した単位比較を既存の標準単位比較へ輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A)

/-- 概要：元の全自由源の頂点は同じ通常置換の局所化源頂点。
方針：元の零単体の全後合成を計算する。
規約：同じ置換対象を保持。使われ方：端点同型の元の成分辺への回収。 -/
lemma freeProbeCAlgSource_relativeReplacement_vertex :
    (freeProbeCAlgSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) =
    (cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1}
        ((cofibrantAlgebraReplacement A).obj (freeProbeElementCofibrantSource A X).obj))) := by
  apply congrArg ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌))
  exact ComposableArrows.ext₀ rfl

/-- 概要：元の全自由源の頂点と同じ cofibrant 局所化源頂点の同型。
方針：同じ置換 augmentation の実反転辺と零単体の表示等式を使う。
規約：元の置換比較射を保持。使われ方：実 U の全源自然性による単位の端点照合。 -/
def freeProbeRelativeFullSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((freeProbeCAlgSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
      ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (freeProbeRelativeElementSource A X))) := by
  let C := cofibrantAlgebraRelativeCategory A
  let f := (cofibrantDKComparison A).app (freeProbeRelativeElementSource A X)
  have : IsIso (Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk f).map (cAlgLocalizationSource A)).toTruncated) :=
    SimplicialLocalization.weakNerveEdges_inverts_arrows C _
      (cAlgLocalizationSource_inverts A) f
      (cofibrantDKComparison_weak A (freeProbeRelativeElementSource A X))
  exact eqToIso (congrArg HomotopyCategory.mk
    (freeProbeCAlgSource_relativeReplacement_vertex A X)) ≪≫
      asIso (Truncated.HomotopyCategory.homMk ((nerve.edgeMk f).map
        (cAlgLocalizationSource A)).toTruncated)

/-- 概要：選択済み自由代数頂点と元の cofibrant 局所化源頂点の同型。
方針：既存の自由源の頂点比較の逆を同じ置換 augmentation の同型へ接続する。
規約：選択済み頂点を変更しない。使われ方：標準単位比較の自由側端点輸送。 -/
def freeProbeRelativeChosenSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (cAlgVertex A ((freeProbeFunctor A).obj X))
      ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (freeProbeRelativeElementSource A X))) :=
  (freeProbeCAlgSource_vertexIso A X).symm ≪≫ freeProbeRelativeFullSourceIso A X

/-- 概要：元の全自由源の端点同型の順射は同じ置換 augmentation の局所化像。
方針：同じ端点同型の定義の順射を回収する。
規約：元の比較射を保持。使われ方：実 U の全源自然性への代入。 -/
lemma freeProbeRelativeFullSourceIso_hom :
    (freeProbeRelativeFullSourceIso A X).hom =
    eqToHom (congrArg HomotopyCategory.mk (freeProbeCAlgSource_relativeReplacement_vertex A X)) ≫
      Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk ((cofibrantDKComparison A).app (freeProbeRelativeElementSource A X))).map
          (cAlgLocalizationSource A)).toTruncated := rfl

end SerrePositivity.EInfinity.BarrattEccles
