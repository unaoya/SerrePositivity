module

public import SerrePositivity.InfinityCategories.F2.KanIntervalCospan
public import SerrePositivity.InfinityCategories.F2.StrictCoherentNatTransComponent
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible
public import SerrePositivity.InfinityCategories.F1B.WeakWhitehead

/-!
概要：元と path 置換後の Kan cospan の coherent な図式は同型。
方針：比較の全成分の弱同値性を Whitehead 判定と coherent 円柱へ渡す。
規約：成分ごとに逆を選んだ自然変換は仮定しない。
使われ方：元の cospan の極限錐を path 模型と同じ頂点で構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {X Y Z : KanObject.{u}}

/-- 概要：cospan の定値 path の比較は全ての成分で弱ホモトピー同値。
方針：第一入力では切断の弱同値性、他では恒等射の弱同値性を使う。
規約：元の f と g は任意。使われ方：図式全体の同型の構成。 -/
lemma intervalCospanSection_isWeakHomotopyEquivalence (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    IsWeakHomotopyEquivalence ((intervalCospanSection f g).app i) := by
  rcases i with ⟨_ | ⟨_ | _⟩⟩
  · change IsWeakHomotopyEquivalence (𝟙 Y.obj)
    exact (isPrecompositionEquivalence_id Y.obj).isWeakHomotopyEquivalence
  · change IsWeakHomotopyEquivalence (intervalReplacementSection (show X.obj ⟶ Y.obj from f))
    exact intervalReplacementSection_isWeakHomotopyEquivalence f
  · change IsWeakHomotopyEquivalence (𝟙 Z.obj)
    exact (isPrecompositionEquivalence_id Z.obj).isWeakHomotopyEquivalence

/-- 概要：cospan の比較の各成分の coherent な辺は可逆。
方針：Kan 複体の弱同値性を Whitehead 判定で移す。
規約：指定された成分の辺。使われ方：指定 prism の垂直辺の判定。 -/
lemma intervalCospanSection_component_isInvertible (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    IsInvertibleEdge (coherentNerveEdge ((intervalCospanSection f g).app i)) := by
  have h := intervalCospanSection_isWeakHomotopyEquivalence f g i
  exact coherentKanEdge_isInvertible_of_isQCatEquivalence
    (f := (intervalCospanSection f g).app i) h.isSimplicialHomotopyEquivalence.isQCatEquivalence

/-- 概要：任意の Kan cospan と path 置換後の cospan の coherent 表示は関手同型。
方針：全成分が可逆な通常の自然変換の標準 coherent 円柱を使う。
規約：指定された図式そのものの同型。使われ方：極限の普遍性の輸送。 -/
def kanIntervalCospanDiagramIso (f : X ⟶ Y) (g : Z ⟶ Y) :
    FunctorIso (strictCoherentDiagram (kanPullbackDiagram f g))
      (strictCoherentDiagram (kanPullbackDiagram (intervalReplacementKanEndpoint f) g)) := by
  apply strictCoherentNatTransIso (intervalCospanSection f g)
  exact intervalCospanSection_component_isInvertible f g

end SerrePositivity.InfinityCategories.F2
