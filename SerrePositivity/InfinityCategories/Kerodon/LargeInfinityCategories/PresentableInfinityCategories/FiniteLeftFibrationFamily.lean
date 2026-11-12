module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteLeftFibrationPresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFamilyGeneratorTransport

/-!
概要：有限底上模型の全表示の各項を、同じ小さい符号族の同型飽和へ入れる。
方針：底上の符号同型を連続置換で送り、strict な逆条件を coherent nerve の頂点同型にする。
規約：元の底への射と全表示の各項を保持し、族の小ささは宇宙 u で述べる。
使われ方：一般の前層の小さい compact 全部分生成圏。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：同じ小さい有限底上符号を left fibration ∞ 圏の頂点族へ実現する。
方針：各符号の実現に元の連続置換を適用する。
規約：符号型は底と同じ宇宙 u。
使われ方：小さい全部分生成圏の対象族。 -/
def finiteLeftFibrationGeneratorVertex {B : SSet.{u}} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverCode B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject q.realization)

/-- 概要：底上の同型は、同じ連続置換後の元の ∞ 圏で頂点同型を与える。
方針：元の置換関手で同型を送り、豊穣 Hom の strict な逆条件を使う。
規約：元の同型の順方向と逆方向を同時に送る。
使われ方：有限模型の全表示の各項を共通の小さい族へ比較する。 -/
def continuousReplacementLeftFibrationVertexIso {B : SSet.{u}} {X Y : Over B} (e : X ≅ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject Y)) := by
  let r := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousLeftFibrationObjectFunctor B).mapIso e
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r.hom) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_isInvertible_of_enrichedInverse r.hom r.inv
    · rw [r.hom_inv_id]
    · rw [r.inv_hom_id]
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r.hom).toTruncated) := hi
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r.hom).toTruncated)

/-- 概要：元の有限模型の全表示は、全て同じ小さい符号族の同型飽和内にある。
方針：各有限部分複体の底上の符号同型を、同じ置換後の頂点同型へ移す。
規約：任意の nerve 頂点で述べ、全表示の各項を保持する。
使われ方：小さい生成圏による元の指定対象の生成性。 -/
lemma finiteLeftFibrationDiagram_in_family {B : SSet.{u}} (X : Over B)
    (a : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation.FiniteOverPieces X)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FamilySaturation (finiteLeftFibrationGeneratorVertex (B := B))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteLeftFibrationDiagram X)).app _ (ULift.up a)) := by
  obtain ⟨A, rfl⟩ := nerveEquiv.symm.surjective a
  have : ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation.finiteOverPiecesDiagram X).obj A).left.Finite := inferInstanceAs A.val.toSSet.Finite
  obtain ⟨q, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_finiteOverCode ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation.finiteOverPiecesDiagram X).obj A)
  refine ⟨q, ⟨?_⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteLeftFibrationDiagram X)).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A)))
    (finiteLeftFibrationGeneratorVertex q)
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.continuousReplacementLeftFibrationObject ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation.finiteOverPiecesDiagram X).obj A)))
    (finiteLeftFibrationGeneratorVertex q)
  exact continuousReplacementLeftFibrationVertexIso e.symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
