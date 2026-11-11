module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitMappingKan
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PostcompositionAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialOpposite

/-!
概要：右関手を固定した、関手圏全体における普遍単位の可縮空間。
方針：後合成の随伴の単位を comma の始対象へ移し、反転して終対象の空間を使う。
規約：実単位の対応の射影ファイバーとの比較は別工程であり、ここでは同一視しない。
使われ方：右射影のファイバーの可縮性を証明する比較先。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：右関手 R への単位 id→RL を保持する、全関手圏の comma。
方針：R による後合成の、恒等関手の頂点上の comma fiber を取る。
規約：L の保存条件や単位の普遍性はまだ課さない。
使われ方：普遍単位を始対象として特徴づける周囲の圏。 -/
def RightUnitComma (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj))

instance rightUnitComma_quasicategory (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) : Quasicategory (RightUnitComma C D w) := by
  change Quasicategory
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber ((ihom C.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor w)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)))
  infer_instance

/-- 概要：右関手を固定した全関手圏の comma には始対象が存在する。
方針：d の左随伴を関手圏の後合成の随伴に移し、その単位の普遍性を使う。
規約：パラメータは元の C 全体であり、各対象だけの普遍性ではない。
使われ方：単位の選択の可縮性の存在側。 -/
lemma rightUnitComma_hasInitial (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) :
    ∃ x : RightUnitComma C D w _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  let a := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenLeftAdjunction w) C.obj
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex a.unitHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C.obj)), ?_⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaInitialCondition_iff a.unitHom).mp
    a.unitMappingSpaceCondition.unitCommaInitialCondition _

/-- 概要：右関手に対する普遍単位の空間。
方針：comma を反転し、その終対象の全部分複体を取る。
規約：始対象を反転した模型であり、随伴の証拠の離散集合にはしない。
使われ方：実単位の右射影のファイバーの比較先。 -/
def RightUniversalUnitSpace (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) : SSet.{u + 1} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (RightUnitComma C D w).op : SSet.{u + 1})

/-- 概要：固定した右関手に対する普遍単位の空間は可縮。
方針：後合成の随伴による始対象の存在を反転し、終対象空間の可縮性を使う。
規約：全高次の境界の充填による IsContractibleKan を証明する。
使われ方：右射影の高次ファイバーの比較で必要な可縮な模型。 -/
lemma rightUniversalUnitSpace_isContractibleKan (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u})
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (RightUniversalUnitSpace C D w) := by
  obtain ⟨x, hx⟩ := rightUnitComma_hasInitial C D w
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices_isContractibleKan ⟨SSet.opObjEquiv.symm x, hx.op_isTerminalVertex⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
