module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeMappingSpan

/-!
概要：right fibration の比較 span から底の pinched Hom と頂点 fiber の実際の比較射を作る。
方針：span の自明 Kan fibration の切断を取り、始点評価へ合成する。
規約：切断の選択を含み、底の頂点や終点に関する自然性は主張しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の比較射の導来ファイバーの模型。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：span の底の slice fiber は底の始点と終点の右 pinched Hom と同型。
方針：終点の Yoneda 表示の後合成を同定し、点上の slice fiber の既存の同型を使う。
規約：射 r と二頂点に充填性は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の比較 span の始域の写像空間表示。 -/
noncomputable def rightFibrationMappingBaseIso {E B : SSet.{u}} (r : E ⟶ B)
    (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c ≫ r)) x ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x (r.app (Opposite.op ⦋0⦌) c) := by
  have h : SSet.yonedaEquiv.symm c ≫ r =
      SSet.yonedaEquiv.symm (r.app (Opposite.op ⦋0⦌) c) := by
    rw [SSet.yonedaEquiv_symm_comp]
  exact (eqToIso (congrArg (fun t : (Δ[0] : SSet.{u}) ⟶ B ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection t) x) h)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x (r.app (Opposite.op ⦋0⦌) c)).symm

/-- 概要：比較 span の中間空間を底の右 pinched Hom へ射影する。
方針：slice fiber への射影に、その写像空間表示の同型を後合成する。
規約：底の終点は r(c)。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の比較射の始域の同値な置換。 -/
noncomputable def rightFibrationMappingHomProjection {E B : SSet.{u}} (r : E ⟶ B)
    (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingTotal r c x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x (r.app (Opposite.op ⦋0⦌) c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingProjection r c x ≫ (rightFibrationMappingBaseIso r c x).hom

/-- 概要：底の pinched Hom への比較 span の射影は自明 Kan fibration。
方針：slice fiber への自明 Kan fibration と厳密な同型を合成する。
規約：B の quasicategory 性は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の比較射を定義する切断の存在。 -/
instance rightFibrationMappingHomProjection_trivialKanFibration {E B : SSet.{u}}
    (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r] (c : E.obj (Opposite.op ⦋0⦌))
    (x : B.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (rightFibrationMappingHomProjection r c x) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingProjection r c x))
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 概要：底の pinched Hom から比較 span への切断を一つ選ぶ。
方針：自明 Kan fibration の切断の存在を使う。
規約：x・c に関する自然性を仮定も主張もしない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の代表を固定した比較射。 -/
noncomputable def rightFibrationMappingSection {E B : SSet.{u}} (r : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r] (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x (r.app (Opposite.op ⦋0⦌) c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingTotal r c x :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (rightFibrationMappingHomProjection r c x))

/-- 概要：選んだ切断を底の写像空間へ戻す合成は恒等射。
方針：切断の存在の仕様を読む。
規約：選択した切断そのものに関する厳密な等式。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の比較の始域の回収。 -/
lemma rightFibrationMappingSection_projection {E B : SSet.{u}} (r : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r] (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌)) :
    rightFibrationMappingSection r c x ≫ rightFibrationMappingHomProjection r c x =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x (r.app (Opposite.op ⦋0⦌) c)) :=
  Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (rightFibrationMappingHomProjection r c x))

/-- 概要：終点 c へ向かう底の写像空間から、始点 x 上の fiber への比較射。
方針：選んだ切断で写像空間の span の中間空間へ移し、始点を評価する。
規約：strict な fiber の同型と導来ファイバーの比較は区別する。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の right fibration における表現可能な比較射の模型。 -/
noncomputable def rightFibrationHomComparison {E B : SSet.{u}} (r : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration r] (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x (r.app (Opposite.op ⦋0⦌) c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r x :=
  rightFibrationMappingSection r c x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation r c x

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
