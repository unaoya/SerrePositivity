module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransportEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：left fibration の strict transport の weighted nerve と、その fiber の比較。
方針：相対関手空間の通常の図式を weighted nerve に写し、係数値の同型と恒等射評価を合成する。
規約：全空間の射影の充填性や元の fibration との全体比較は後続で証明する。
使われ方：Kerodon §§5.3.3（Tag 025W）–5.3.5（Tag 037H）、strict transport からの fibration の復元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：strict transport を単体集合値の通常の関手として束縛する。
方針：相対関手空間と undercategory による前合成の恒等・合成則を使う。
規約：Kan 性を忘れた図式の定義には p の left fibration 性を要求しない。
使われ方：Kerodon §§5.3.1（Tag 035D）–5.3.3（Tag 025W）、weighted nerve に入れる係数図式。 -/
@[kerodon 035E]
def leftStrictTransportDiagram {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : C ⥤ SSet.{u} where
  obj c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport p c
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMap p f
  map_id c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMap_id p c
  map_comp f g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMap_comp p f g

/-- 概要：strict transport 表現を係数とする weighted nerve の全空間。
方針：単体集合値の strict transport 図式の weighted nerve を取る。
規約：この時点では元の全空間 E との同値を主張しない。
使われ方：Kerodon §§5.3.3（Tag 025W）–5.3.5（Tag 037H）、strict transport からの復元候補。 -/
def leftStrictTransportWeightedNerve {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : SSet.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (leftStrictTransportDiagram p)

/-- 概要：strict transport の weighted nerve から底の nerve への射影。
方針：weighted nerve の各単体の底の射列を取り出す。
規約：元の p と同じ底を持つ。
使われ方：Kerodon §§5.3.3（Tag 025W）–5.3.5（Tag 037H）、底上で元の fibration と比較する射影。 -/
def leftStrictTransportWeightedProjection {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) : leftStrictTransportWeightedNerve p ⟶ nerve C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (leftStrictTransportDiagram p)

/-- 概要：left fibration の strict transport の weighted nerve の fiber は Kan 複体。
方針：strict transport の値の Kan 性と weighted nerve の fiber の同型を使う。
規約：全空間の quasicategory 性を仮定しない。
使われ方：Kerodon §§5.3.3（Tag 025W）–5.3.5（Tag 037H）、復元候補の fiber の比較の始域。 -/
instance leftStrictTransportWeightedFiber_kanComplex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (c : C) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (leftStrictTransportWeightedProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  have : KanComplex ((leftStrictTransportDiagram p).obj c) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport_kanComplex p c
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiber_kanComplex (leftStrictTransportDiagram p) c

/-- 概要：strict transport の weighted nerve の各 fiber は元の fibration の fiber と同値。
方針：weighted nerve の fiber 同型の逆に続けて、strict transport の恒等射評価を使う。
規約：fiber ごとの同値であり、全空間の同値をここから推論しない。
使われ方：Kerodon §§5.3.3（Tag 025W）–5.3.5（Tag 037H）、復元の全体比較で必要な fiber 上の検査。 -/
noncomputable def leftStrictTransportWeightedFiberEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (leftStrictTransportWeightedProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  have : KanComplex ((leftStrictTransportDiagram p).obj c) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport_kanComplex p c
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberIso (leftStrictTransportDiagram p) c).symm).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFiberEquivalence p c)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
