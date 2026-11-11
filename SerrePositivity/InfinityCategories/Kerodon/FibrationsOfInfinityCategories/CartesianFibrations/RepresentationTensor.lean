module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationCartesianRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TensorFiber
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：実際の表現を任意のパラメーターとの積へ移す。
方針：積の第一射影の cartesian 正方形に沿って表現を制限する。
規約：図式と全空間の射はパラメーターを忘れる射の前合成。
使われ方：相対射の族を指定両端の collage で実現する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：積の第一射影の自然性は pullback 正方形。
方針：次数ごとの積の二成分を使う。
規約：パラメーターと元の射は任意。
使われ方：表現をパラメーターとの積へ移す正方形。 -/
lemma isPullback_tensor_fst {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u}) :
    IsPullback (fst E K) (p ▷ K) p (fst B K) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    have hk : (p.app n x.1, x.2) = (p.app n y.1, y.2) := h.2
    exact Prod.ext h.1 (congrArg (fun z : B.obj n × K.obj n ↦ z.2) hk)
  · intro x y h
    exact ⟨(x, y.2), rfl, Prod.ext h rfl⟩

/-- 概要：元の表現のパラメーターとの積。
方針：第一射影の pullback に沿って cartesian 制限する。
規約：パラメーターの小ささや Kan 性は不要。
使われ方：パラメーター付きの相対射の両端に置く指定表現。 -/
def LeftTransportRepresentation.tensor {E B : SSet.{u + 1}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (K : SSet.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation (p ▷ K) :=
  R.cartesianRestrict (fst E K) (fst B K) (isPullback_tensor_fst p K)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportRepresentation (tensor)


/-- 概要：積の表現の分類図式は元の図式の定値パラメーター族。
方針：cartesian 制限の図式公式。
規約：厳密な射の一致。
使われ方：coherent な変換の族の両端。 -/
lemma LeftTransportRepresentation.tensor_diagram {E B : SSet.{u + 1}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (K : SSet.{u + 1}) :
    (R.tensor K).diagram = fst B K ≫ R.diagram := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportRepresentation (tensor_diagram)


/-- 概要：積の表現は元の全空間側の射の定値パラメーター族を保つ。
方針：cartesian 制限の pointed space への射の公式。
規約：全空間の射を同値類に置き換えない。
使われ方：元の相対射の族を回収する条件。 -/
lemma LeftTransportRepresentation.tensor_pointedMap {E B : SSet.{u + 1}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (K : SSet.{u + 1}) :
    (R.tensor K).pointedMap = fst E K ≫ R.pointedMap :=
  R.cartesianRestrict_pointedMap _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftTransportRepresentation (tensor_pointedMap)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
