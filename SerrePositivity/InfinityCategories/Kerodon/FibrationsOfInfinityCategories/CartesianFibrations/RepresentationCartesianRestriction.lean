module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessTotalIso

/-!
概要：任意の pullback 正方形に沿って表現を実際の全空間へ制限する。
方針：標準 pullback への制限を pullback の一意同型で前合成する。
規約：図式と pointed space への射を厳密に回収する。
使われ方：区間実現の表現の両端を元の left fibration の表現に戻す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationCartesianRestriction

local instance {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：cartesian な全空間の射に沿って表現を制限する。
方針：標準 pullback への制限と全空間の同型による前合成を合成する。
規約：元と先の射影は left fibration。
使われ方：区間実現の端点の表現。 -/
def LeftTransportRepresentation.cartesianRestrict {E F B D : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ D} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (e : F ⟶ E) (g : D ⟶ B)
    (h : IsPullback e q p g) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation q :=
  ((R.toSquare.restrict g).totalPre h.isoPullback.hom h.isoPullback_hom_snd).toRepresentation
    (((R.toSquare.restrict g).isRepresentation_totalPre_iff h.isoPullback
      h.isoPullback_hom_snd).mpr (R.toSquare.isRepresentation_restrict
        R.toSquare_isRepresentation g))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationCartesianRestriction.LeftTransportRepresentation (cartesianRestrict)


/-- 概要：cartesian 制限は分類図式を元の底の射で前合成する。
方針：四角形から表現へ戻す定義。
規約：射の厳密な一致。
使われ方：復元した coherent な変換の両端。 -/
lemma LeftTransportRepresentation.cartesianRestrict_diagram {E F B D : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ D} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (e : F ⟶ E) (g : D ⟶ B)
    (h : IsPullback e q p g) : (R.cartesianRestrict e g h).diagram = g ≫ R.diagram := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationCartesianRestriction.LeftTransportRepresentation (cartesianRestrict_diagram)


/-- 概要：cartesian 制限の pointed space への射は元の全空間の射による前合成。
方針：標準 pullback への同型の第一射影を計算する。
規約：比較の選択を挟まず実際の射を回収する。
使われ方：変換が元の相対射を表現する条件。 -/
lemma LeftTransportRepresentation.cartesianRestrict_pointedMap {E F B D : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ D} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) (e : F ⟶ E) (g : D ⟶ B)
    (h : IsPullback e q p g) : (R.cartesianRestrict e g h).pointedMap = e ≫ R.pointedMap := by
  change ((R.toSquare.restrict g).totalPre h.isoPullback.hom
    h.isoPullback_hom_snd).comparison ≫ pullback.fst _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftTransportSquare.comparison, pullback.lift_fst]
  change h.isoPullback.hom ≫ (pullback.fst p g ≫ R.pointedMap) = _
  rw [← Category.assoc, h.isoPullback_hom_fst]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationCartesianRestriction.LeftTransportRepresentation (cartesianRestrict_pointedMap)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationCartesianRestriction
