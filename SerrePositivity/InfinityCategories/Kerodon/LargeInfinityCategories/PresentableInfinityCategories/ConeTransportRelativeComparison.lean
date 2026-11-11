module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoslicePointTransportComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentConeSections
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：元の全解錐の各脚による標準輸送は元の全解図式と相対関手空間で同型。
方針：元の全空間の頂点の coslice 上の比較を同じ全錐の切断で前合成する。
規約：比較は全図式と同じ底を固定した相対 Hom の同型。
使われ方：分類した解関手の retract の分裂等式を構成する。

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

variable {A E B : SSet.{u}} (p : E ⟶ B)
  {f : A ⟶ E} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone f)

/-- 概要：元の全解錐の脚を底の指定頂点の coslice へ同時に写す。
方針：全空間の coslice 切断を元の射影で後合成する。
規約：同じ全解頂点を始点とする全ての脚を保持する。
使われ方：底上の表現可能関手への全空間比較。 -/
def conePointComparison :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c.vertex)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection c ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp (SSet.yonedaEquiv.symm c.vertex) p
      (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c.vertex))
      (SSet.yonedaEquiv_symm_comp c.vertex p)

/-- 概要：底の coslice への全脚比較は元の全解図式の底を厳密に保つ。
方針：正規化済み後合成と錐の coslice 切断の射影公式を使う。
規約：元の底の全射 f ≫ p。
使われ方：底を保つ分類比較の条件。 -/
lemma conePointComparison_projection :
    conePointComparison p c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c.vertex)) = f ≫ p := by
  rw [conePointComparison, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableCoslicePostcomp_projection,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection_projection]

variable [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]

/-- 概要：同じ全錐の脚に沿う標準輸送は元の全図式と相対関手空間で同型。
方針：頂点の coslice 上の比較を元の錐の全切断で前合成する。
規約：元の図式の全高次単体と底を保持する。
使われ方：全解関手を表現可能関手の retract にする恒等関係。 -/
def coneTransportRelativeComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (f ≫ p) f rfl)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (f ≫ p)
        (conePointComparison p c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceVertexTransport p c.vertex)
        (by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceVertexTransport_projection,
          conePointComparison_projection])) := by
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex) ≫ p
  let j : CategoryTheory.Over.mk (f ≫ p) ⟶ CategoryTheory.Over.mk a :=
    Over.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection c) (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection c ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex) ≫ p) = f ≫ p
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection_projection])
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceVertexTransportComparison p c.vertex)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p j)
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_vertex p j _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_vertex p j _ _] at h
  simpa only [j, Over.homMk_left, Over.mk_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeCosliceSection_projection,
    conePointComparison, Category.assoc] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
