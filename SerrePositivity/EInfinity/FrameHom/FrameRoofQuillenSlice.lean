module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofTarget

/-!
# 元の実屋根の Quillen A slice を次数の Over 圏へ送る

概要：指定した実屋根の点と全高次 slice を、同じ次数へ向かう射の図式と照合する。
方針：slice の後合成・同じ点の厳密な輸送・元の nerve Over 同型を使う。
規約：元の指定点を保持し、全単体の射影式を証明する。
使われ方：sourceFrameHom×Δ[n] による元の全 Quillen A slice の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)

def roofTargetOverBaseMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm b) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (roofTargetDegree A Y q b))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (SSet.yonedaEquiv.symm b) (roofTargetProjection A Y q) ≫
    (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (roofTargetPoint_projection A Y q b))).hom

lemma roofTargetOverBaseMap_projection : roofTargetOverBaseMap A Y q b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (roofTargetDegree A Y q b))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b) ≫ roofTargetProjection A Y q := by
  rw [roofTargetOverBaseMap, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverProjection_eqTransport (roofTargetPoint_projection A Y q b),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection]

variable {S : SSet.{u}} (f : S ⟶ roofTarget A Y q)

abbrev roofQuillenSlice := pullback f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b))

def roofQuillenSliceOver : roofQuillenSlice A Y q b f ⟶
    nerve (Over (roofTargetDegree A Y q b)) :=
  pullback.snd _ _ ≫ roofTargetOverBaseMap A Y q b ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso (roofTargetDegree A Y q b)).inv

lemma roofQuillenSliceOver_projection : roofQuillenSliceOver A Y q b f ≫
    nerveMap (Over.forget (roofTargetDegree A Y q b)) =
      pullback.fst f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm b)) ≫
        f ≫ roofTargetProjection A Y q := by
  have hi : (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso (roofTargetDegree A Y q b)).inv ≫
      nerveMap (Over.forget (roofTargetDegree A Y q b)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (roofTargetDegree A Y q b))) := by
    change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (roofTargetDegree A Y q b))
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso_projection, Iso.inv_hom_id_assoc]
  rw [roofQuillenSliceOver, Category.assoc, Category.assoc, hi,
    roofTargetOverBaseMap_projection]
  rw [← Category.assoc, ← pullback.condition, Category.assoc]

def roofQuillenSliceDegreeMap : roofQuillenSlice A Y q b f ⟶
    pullback (f ≫ roofTargetProjection A Y q)
      (nerveMap (Over.forget (roofTargetDegree A Y q b))) :=
  pullback.lift (pullback.fst _ _) (roofQuillenSliceOver A Y q b f)
    (by simpa only [Category.assoc] using (roofQuillenSliceOver_projection A Y q b f).symm)

lemma roofQuillenSliceDegreeMap_source : roofQuillenSliceDegreeMap A Y q b f ≫
    pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

lemma roofQuillenSliceDegreeMap_over : roofQuillenSliceDegreeMap A Y q b f ≫
    pullback.snd _ _ = roofQuillenSliceOver A Y q b f := pullback.lift_snd _ _ _

end SerrePositivity.EInfinity.FrameHom.FrameArrows
