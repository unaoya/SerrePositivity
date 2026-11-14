module
public import SerrePositivity.KST.SConstruction.PerfectInvariantHoArrow
public import SerrePositivity.KST.SConstruction.PerfectVerdierInvariantFiber
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquareArrows

/-! # 同じ Cat^perf の値と実 fiber 図式の対象・二辺の比較
概要：実 fiber 四角形の三対象を、元の不変量値の対象と同じ辺の類に照合する。
方針：元の頂点等号による同型と、同じ一単体の端点移送を用いる。
規約：射の類の式に元の包含・完備化後の射影を保持する。使われ方：分裂の切断の移送。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {E : perfectStableInfinity.{u} ⟶ Sp.{u}} (hE : IsPerfectLocalizingInvariant E)

/-- 実 fiber 図式の左端と同じ元の不変量値の対象の同型。 -/
def IsPerfectLocalizingInvariant.perfectFiberLeftIso (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (hE.sequenceFiberTriangle d).square 0 0 ≅
      perfectInvariantHoObject E d.leftVertex :=
  eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
    (hE.sequenceFiberTriangle_left d))

/-- 実 fiber 図式の中央と同じ元の不変量値の対象の同型。 -/
def IsPerfectLocalizingInvariant.perfectFiberMiddleIso (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (hE.sequenceFiberTriangle d).square 1 0 ≅
      perfectInvariantHoObject E d.middleVertex :=
  eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
    (hE.sequenceFiberTriangle_middle d))

/-- 実 fiber 図式の右端と同じ元の不変量値の対象の同型。 -/
def IsPerfectLocalizingInvariant.perfectFiberRightIso (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (hE.sequenceFiberTriangle d).square 1 1 ≅
      perfectInvariantHoObject E d.rightVertex :=
  eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
    (hE.sequenceFiberTriangle_right d))

/-- 同じ包含の元の値の射は、実 fiber 図式の底辺と対象比較の下で可換する。 -/
lemma IsPerfectLocalizingInvariant.perfectFiber_bottom_naturality
    (d : PerfectVerdierSequence.{u}) :
    (hE.perfectFiberLeftIso d).hom ≫
        perfectInvariantHoArrow E d.verdier.inclusion d.left_complete d.middle_complete =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (hE.sequenceFiberTriangle d).square ≫ (hE.perfectFiberMiddleIso d).hom := by
  have he : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (hE.sequenceFiberTriangle d).square).edge =
      ((perfectStableArrow d.verdier.inclusion d.left_complete d.middle_complete).map E).edge := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow_edge, hE.sequenceFiberTriangle_bottom d, Equiv.apply_symm_apply]
  exact (FiberModel.homMk_transport (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (hE.sequenceFiberTriangle d).square)
    ((perfectStableArrow d.verdier.inclusion d.left_complete d.middle_complete).map E).toTruncated
    (hE.sequenceFiberTriangle_left d) (hE.sequenceFiberTriangle_middle d) he).symm

/-- 同じ完備化後の射影の値は、実 fiber 図式の右辺と対象比較の下で可換する。 -/
lemma IsPerfectLocalizingInvariant.perfectFiber_right_naturality
    (d : PerfectVerdierSequence.{u}) :
    (hE.perfectFiberMiddleIso d).hom ≫
        perfectInvariantHoArrow E d.projection d.middle_complete d.right_complete =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (hE.sequenceFiberTriangle d).square ≫ (hE.perfectFiberRightIso d).hom := by
  have he : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (hE.sequenceFiberTriangle d).square).edge =
      ((perfectStableArrow d.projection d.middle_complete d.right_complete).map E).edge := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge, hE.sequenceFiberTriangle_projection d, Equiv.apply_symm_apply]
  exact (FiberModel.homMk_transport (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (hE.sequenceFiberTriangle d).square)
    ((perfectStableArrow d.projection d.middle_complete d.right_complete).map E).toTruncated
    (hE.sequenceFiberTriangle_middle d) (hE.sequenceFiberTriangle_right d) he).symm

end SerrePositivity.KST.SConstruction
