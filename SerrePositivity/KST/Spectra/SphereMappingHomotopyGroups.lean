module

public import SerrePositivity.KST.Spectra.SphereLoopMappingClasses
public import SerrePositivity.KST.Spectra.CirclePowerPositiveHomotopy

/-!
概要：正次元の球面の Hom の正次数群と標的の高い次数の群の標準同型。
方針：基本群の比較を loop 値の球面の群から得て、内部 Hom の交換と loop で反復する。
規約：すべて RelStruct・MulStruct から構成した通常の群の同型。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の tower fiber の係数の次数移動。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SphereSimplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：正次元の球面の Hom の基本群は標的の球面次元より一つ高い群。
方針：loop 値の写像類を基本群と球面の高次群の二つの群同型で比較する。
規約：球面の次元は n+1、標的の実際の次数は n+2。
使われ方：Goerss–Jardine I §7、VIII §1。正次数の帰納法の基本段。 -/
def fundamentalHomotopyEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right 0
        (PointedSimplicialSet.basepoint
          (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y)) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1) Y.basepoint :=
  (LoopMappingClasses.groupEquiv (PointedSimplicialSet.sphere.{u} (n + 1)) Y).symm.trans
    ((LoopMappingClasses.sphereComponentEquiv Y n).trans (CirclePower.positiveHomotopyEquiv Y n))

/-- 概要：正次元球面の Hom の正次数群を球面の次元だけ移動する。
方針：基本群の比較から出発し、loop の群の同型と内部 Hom の交換を反復する。
規約：球面の次元は n+1、Hom の次数は r+1、標的の次数は n+r+2。
使われ方：Goerss–Jardine I §7、VIII §1。塔の fiber の正次数群の計算。 -/
def positiveHomotopyEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right r
        (PointedSimplicialSet.basepoint
          (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y)) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1 + r) Y.basepoint := by
  induction r generalizing Y with
  | zero => exact fundamentalHomotopyEquiv Y n
  | succ r ih =>
    let H : PointedSimplicialSet.{u} :=
      PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y
    let ep : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace H ≅
        PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) :=
      _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle
        (PointedSimplicialSet.sphere.{u} (n + 1)) Y
    let e : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace H).right ≅
        (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right :=
      PointedSimplicialSet.forget.mapIso ep
    exact (loopPositiveHomotopyEquiv H r).symm.trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r e (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint ep.hom)).trans
        ((ih (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).trans (loopPositiveHomotopyEquiv Y (n + 1 + r))))

end

end SerrePositivity.KST.Spectra.SphereSimplex
