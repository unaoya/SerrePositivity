module

public import SerrePositivity.KST.Spectra.SimplexCellSphereIso
public import SerrePositivity.KST.Spectra.SphereMappingHomotopyGroups

/-!
概要：セルの球面の Hom の正次数群を係数の高い次数の群へ移す。
方針：二つの球面の厳密な同型を Hom へ送り、標準球面の次数移動に合成する。
規約：球面の次元 n+1 と Hom の次数 r+1 を足した次数を得る。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の塔の各セルの群の計算。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.SimplexCell

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：セルの球面の Hom の群は標的の球面次元だけ高い群である。
方針：境界を直接潰す球面へ源を移し、標準の球面の群同型を適用する。
規約：実際の標的の次数は n+r+2。
使われ方：Goerss–Jardine I §7、VIII §1。各 fiber の係数の同定。 -/
def positiveHomotopyEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom (sphere.{u} (n + 1)) Y).right r
        (PointedSimplicialSet.basepoint (PointedObject.basedHom (sphere.{u} (n + 1)) Y)) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1 + r) Y.basepoint := by
  let ep : PointedObject.basedHom (sphere.{u} (n + 1)) Y ≅
      PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y :=
    (internalHom.flip.obj Y).mapIso (sphereIso.{u} (n + 1)).symm.op
  let e : (PointedObject.basedHom (sphere.{u} (n + 1)) Y).right ≅
      (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right :=
    PointedSimplicialSet.forget.mapIso ep
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r e (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint ep.hom)).trans
    (SphereSimplex.positiveHomotopyEquiv Y n r)

end

end SerrePositivity.KST.Spectra.SimplexCell
