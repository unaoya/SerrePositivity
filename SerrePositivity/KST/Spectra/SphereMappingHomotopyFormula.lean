module

public import SerrePositivity.KST.Spectra.SphereMappingHomotopyGroups
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget

/-!
概要：球面の正次数群の次数移動の帰納式と loop の交換の自然性。
方針：構成で用いた内部 Hom の交換を独立の同型として名前を付ける。
規約：球面は正次元。群の添字は実際の次数より一つ小さい。
使われ方：Goerss–Jardine I §7、VIII §1。係数の自然性の帰納法。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SphereSimplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：球面からの Hom と loop の二つの順序を交換する。
方針：点つき内部 Hom の源の交換同型を使う。
規約：この厳密な同型に Kan 性は不要。
使われ方：Goerss–Jardine I §7。球面の次数移動の帰納的な構造。 -/
def loopSwap (Y : PointedSimplicialSet.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y) ≅
      PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u}
    (PointedSimplicialSet.sphere.{u} (n + 1)) Y

lemma positiveHomotopyEquiv_zero (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right 0
      (PointedSimplicialSet.basepoint
        (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y))) :
    positiveHomotopyEquiv Y n 0 a = fundamentalHomotopyEquiv Y n a := rfl

/-- 概要：正次数の次数移動の一段の帰納式。
方針：loop の群の逆同型、源の交換、帰納的な比較、標的の loop の順に展開する。
規約：構成済みの群同型そのものの等式。
使われ方：Goerss–Jardine I §7、VIII §1。自然性の帰納法で使う計算式。 -/
lemma positiveHomotopyEquiv_succ (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n r : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right (r + 1)
      (PointedSimplicialSet.basepoint
        (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y))) :
    positiveHomotopyEquiv Y n (r + 1) a =
      loopPositiveHomotopyEquiv Y (n + 1 + r)
        (positiveHomotopyEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r
          (pointedGroupMap
            (X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace
              (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y))
            (Y := PointedObject.basedHom
              (PointedSimplicialSet.sphere.{u} (n + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y))
            r (loopSwap Y n).hom
            ((loopPositiveHomotopyEquiv
              (PointedObject.basedHom
                (PointedSimplicialSet.sphere.{u} (n + 1)) Y) r).symm a))) := rfl

end

end SerrePositivity.KST.Spectra.SphereSimplex
