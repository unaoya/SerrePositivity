module

public import SerrePositivity.InfinityCategories.F1.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.F1.CoherentHomEquivalence
public import SerrePositivity.InfinityCategories.F1.CoherentVertices

/-!
概要：𝒮 内の任意の二頂点の左 Hom を元の値の内部 Hom と比較する。
方針：左右の pinched 模型の同値と coherent な豊穣 Hom 比較を合成する。
規約：頂点の標準化の等式を明示して保持する。
使われ方：全空間の単位による全 Hom の前合成を native な定義域で表示する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：𝒮 内の左 Hom と元の Kan 値の内部 Hom の持ち上げの同値。
方針：区間を介した右 Hom への比較と豊穣 Hom の比較の逆を続ける。
規約：選択された逆を含む。使われ方：全 Hom の単位前合成の比較。 -/
def spaceLeftHomValueEquivalence (x y : SpaceInfinity.{u} _⦋0⦌) :
    QCatEquivalence (pinchedHomLeft x y) ((SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (spaceInfinityObject x).obj).obj (spaceInfinityObject y).obj)) := by
  let e := coherentHomEquivalence (spaceInfinityObject x) (spaceInfinityObject y)
  let i : pinchedHom x y ≅ pinchedHom
      (coherentNerveVertex (spaceInfinityObject x))
      (coherentNerveVertex (spaceInfinityObject y)) :=
    eqToIso (congrArg₂ (fun a b ↦ pinchedHom a b)
      (coherentNerveVertex_object x).symm (coherentNerveVertex_object y).symm)
  exact (pinchedHomLeftRightEquivalence x y).trans
    ((qCatEquivalenceOfIso i).trans e.symm)

end SerrePositivity.InfinityCategories.F2
