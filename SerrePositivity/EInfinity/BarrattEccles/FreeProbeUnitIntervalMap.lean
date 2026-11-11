module

public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnitComma
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PointwiseUnitComparison

/-!
# 元の導来自由単位が誘導する標準区間比較

概要：同じ U と同じ実単位の前合成で、元の二つの ∞ 写像空間を比較する。
方針：U の区間後合成と元の単位の区間前合成を合成する。
規約：任意の同値の選択で標準比較を置き換えない。
使われ方：実 Hom span と単位の普遍性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

def derivedFreeProbeUnitIntervalMap (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌)
    (y : (CAlg_R A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (derivedFreeProbeVertex A x) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (cAlgForgetDerived A) (derivedFreeProbeVertex A x) y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌) y)
      (derivedFreeProbeUnitHom A x)

lemma derivedFreeProbeUnitIntervalMap_family (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A) _⦋0⦌)
    (y : (CAlg_R A) _⦋0⦌) (T : SSet.{u + 1})
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (derivedFreeProbeVertex A x) y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ derivedFreeProbeUnitIntervalMap A x y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap T (derivedFreeProbeUnitHom A x) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso T (derivedFreeProbeVertex A x) (cAlgForgetDerived A)).inv ≫
          (hoFunctor.map ((ihom T).map (cAlgForgetDerived A))).toFunctor.map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom f) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso T y (cAlgForgetDerived A)).hom := by
  rw [derivedFreeProbeUnitIntervalMap, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom]

end SerrePositivity.EInfinity.BarrattEccles
