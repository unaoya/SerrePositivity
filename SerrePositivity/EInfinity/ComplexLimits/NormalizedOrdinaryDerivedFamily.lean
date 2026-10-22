module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedOrdinaryDerivedHom
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.IntervalFamilyInvariance

/-!
# 同じ元の始域比較を用いる実 D(R) Hom 比較の全区間族

概要：元の始域へ戻した実 Hom 比較は、任意パラメータで同じ probe 比較の逆の前合成を表す。
方針：pinched/区間比較の可逆二胞体と全区間族の前合成公式を使う。
規約：零単体の類の一致だけではなく任意の単体集合 T の族を扱う。
使われ方：標準導来単位の全族の公式と同じ始域比較への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedOrdinaryDerivedHomMap_family (X Y : Complex A) (T : SSet.{u + 1})
    (f : T ⟶ SSet.uliftFunctor.{u + 1, u}.obj
      (((normalizedProbeTensorHom A).obj (Opposite.op X)).obj
        (complexSemifreeResolutionValue A Y).val)) :
    let x := (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)
    let qx := (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((framedLimitProbeFunctor A).obj X))
    let y := (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)
    intervalFamilyHom (f ≫ normalizedOrdinaryDerivedHomMap A X Y ≫
      PinchedInterval.comparison x y) =
    constantFunctorHomMap T (complexProbeDerivedSourceVertexIso A X).inv ≫
      intervalFamilyHom (f ≫ normalizedProbeDerivedHomMap A X Y ≫
        (normalizedProbeDerivedEndpointIso A X Y).hom ≫ PinchedInterval.comparison qx y) := by
  let x := (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (nerveVertex X)
  let qx := (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
    (nerveVertex ((framedLimitProbeFunctor A).obj X))
  let y := (complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (nerveVertex Y)
  let p := normalizedProbeDerivedHomMap A X Y ≫ (normalizedProbeDerivedEndpointIso A X Y).hom
  let e := complexProbeDerivedSourceVertexIso A X
  have H := FunctorIso.simplicialHomotopy
    (PinchedInterval.liftMapComparisonIso (intervalPrecompose y e.inv))
  have h := intervalFamilyHom_eq_of_homotopy (functorHomotopyPrecomp H (f ≫ p))
  calc
    _ = intervalFamilyHom ((f ≫ p) ≫
        (PinchedInterval.comparison qx y ≫ intervalPrecompose y e.inv)) := by
      simpa only [normalizedOrdinaryDerivedHomMap, PinchedInterval.precompose,
        p, e, x, qx, y, Category.assoc] using h
    _ = _ := by
      rw [← Category.assoc, intervalPrecompose_family]
      rfl

end SerrePositivity.EInfinity.ComplexLimits
