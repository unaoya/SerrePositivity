module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorPrecompositionFamily
public import SerrePositivity.EInfinity.ComplexLimits.IntervalFamilyFunctorPrecomposition

/-!
# 実正規化 Hom の全族の同じ関手による前合成

概要：元の複体射の正規化 Hom 前合成は、同じ関手で送った元の辺の前合成を表す。
方針：全複体 dg nerve 上の全族公式を元の関手 F により送る。
規約：任意 K・元の射・元の関手を保つ。Small や cofibrancy の仮定はない。
使われ方：半自由分解関手による自由単位の全族の像を同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.HomotopyFunctionComplex DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedTensorHom_precomp_family_map {C : SSet.{u + 1}}
    (F : dgNerve A (Complex A) ⟶ C) {X X' : Complex A} (Y : Complex A) (f : X' ⟶ X)
    (K : SSet.{u + 1}) (g : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj
      ((cosimplicialHom (normalizedSimplexTensor A X)).obj Y)) :
    intervalFamilyHom (g ≫ SSet.uliftFunctor.{u + 1, u}.map
      ((cosimplicialHomMap ((normalizedSimplexTensorFamily A).map f)).app Y) ≫
      (normalizedTensorPinchedIso A X' Y).hom ≫
      pinchedHomToIntervalMappingSpace (X := dgNerve A (Complex A))
        (Simplex.vertex X') (Simplex.vertex Y) ≫
      intervalFunctorMap F (Simplex.vertex X') (Simplex.vertex Y)) =
    constantFunctorHomMap K ((hoFunctor.map F).toFunctor.map
      (Truncated.HomotopyCategory.homMk
        (dgClosedEdge A (Complex A) ((complexToClosed A).map f)))) ≫
      intervalFamilyHom (g ≫ (normalizedTensorPinchedIso A X Y).hom ≫
        pinchedHomToIntervalMappingSpace (X := dgNerve A (Complex A))
          (Simplex.vertex X) (Simplex.vertex Y) ≫
        intervalFunctorMap F (Simplex.vertex X) (Simplex.vertex Y)) := by
  let l : K ⟶ intervalMappingSpace (X := dgNerve A (Complex A))
      (Simplex.vertex X') (Simplex.vertex Y) :=
    g ≫ SSet.uliftFunctor.{u + 1, u}.map
      ((cosimplicialHomMap ((normalizedSimplexTensorFamily A).map f)).app Y) ≫
      (normalizedTensorPinchedIso A X' Y).hom ≫
      pinchedHomToIntervalMappingSpace (X := dgNerve A (Complex A))
        (Simplex.vertex X') (Simplex.vertex Y)
  let r : K ⟶ intervalMappingSpace (X := dgNerve A (Complex A))
      (Simplex.vertex X) (Simplex.vertex Y) :=
    g ≫ (normalizedTensorPinchedIso A X Y).hom ≫
      pinchedHomToIntervalMappingSpace (X := dgNerve A (Complex A))
        (Simplex.vertex X) (Simplex.vertex Y)
  have h : intervalFamilyHom l = constantFunctorHomMap K
      (Truncated.HomotopyCategory.homMk
        (dgClosedEdge A (Complex A) ((complexToClosed A).map f))) ≫ intervalFamilyHom r := by
    simpa only [l, r, dgPinchedFamilyHom, Category.assoc] using
      normalizedTensorPinchedIso_precomp_family A Y f K g
  exact intervalFamilyFunctorMap_precompose F
    (Truncated.HomotopyCategory.homMk
      (dgClosedEdge A (Complex A) ((complexToClosed A).map f))) l r h

end SerrePositivity.EInfinity.ComplexLimits
