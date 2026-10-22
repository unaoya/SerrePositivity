module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedKProjectiveDerivedHom
public import SerrePositivity.InfinityCategories.Derived.PinchedFamilyPostcomposition

/-!
# 元の K-projective 導来 Hom 比較の全区間族

概要：実正規化 Hom 比較は同じ半自由分解関手の全区間族への作用を表す。
方針：元の pinchedHomMap に対する全パラメータの自然性を使う。
規約：任意 K と同じ二つの頂点・分解関手を保つ。
使われ方：元の自由単位と実導来 Hom の幾何的三角形への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.HomotopyFunctionComplex DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedKProjectiveDerivedHomMap_interval (X Y : KProjectiveComplex A) :
    normalizedKProjectiveDerivedHomMap A X Y ≫
      pinchedHomToIntervalMappingSpace (X := derivedInfinityCategory A)
      ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (Simplex.vertex X))
      ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (Simplex.vertex Y)) =
    (normalizedKProjectiveHomIso A X Y).hom ≫
      pinchedHomToIntervalMappingSpace (X := dgNerve A (KProjectiveComplex A))
        (Simplex.vertex X) (Simplex.vertex Y) ≫
        intervalFunctorMap (kProjectiveDerivedSource A) (Simplex.vertex X) (Simplex.vertex Y) := by
  rw [normalizedKProjectiveDerivedHomMap, Category.assoc,
    pinchedHomToIntervalMappingSpace_naturality]

lemma normalizedKProjectiveDerivedHomMap_family (X Y : KProjectiveComplex A)
    (K : SSet.{u + 1}) (g : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj
      ((cosimplicialHom (normalizedSimplexTensor A X.val)).obj Y.val)) :
    intervalFamilyHom (g ≫ normalizedKProjectiveDerivedHomMap A X Y ≫
      pinchedHomToIntervalMappingSpace (X := derivedInfinityCategory A)
      ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (Simplex.vertex X))
      ((kProjectiveDerivedSource A).app (Opposite.op ⦋0⦌) (Simplex.vertex Y))) =
    intervalFamilyHom (g ≫ (normalizedKProjectiveHomIso A X Y).hom ≫
      pinchedHomToIntervalMappingSpace (X := dgNerve A (KProjectiveComplex A))
        (Simplex.vertex X) (Simplex.vertex Y) ≫
        intervalFunctorMap (kProjectiveDerivedSource A) (Simplex.vertex X) (Simplex.vertex Y)) := by
  rw [normalizedKProjectiveDerivedHomMap_interval]

end SerrePositivity.EInfinity.ComplexLimits
