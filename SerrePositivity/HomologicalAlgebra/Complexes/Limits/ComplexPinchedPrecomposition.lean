module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.PinchedEnrichedPrecomposition
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedSource
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits

/-!
# 元の複体射の Hom 前合成と dg nerve の全区間族

概要：明示した homPrecompose の実 pinched 像は、同じ複体射の ∞ 前合成を表す。
方針：元の閉射変換と豊穣前合成を同定し、小ささなしの全族公式へ渡す。
規約：全複体・元の射・全パラメータを保つ。
使われ方：実自由単位の前合成と同じ ∞ 写像空間の作用の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories

open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma complexToClosed_homTo {P Q : Complex A} (f : P ⟶ Q) :
    ForgetEnrichment.homTo (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f) = closedMap A f := rfl

lemma complexToClosed_precomposition {P Q : Complex A} (f : P ⟶ Q) (T : Complex A) :
    eHomWhiskerRight (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f)
      (ForgetEnrichment.of (Complex A) T) = homPrecompose f T := by
  change (λ_ (homComplex A Q T)).inv ≫
    ForgetEnrichment.homTo (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f) ▷ homComplex A Q T ≫
      enrichedComposition P Q T = homPrecompose f T
  rw [_root_.SerrePositivity.ComplexLimits.complexToClosed_homTo]
  exact (homPrecompose_closedMap A f T).symm

lemma complexPinchedPrecomposition_family {P Q : Complex A} (f : P ⟶ Q) (T : Complex A)
    (K : SSet.{u + 1}) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) Q T) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (homPrecompose f T)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f))) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) g := by
  have h := _root_.SerrePositivity.ComplexLimits.pinchedEnrichedPrecomposition_family A (Complex A)
    ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f) g
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A)
    (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A)
      (eHomWhiskerRight (Complex A) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f)
        (ForgetEnrichment.of (Complex A) T))) = _ at h
  rw [_root_.SerrePositivity.ComplexLimits.complexToClosed_precomposition] at h
  exact h

end SerrePositivity.ComplexLimits
