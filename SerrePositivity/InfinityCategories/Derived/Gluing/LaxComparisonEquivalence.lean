module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomPullbackEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomFaithfulnessCriterion
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxComparisonEssentialSurjectivity
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence
/-!
概要：元の dg gluing から導来加群圏上の lax pullback への正本比較は ∞ 圏の同値である。
方針：正本 Hom 比較の実逆射から充満忠実性を得て、既存の本質的全射性と合わせる。
規約：元対象・Hom 複体・両射影と augmentation の族を保持する。
使われ方：全試験関手の普遍性と安定 gluing の比較に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
lemma dgGluingUniverseDerivedNerveLaxComparison_isFullyFaithful :
    IsFullyFaithful (dgGluingUniverseDerivedNerveLaxComparison R C D M) :=
  (dgGluingUniverseDerivedNerveLaxComparison_fullyFaithful_iff R C D M).mpr
    (fun X Y => dgGluingLaxHomPullbackComparison_equivalence R C D M X Y)
lemma dgGluingUniverseDerivedNerveLaxComparison_isQCatEquivalence :
    IsQCatEquivalence (dgGluingUniverseDerivedNerveLaxComparison R C D M) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgGluingUniverseDerivedNerveLaxComparison_isFullyFaithful R C D M)
    (dgGluingUniverseDerivedNerveLaxComparison_isEssentiallySurjective R C D M)

def dgGluingUniverseDerivedNerveLaxEquivalence :
    QCatEquivalence
      ((SSet.uliftFunctor.{max (u + 1) v w,max u v w}).obj
        (dgNerve R (DGGluingObject R C D M)))
      (F2.laxPullback (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)) :=
  (dgGluingUniverseDerivedNerveLaxComparison_isQCatEquivalence R C D M).choose
lemma dgGluingUniverseDerivedNerveLaxEquivalence_hom :
    (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).hom =
      dgGluingUniverseDerivedNerveLaxComparison R C D M := rfl
end SerrePositivity.InfinityCategories
