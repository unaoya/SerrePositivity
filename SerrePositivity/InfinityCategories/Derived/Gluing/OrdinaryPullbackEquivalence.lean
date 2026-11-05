module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackEssentialSurjectivity
/-!
概要：元 dg gluing 内の可逆 augmentation 部分圏と通常 pullback の同値。
方針：同じ制限比較の充満忠実性と本質的全射性を合わせる。
規約：比較写像を選び直さず、全単体上の元の制限を保持する。
使われ方：通常 pullback の安定性と同じ dg 核の商に用いる。
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
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingOrdinaryPullbackComparison_isEssentiallySurjective :
    IsEssentiallySurjective (dgGluingOrdinaryPullbackComparison R C D M) :=
  (dgGluingPullbackEquivalenceSubcomplexComparison_isEssentiallySurjective R C D M hC hD).comp
    (qCatEquivalenceOfIso (F2.catPullbackEquivalenceSubcomplexIso
      (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)).symm).isEssentiallySurjective
lemma dgGluingOrdinaryPullbackComparison_isQCatEquivalence :
    IsQCatEquivalence (dgGluingOrdinaryPullbackComparison R C D M) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgGluingOrdinaryPullbackComparison_isFullyFaithful R C D M)
    (dgGluingOrdinaryPullbackComparison_isEssentiallySurjective R C D M hC hD)
def dgGluingOrdinaryPullbackEquivalence :
    QCatEquivalence
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (dgNerve R (DGGluingPullbackObject R C D M)))
      (F2.catPullback (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M)) :=
  (dgGluingOrdinaryPullbackComparison_isQCatEquivalence R C D M hC hD).choose
lemma dgGluingOrdinaryPullbackEquivalence_hom :
    (dgGluingOrdinaryPullbackEquivalence R C D M hC hD).hom =
      dgGluingOrdinaryPullbackComparison R C D M := rfl
end SerrePositivity.InfinityCategories
