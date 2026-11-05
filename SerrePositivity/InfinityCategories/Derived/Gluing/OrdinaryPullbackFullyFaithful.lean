module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackComparison
public import SerrePositivity.InfinityCategories.Derived.DGNerveCommonMap
public import SerrePositivity.InfinityCategories.Derived.DGFunctorFullyFaithful
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus
/-!
概要：通常 pullback への正本制限比較の充満忠実性。
方針：充満 dg 包含の Hom 恒等写像を共通宇宙へ運び、正本比較と合成する。
規約：元の Hom 複体を使い、対象条件について追加仮定を置かない。
使われ方：通常 pullback 比較の同値と実完全包含の構成に用いる。
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
lemma dgGluingPullbackUniverseInclusion_isFullyFaithful :
    IsFullyFaithful (dgGluingPullbackUniverseInclusion R C D M) := by
  change IsFullyFaithful (dgNerveCommonMap.{u, max u v w, max u v w, max (u + 1) v w}
    (dgGluingPullbackInclusion R C D M))
  rw [dgNerveCommonMap_lifted]
  have h := dgNerve_map_isFullyFaithful_of_homIso
    (dgUniverseLiftFunctor.{u, max u v w, max u v w,
      max (u + 1) v w, max (u + 1) v w} (dgGluingPullbackInclusion R C D M))
    (fun _ _ => by change IsIso (𝟙 _); infer_instance)
  exact (qCatEquivalenceOfIso (dgNerveUniverseLiftIso R
    (DGGluingPullbackObject R C D M))).isQCatEquivalence.isFullyFaithful.comp
      (h.comp (qCatEquivalenceOfIso
        (dgNerveUniverseLiftIso R (DGGluingObject R C D M)).symm).isQCatEquivalence.isFullyFaithful)
lemma dgGluingPullbackToLax_isFullyFaithful :
    IsFullyFaithful (dgGluingPullbackToLax R C D M) :=
  (dgGluingPullbackUniverseInclusion_isFullyFaithful R C D M).comp
    (dgGluingUniverseDerivedNerveLaxComparison_isFullyFaithful R C D M)
lemma dgGluingPullbackEquivalenceSubcomplexComparison_isFullyFaithful :
    IsFullyFaithful (dgGluingPullbackEquivalenceSubcomplexComparison R C D M) := by
  apply (F2.laxPullbackEquivalenceSubcomplex_isFullyFaithful
    (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
    (dgGluingUniverseDerivedCoefficient R C D M)).cancel_right
  rw [dgGluingPullbackEquivalenceSubcomplexComparison_ι]
  exact dgGluingPullbackToLax_isFullyFaithful R C D M
lemma dgGluingOrdinaryPullbackComparison_isFullyFaithful :
    IsFullyFaithful (dgGluingOrdinaryPullbackComparison R C D M) :=
  (dgGluingPullbackEquivalenceSubcomplexComparison_isFullyFaithful R C D M).comp
    (qCatEquivalenceOfIso (F2.catPullbackEquivalenceSubcomplexIso
      (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)).symm).isQCatEquivalence.isFullyFaithful
end SerrePositivity.InfinityCategories
