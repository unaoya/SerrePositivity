module

public import SerrePositivity.KST.LocalizingInvariants.LaxArrowTransformation
public import SerrePositivity.KST.LocalizingInvariants.FullStableExact
public import SerrePositivity.KST.LocalizingInvariants.PullbackDifferenceVertices
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationStability

/-!
概要：通常 pullback は安定 ∞ 圏であり、元の lax pullback への比較包含は完全。
方針：同値矢印の頂点条件の安定閉性と F2 の全部分複体への厳密同型を使う。
規約：元の Cat∞ の pullback と射影を保持する。使われ方：K-8(d) の差の商の左項。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)

instance equivalenceSubcomplex_isStable :
    IsStable (F2.laxPullbackEquivalenceSubcomplex p.hom q.hom : SSet.{u}) :=
  FullSubcomplex.isStable (F2.IsLaxEquivalenceVertex p.hom q.hom)
    (laxEquivalenceVertex_stable p q)

instance ordinaryPullback_isStable : IsStable (F2.catPullback p.hom q.hom) := by
  let e := F2.catPullbackEquivalenceSubcomplexIso p.hom q.hom
  exact isStable_of_trivialKanFibration e.hom

instance pullbackComparison_isExact : IsExactFunctor (F2.catPullbackToLax p.hom q.hom) := by
  rw [← F2.catPullbackToEquivalenceSubcomplex_ι]
  have : IsExactFunctor (F2.catPullbackEquivalenceSubcomplexIso p.hom q.hom).hom :=
    inferInstance
  have : IsExactFunctor (fullSubcomplexOnVertices (F2.laxPullback p.hom q.hom)
      (F2.IsLaxEquivalenceVertex p.hom q.hom)).ι :=
    FullSubcomplex.inclusion_isExact _ (laxEquivalenceVertex_stable p q)
  exact inferInstanceAs (IsExactFunctor
    ((F2.catPullbackEquivalenceSubcomplexIso p.hom q.hom).hom ≫
      (fullSubcomplexOnVertices (F2.laxPullback p.hom q.hom)
        (F2.IsLaxEquivalenceVertex p.hom q.hom)).ι))

/-- F2 の元の通常 pullback を K-5 の安定対象へ束ねる。 -/
def pullbackCategory : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u} :=
  ⟨F2.catPullback p.hom q.hom, inferInstance, inferInstance⟩

/-- 元の通常 pullback の全単体上の比較包含。 -/
def pullbackInclusion : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (pullbackCategory p q) (laxCategory p q) :=
  ⟨F2.catPullbackToLax p.hom q.hom, inferInstance⟩

lemma pullbackInclusion_fullyFaithful : IsFullyFaithful (pullbackInclusion p q).hom :=
  pullbackComparison_fullyFaithful p q

def pullbackFst : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (pullbackCategory p q) C where
  hom := (pullbackInclusion p q).hom ≫ (laxFst p q).hom
  isExact := inferInstance

def pullbackSnd : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (pullbackCategory p q) D where
  hom := (pullbackInclusion p q).hom ≫ (laxSnd p q).hom
  isExact := inferInstance

lemma pullbackFst_hom : (pullbackFst p q).hom = F2.catPullbackFst p.hom q.hom :=
  F2.catPullbackToLax_fst p.hom q.hom

lemma pullbackSnd_hom : (pullbackSnd p q).hom = F2.catPullbackSnd p.hom q.hom :=
  F2.catPullbackToLax_snd p.hom q.hom

end SerrePositivity.KST.LocalizingInvariants
