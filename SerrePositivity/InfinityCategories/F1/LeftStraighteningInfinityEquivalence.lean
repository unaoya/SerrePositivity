module

public import SerrePositivity.InfinityCategories.F1.LeftFibrationFirstVertexUlift
public import SerrePositivity.InfinityCategories.F1.UniverseRelativePullbackReflection
public import SerrePositivity.InfinityCategories.F1.LeftFibrationBaseChangeFullyFaithful

/-!
概要：一般の小さい quasicategory 上の実際の空間値 straightening は圏同値。
方針：初頂点引き戻しの全相対 Hom 作用を元の宇宙で同値とし、同じ分類写像の充満忠実性を得る。
規約：構成済みの分類写像そのものに F0 の充満忠実・本質的全射判定を適用する。
使われ方：left fibration の空間値分類と、双対の right fibration の前層による分類。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 一般の小さい底上の初頂点引き戻しは、同じ全相対 Hom への作用として同値。 -/
lemma leftFibrationFirstVertexPullback_isQCatEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q] :
    IsQCatEquivalence (relativeFunctorPullback p q (transportSimplexFirstVertexMap B)) :=
  relativeFunctorPullback_isQCatEquivalence_of_ulift.{u, u + 1} p q _
    (leftFibrationFirstVertexUliftPullback_isQCatEquivalence p q)

/-- 一般の小さい quasicategory 上で、同じ初頂点引き戻し関手は充満忠実。 -/
lemma leftFibrationInfinityFirstVertexBaseChange_isFullyFaithful
    (B : SSet.{u}) [Quasicategory B] :
    IsFullyFaithful (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B)) := by
  apply (leftFibrationInfinityBaseChange_isFullyFaithful_iff _).mpr
  intro p q
  exact leftFibrationFirstVertexPullback_isQCatEquivalence p.val.hom q.val.hom

/-- 構成済みの同じ空間値 straightening は、一般の小さい quasicategory 上で充満忠実。 -/
lemma leftStraighteningInfinityMap_isFullyFaithful (B : SSet.{u}) [Quasicategory B] :
    IsFullyFaithful (leftStraighteningInfinityMap B) :=
  (leftStraighteningInfinityMap_isFullyFaithful_iff_firstVertexBaseChange B).mpr
    (leftFibrationInfinityFirstVertexBaseChange_isFullyFaithful B)

/-- 同じ straightening の充満忠実性と本質的全射性を合わせ、空間値の分類同値を閉じる。 -/
lemma leftStraighteningInfinityMap_isQCatEquivalence (B : SSet.{u}) [Quasicategory B] :
    IsQCatEquivalence (leftStraighteningInfinityMap B) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (leftStraighteningInfinityMap_isFullyFaithful B)
    (leftStraighteningInfinityMap_isEssentiallySurjective B)

/-- 順方向を構成済みの同じ分類写像に固定した空間値 straightening の同値。 -/
def leftStraighteningInfinityEquivalence (B : SSet.{u}) [Quasicategory B] :
    QCatEquivalence (LeftFibrationInfinity B)
      (SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj B)) :=
  (leftStraighteningInfinityMap_isQCatEquivalence B).choose

end SerrePositivity.InfinityCategories
