module
public import SerrePositivity.KST.Fibration.TailWeakEndpoint
public import SerrePositivity.KST.Fibration.TailWeakJointReflection
public import SerrePositivity.KST.Fibration.WeakCofiberCompletionSection
public import SerrePositivity.KST.Fibration.RelativePullbackMulti

/-! # 最後の W 辺の全 cofiber 補完と先行列の相対引き戻し -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 最後の W 辺の補完を忘れて元の先行列を取る完全関手。 -/
def tailCompletionPrefix {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    weakCofiberCompletionModel q (tailWeakEdgeExact q n) ⟶ weakStringModel q ⦋n + 1⦌ :=
  weakCofiberCompletionForget q (tailWeakEdgeExact q n) ≫ tailWeakPrefixExact q n

/-- 最後の辺の全補完と先行列は、元の共有端点上の実引き戻しをなす。 -/
lemma tailCompletion_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    IsPullback (weakCofiberCompletionCofiber q (tailWeakEdgeExact q n)).val
      (tailCompletionPrefix q n).val (relativeCofiberSubobject
        (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)).val
      (tailPrefixEndpointTop q n).val := by
  have h : IsPullback (weakCofiberCompletionCofiber q (tailWeakEdgeExact q n)).val
      (weakCofiberCompletionForget q (tailWeakEdgeExact q n)).val
      (weakArrowCofiberEquivalence q).hom.val (tailWeakEdgeExact q n).val :=
    IsPullback.of_hasPullback _ _
  have ht := (h.flip.paste_horiz (tailWeak_top_isPullback q n)).flip
  change IsPullback _ _
    ((weakArrowCofiberEquivalence q).hom ≫ weakArrowSourceTopExact q).val _ at ht
  rw [weakCofiberProjection_sourceTop] at ht
  exact ht

/-- 最後の補完と先行列の両実成分は、零対象と押し出しを共同で反映する。 -/
lemma tailCompletion_jointReflection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    JointlyReflectsSData (weakCofiberCompletionCofiber q (tailWeakEdgeExact q n)).val
      (tailCompletionPrefix q n).val where
  zero v hc hp := by
    have hn := (weakArrowCofiberEquivalence q).hom.property.1 _ hc
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((weakCofiberCompletionCofiber q (tailWeakEdgeExact q n) ≫
      (weakArrowCofiberEquivalence q).hom).val.app _ v) at hn
    rw [weakCofiberCompletionCofiber_projection] at hn
    have hz := (tailWeak_jointReflection q n).zero
      ((weakCofiberCompletionForget q (tailWeakEdgeExact q n)).val.app _ v) hp hn
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_iff_map_of_trivialKanFibration
      (weakCofiberCompletionForget q (tailWeakEdgeExact q n)).val v).2 hz
  pushout F hc hp := by
    have hn := (stableModelHom_preservesSConstructionData
      (weakArrowCofiberEquivalence q).hom).2 _ hc
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ (weakCofiberCompletionCofiber q (tailWeakEdgeExact q n) ≫
      (weakArrowCofiberEquivalence q).hom).val) at hn
    rw [weakCofiberCompletionCofiber_projection] at hn
    have hz := (tailWeak_jointReflection q n).pushout
      (F ≫ (weakCofiberCompletionForget q (tailWeakEdgeExact q n)).val) hp hn
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_iff_postcomp_trivialKanFibration
      (weakCofiberCompletionForget q (tailWeakEdgeExact q n)).val F).2 hz

/-- 元の先行列と最後の cofiber の全反復比較に使う、証明済みの実引き戻しデータ。 -/
def tailRelativePullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    RelativePullback (sInputModel B) (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q) where
  total := weakCofiberCompletionModel q (tailWeakEdgeExact q n)
  base := weakStringModel q ⦋n + 1⦌
  cofiber := weakCofiberCompletionCofiber q (tailWeakEdgeExact q n)
  projection := tailCompletionPrefix q n
  endpoint := tailPrefixEndpointTop q n
  isPullback := tailCompletion_isPullback q n
  reflects := tailCompletion_jointReflection q n

end SerrePositivity.KST.Fibration
