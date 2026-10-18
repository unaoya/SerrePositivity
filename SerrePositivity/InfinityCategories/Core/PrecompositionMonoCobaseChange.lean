module

public import SerrePositivity.InfinityCategories.Core.EquivalencePullbackPathLifting
public import SerrePositivity.InfinityCategories.Core.PrecompositionUnderPushout

/-!
概要：任意の前合成の同値条件の単射に沿う pushout による保存。
方針：内部 Hom が pushout を引き戻しに移すことと制限の相対 path の持ち上げを使う。
規約：同値条件を課す射自身の単射性は不要。
使われ方：Kerodon §4.5.5、§4.6.2 の比較射の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：前合成の同値条件は任意の単射に沿う pushout により保存される。
方針：関手単体集合の引き戻しを、可逆 path の持ち上げを持つ制限に沿う同値の引き戻しとして扱う。
規約：g が単射であり、i 自身の単射性は要求しない。
使われ方：Kerodon §4.5.5、Theorem 4.6.2.8 のセルの貼り合わせ。 -/
lemma IsPrecompositionEquivalence.of_isPushout_of_mono_other {A B C D : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ C} [Mono g] {k : B ⟶ D} {j : C ⟶ D}
    (hi : IsPrecompositionEquivalence i) (h : IsPushout i g k j) :
    IsPrecompositionEquivalence j := by
  intro X hX
  have : TrivialKanFibration (relativeEquivalencePathMapAt ((pre g).app X) 1) :=
    trivialKanFibration_relativeEquivalencePathMapAt_pre g X 1
  have hp := (hi X).pullback_snd_of_relativePath ((pre g).app X)
  have hpb := (isPullback_pre_of_isPushout h X).flip
  have he := hpb.isoPullback_hom_snd
  rw [← he]
  exact (qCatEquivalenceOfIso hpb.isoPullback).isQCatEquivalence.comp hp

end SerrePositivity.InfinityCategories
