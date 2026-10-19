module

public import SerrePositivity.InfinityCategories.F1B.KanPathRelativeFunctorMapping
public import SerrePositivity.InfinityCategories.F1B.KanIsofibrationCriterion
public import SerrePositivity.InfinityCategories.Core.EquivalencePullbackPathLifting

/-!
概要：元の相対標的から path 置換上の相対標的への切断による比較。
方針：切断の後合成の同値を関手制限の isofibration に沿って引き戻す。
規約：U の充填性を仮定しない。
使われ方：path 置換上の片側比較を元の相対制限へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：元と底の両立する関手の組を定値 path の組へ写す。
方針：元の図式だけに切断を後合成し、底の図式を保って引き戻しへ持ち上げる。
規約：U の両端や添字に充填性は不要。
使われ方：一般 U の相対標的の比較射。 -/
def kanPathRelativeTargetComparison {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj δ (equivalencePathReplacementMap U)) : s.pt ⟶ t.pt :=
  t.isPullback.lift (s.fst ≫ (ihom K).map (equivalencePathReplacementSection U)) s.snd (by
    change (s.fst ≫ (ihom K).map (equivalencePathReplacementSection U)) ≫
      (ihom K).map (equivalencePathReplacementMap U) = s.snd ≫ (pre δ).app E
    rw [Category.assoc, ← Functor.map_comp, equivalencePathReplacementSection_map]
    exact s.isPullback.w)

/-- 概要：相対標的の切断比較の第一成分は元の図式の切断への後合成。
方針：引き戻しの持ち上げの第一射影の式。
規約：全単体での射の等式。
使われ方：比較射を同値の引き戻しとして同定する。 -/
lemma kanPathRelativeTargetComparison_fst {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj δ (equivalencePathReplacementMap U)) :
    kanPathRelativeTargetComparison U δ s t ≫ t.fst =
      s.fst ≫ (ihom K).map (equivalencePathReplacementSection U) := t.isPullback.lift_fst _ _ _

/-- 概要：相対標的の切断比較は底の図式を保つ。
方針：引き戻しの持ち上げの第二射影の式。
規約：全単体での射の等式。
使われ方：切断比較の引き戻しの普遍性。 -/
lemma kanPathRelativeTargetComparison_snd {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj δ (equivalencePathReplacementMap U)) :
    kanPathRelativeTargetComparison U δ s t ≫ t.snd = s.snd := t.isPullback.lift_snd _ _ _

/-- 概要：単射に沿う相対標的の切断比較は圏同値。
方針：元の図式への第一射影の引き戻し正方形を消去し、制限に沿う切断の同値を移す。
規約：U に fibration 性は要求しない。
使われ方：一般 U の元の相対制限の片側比較。 -/
lemma kanPathRelativeTargetComparison_isQCatEquivalence {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C) [Mono δ]
    (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj δ (equivalencePathReplacementMap U))
    [Quasicategory s.pt] [Quasicategory t.pt] :
    IsQCatEquivalence (kanPathRelativeTargetComparison U δ s t) := by
  have : Quasicategory ((internalHom.obj (Opposite.op K)).obj
      (equivalencePathReplacement U)) :=
    inferInstanceAs (Quasicategory ((ihom K).obj (equivalencePathReplacement U)))
  have ht : KanEquivalenceLifting t.fst := by
    intro A B i hm hi
    have : HasLiftingProperty i ((internalHom.map δ.op).app E) :=
      kanEquivalenceLifting_pre δ (X := E) i hm hi
    exact t.isPullback.flip.hasLiftingProperty i
  have : InnerFibration t.fst := ht.innerFibration
  have : TrivialKanFibration (relativeEquivalencePathMapAt t.fst 1) :=
    kanRelativeEquivalencePathMapAt_one_trivialKanFibration t.fst
      (KanEquivalenceLifting.invertibleTargetLifting ht)
  let e := (ihom K).map (equivalencePathReplacementSection U)
  have he : IsQCatEquivalence e :=
    (kanEquivalencePathReplacementSection_isQCatEquivalence U).postcompose K
  have ho : IsPullback s.fst (kanPathRelativeTargetComparison U δ s t ≫ t.snd)
      (e ≫ (ihom K).map (equivalencePathReplacementMap U)) ((pre δ).app E) := by
    rw [kanPathRelativeTargetComparison_snd]
    dsimp only [e]
    rw [← Functor.map_comp, equivalencePathReplacementSection_map]
    exact s.isPullback
  have hp := ho.of_bot (kanPathRelativeTargetComparison_fst U δ s t).symm t.isPullback
  have : InnerFibration (pullback.fst e t.fst) :=
    ⟨innerFibrations.pullback_fst e t.fst (InnerFibration.mem (q := t.fst))⟩
  have : Quasicategory (pullback e t.fst) :=
    quasicategory_of_innerFibration (pullback.fst e t.fst)
  rw [← hp.isoPullback_hom_snd]
  exact (qCatEquivalenceOfIso hp.isoPullback).isQCatEquivalence.comp
    (he.pullback_snd_of_relativePath t.fst)

end SerrePositivity.InfinityCategories.F1B
