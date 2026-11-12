module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeCommaComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationEquivalenceLifting
public import
  SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquarePrecompositionCoherence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.PullbackCommonNormalizedIso
/-!
概要：元の任意の関手同型に沿って指定下側変換を移し、実 under comma の比較を得る。
方針：left fibration 上の指定 path を厳密化し、その同じ同型を二成分の比較へ束ねる。
規約：元の関手同型と指定変換を保持し、pullback の Kan 性を仮定しない。
使われ方：終点評価の下での元の補間旧族と試験族の比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：指定下側変換を元の上側同型に沿って輸送すると、同じ実 under comma で同型。
方針：同じ指定 path の像の一致で貼り合わせる。
規約：元の比較と指定値を保持。使われ方：終点評価下の相対余錐の帰還。 -/
lemma exists_relativeCommaFamily_iso_of_functorIso
    {A K E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (e : E ⟶ B) (z : K ⟶ B) (f g : A ⟶ E) (t : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (ht : g ≫ e = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    ∃ (t' : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z) (hf : f ≫ e = t' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z),
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily e z t' f hf)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily e z t g ht)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z
  let d' := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d.postcomp e) rfl ht
  let c := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.pathCorrectedFunctorSquare p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_equivalenceLifting p) t (f ≫ e) d'
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily e z c.map f c.comm.symm
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily e z t g ht
  have ha₀ : a ≫ pullback.fst p e = c.map := pullback.lift_fst _ _ _
  have hb₀ : b ≫ pullback.fst p e = t := pullback.lift_fst _ _ _
  have ha₁ : a ≫ pullback.snd p e = f := pullback.lift_snd _ _ _
  have hb₁ : b ≫ pullback.snd p e = g := pullback.lift_snd _ _ _
  let L := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq c.exactComponentIso ha₀.symm hb₀.symm
  let R := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d ha₁.symm hb₁.symm
  have hL₀ : (a ≫ pullback.fst p e) ≫ p = f ≫ e :=
    (congrArg (fun v => v ≫ p) ha₀).trans c.comm
  have hL₁ : (b ≫ pullback.fst p e) ≫ p = g ≫ e :=
    (congrArg (fun v => v ≫ p) hb₀).trans ht.symm
  have hR₀ : (a ≫ pullback.snd p e) ≫ e = f ≫ e := congrArg (fun v => v ≫ e) ha₁
  have hR₁ : (b ≫ pullback.snd p e) ≫ e = g ≫ e := congrArg (fun v => v ≫ e) hb₁
  have hc : HEq (c.exactComponentIso.postcomp p) d' :=
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ c.comm rfl).symm.trans
      (heq_of_eq c.exactComponentIso_postcomp_normalized)
  have hl : HEq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (L.postcomp p) hL₀ hL₁) (d.postcomp e) :=
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans
        (hc.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)))
  have hr : HEq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (R.postcomp e) hR₀ hR₁) (d.postcomp e) :=
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _)
  exact ⟨c.map, c.comm.symm, ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackFunctorIsoOfCommonNormalizedIsos p e a b L R
    hL₀ hL₁ hR₀ hR₁ (eq_of_heq (hl.trans hr.symm))⟩⟩
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
