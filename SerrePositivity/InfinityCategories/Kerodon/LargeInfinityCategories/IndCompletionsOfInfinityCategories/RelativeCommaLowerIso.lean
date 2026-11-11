module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeCommaTransport

/-!
概要：同じ上側全族を保ち、底の像が等号同型である下側比較を実 under comma へ戻す。
方針：指定下側同型と上側恒等同型を、同じ実 pullback で貼り合わせる。
規約：元の上側族と指定変換の値を保持する。
使われ方：全余錐から戻した指定下側変換の旧族上の相殺。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の同じ上側族で、底固定の下側比較は実 under comma の比較になる。
方針：二成分の指定像を等号同型で照合。
規約：同じ全族と指定値。使われ方：元の指定変換の下の余錐への帰還。 -/
lemma nonempty_relativeCommaFamily_iso_of_lowerIso
    {A K E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (e : E ⟶ B) (z : K ⟶ B) (q : A ⟶ E) (t t' : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (ht : q ≫ e = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z)
    (ht' : q ≫ e = t' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso t t') (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (d.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z))) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily e z t q ht)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily e z t' q ht')) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily e z t q ht
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily e z t' q ht'
  have ha₀ : a ≫ pullback.fst p e = t := pullback.lift_fst _ _ _
  have hb₀ : b ≫ pullback.fst p e = t' := pullback.lift_fst _ _ _
  have ha₁ : a ≫ pullback.snd p e = q := pullback.lift_snd _ _ _
  have hb₁ : b ≫ pullback.snd p e = q := pullback.lift_snd _ _ _
  let L := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d ha₀.symm hb₀.symm
  let R := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso q q from Iso.refl _) ha₁.symm hb₁.symm
  have hLp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (L.postcomp p)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackProjectionComposite_eq p e a) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackProjectionComposite_eq p e b)) :=
    (hd.of_heq (congrArg (fun m ↦ m ≫ p) ha₀.symm)
      (congrArg (fun m ↦ m ≫ p) hb₀.symm)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _)).of_heq
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackProjectionComposite_eq p e a) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackProjectionComposite_eq p e b)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (R.postcomp e) :=
    ((show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso q q from Iso.refl _) from ⟨rfl, rfl⟩).of_heq
      ha₁.symm hb₁.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)).postcomp e
  have hbase : (a ≫ pullback.snd p e) ≫ e = (b ≫ pullback.snd p e) ≫ e := by
    rw [ha₁, hb₁]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackFunctorIsoOfCompatibleIsos p e a b L R
    ((hLp.eq hbase).trans (hR.eq hbase).symm)⟩
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
