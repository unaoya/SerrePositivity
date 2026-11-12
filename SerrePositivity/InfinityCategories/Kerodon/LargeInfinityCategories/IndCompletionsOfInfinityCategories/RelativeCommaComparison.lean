module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.PullbackCompatibleFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FullyFaithfulSquareRelativeIsoReflection
/-!
概要：指定した下側変換を保つ二つの comma 族の比較を、実 under comma 内へ戻す。
方針：下側の恒等同型と上側の指定同型を、left fibration の引き戻しで束ねる。
規約：元の二族と指定変換を保持し、pullback の Kan 性を仮定しない。
使われ方：Ind 射図式の始点評価下の相対補間と余錐の帰還。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {A K E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
  (e : E ⟶ B) (z : K ⟶ B) (f g : A ⟶ E) (t : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
  (hf : f ≫ e = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) (hg : g ≫ e = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z)
/-- 概要：指定した下側変換と元の全族を、実 under comma の族へ束ねる。
方針：厳密な pullback の普遍性を使う。規約：同じ全射を保持。
使われ方：相対補間の元のパラメーター族。 -/
def relativeCommaFamily (f : A ⟶ E) (h : f ≫ e = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) :=
  pullback.lift t f h.symm
/-- 概要：同じ下側変換の下で、射影が元の等号同型となる指定比較を実 comma 内へ戻す。
方針：二成分を貼り合わせ、左ファイブレーションで可逆性を反映する。
規約：同じ全族と指定変換を保持。使われ方：補間余錐の元の試験族への帰還。 -/
lemma nonempty_relativeCommaFamily_iso (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (hd : d.postcomp e = eqToIso (congrArg
      (fun v => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex v)) (hf.trans hg.symm))) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (relativeCommaFamily e z t f hf)
      (relativeCommaFamily e z t g hg)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z
  let a := relativeCommaFamily e z t f hf
  let b := relativeCommaFamily e z t g hg
  have ha₀ : a ≫ pullback.fst p e = t := pullback.lift_fst _ _ _
  have hb₀ : b ≫ pullback.fst p e = t := pullback.lift_fst _ _ _
  have ha₁ : a ≫ pullback.snd p e = f := pullback.lift_snd _ _ _
  have hb₁ : b ≫ pullback.snd p e = g := pullback.lift_snd _ _ _
  let L := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso t t from Iso.refl _) ha₀.symm hb₀.symm
  let R := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq d ha₁.symm hb₁.symm
  have hL : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso L :=
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso t t from Iso.refl _) from ⟨rfl, rfl⟩).of_heq
      ha₀.symm hb₀.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)
  have hLp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (L.postcomp p)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackProjectionComposite_eq p e a) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackProjectionComposite_eq p e b)) :=
    (hL.postcomp p).of_heq (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackProjectionComposite_eq p e a)
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackProjectionComposite_eq p e b) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _)
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (R.postcomp e) := by
    have hde : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (d.postcomp e) := by
      rw [hd]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isFunctorEqIso_eqToIso (hf.trans hg.symm)
    exact hde.of_heq (congrArg (fun v => v ≫ e) ha₁.symm)
      (congrArg (fun v => v ≫ e) hb₁.symm) (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _)
  have hbase : (a ≫ pullback.snd p e) ≫ e = (b ≫ pullback.snd p e) ≫ e := by
    rw [ha₁, hb₁]
    exact hf.trans hg.symm
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.pullbackFunctorIsoOfCompatibleIsos p e a b L R
    ((hLp.eq hbase).trans (hR.eq hbase).symm)⟩
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
