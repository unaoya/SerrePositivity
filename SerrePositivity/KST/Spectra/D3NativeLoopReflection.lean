module

public import SerrePositivity.KST.Spectra.D3LoopDiagramReflection
public import SerrePositivity.KST.Spectra.D3CommonLoopDiagramSection

/-!
概要：実 loop 全図式の零角交換による反転を、元の nativeLoop の全関手自己同型にする。
方針：元の厳密 loop 切断へ前合成し、共通実図式族との指定比較にも自然性を適用する。
規約：nativeLoop を変更せず、安定性や未証明の模型補正との一致は仮定しない。
使われ方：段ごとの自由な補正ではなく、BF 全体ですでに coherent な反転候補の保持。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の nativeLoop の実全図式に由来する coherent な反転候補。 -/
def d3NativeLoopReflection : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso nativeLoop.{u} nativeLoop :=
  (d3LoopDiagramReflection nativeLoopTargetEquivalence.inv
    nativeLoopTargetEquivalence_inv_target).precomp nativeLoopTargetEquivalence.inv

/-- 同じ nativeLoop 上の反転候補は、全関手空間で二回の合成が恒等。 -/
lemma d3NativeLoopReflection_involution :
    d3NativeLoopReflection.{u} ≪≫ d3NativeLoopReflection = Iso.refl _ := by
  have h := congrArg (fun e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e nativeLoopTargetEquivalence.{u}.inv)
    (d3LoopDiagramReflection_involution nativeLoopTargetEquivalence.inv
      nativeLoopTargetEquivalence_inv_target)
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans] at h
  have hr : (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0) from Iso.refl _).precomp
        nativeLoopTargetEquivalence.inv = Iso.refl _ := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
    exact Functor.mapIso_refl _ _
  rw [hr] at h
  exact h

namespace AdjointLoopRelativeBF

/-- 選択済み共通実全図式の始点作用にある同じ coherent な反転候補。 -/
def commonChosenLoopReflection : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso commonChosenLoopSource.{u} commonChosenLoopSource :=
  (d3LoopDiagramReflection nativeLoopTargetEquivalence.inv
    nativeLoopTargetEquivalence_inv_target).precomp commonChosenLoopDiagramFamily

/-- 元の nativeLoop への指定全図式比較は、同じ全図式反転と自然に交換する。 -/
lemma commonChosenLoopReflection_native_square :
    (commonChosenLoopDiagramNativeIso.{u}).postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0) ≪≫
      (d3LoopDiagramReflection nativeLoopTargetEquivalence.inv
        nativeLoopTargetEquivalence_inv_target).precomp
          (commonNativeLoopEndpoint ≫ nativeLoopTargetEquivalence.inv) =
    commonChosenLoopReflection ≪≫
      commonChosenLoopDiagramNativeIso.postcomp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0) :=
  d3LoopDiagramReflection_naturality nativeLoopTargetEquivalence.inv
    nativeLoopTargetEquivalence_inv_target commonChosenLoopDiagramNativeIso

end AdjointLoopRelativeBF
end SerrePositivity.KST.Spectra.OmegaSpectrum
