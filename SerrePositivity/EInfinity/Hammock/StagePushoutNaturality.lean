module
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

public import SerrePositivity.EInfinity.Hammock.LengthStagePushout
public import SerrePositivity.EInfinity.Hammock.LengthBoundaryNaturality

/-!
# 元の段階の pushout の比較の四辺

概要：元の自然変換の境界余積と最大語余積への作用は段階の四つの射と可換する。
方針：元の余積包含で検査し、境界の制限と元の段階の標準射の自然性へ帰着する。
規約：比較射は同じ自然変換の成分から定める Limits.Sigma.map。
使われ方：proper 図式の有限段階の弱同値の帰納。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

variable {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G) (n : ℕ)

def stageBoundarySumMap : stageBoundarySum F n ⟶ stageBoundarySum G n :=
  Limits.Sigma.map (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => lengthBoundaryMap η n a.val)

def stageTopSumMap : stageTopSum F n ⟶ stageTopSum G n :=
  Limits.Sigma.map (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => η.app a.val)

lemma stageBoundarySumMap_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n) :
    Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => (lengthBoundary F n a.val).toFunctor) a ≫
        stageBoundarySumMap η n = lengthBoundaryMap η n a.val ≫
      Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => (lengthBoundary G n a.val).toFunctor) a :=
  Sigma.ι_map _ _

lemma stageTopSumMap_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n) :
    Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => F.obj a.val) a ≫ stageTopSumMap η n =
      η.app a.val ≫ Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => G.obj a.val) a :=
  Sigma.ι_map _ _

lemma stageBoundarySumMap_inclusion :
    stageBoundarySumInclusion F n ≫ stageTopSumMap η n =
      stageBoundarySumMap η n ≫ stageBoundarySumInclusion G n := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, stageBoundarySumInclusion_fac, Category.assoc, stageTopSumMap_fac]
  rw [← Category.assoc (Sigma.ι _ a) (stageBoundarySumMap η n),
    stageBoundarySumMap_fac, Category.assoc, stageBoundarySumInclusion_fac]
  rw [← Category.assoc (lengthBoundaryMap η n a.val), lengthBoundaryMap_ι]
  exact (Category.assoc _ _ _).symm

lemma stageBoundarySumMap_attach (hF : ProperDiagram F) (hG : ProperDiagram G) :
    stageBoundaryAttach n hF ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η n =
      stageBoundarySumMap η n ≫ stageBoundaryAttach n hG := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, stageBoundaryAttach_fac, ← Category.assoc,
    stageBoundarySumMap_fac, Category.assoc, stageBoundaryAttach_fac,
    lengthBoundaryMap_attach]

lemma stageTopSumMap_inclusion :
    stageTopInclusion F n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η (n + 1) =
      stageTopSumMap η n ≫ stageTopInclusion G n := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, stageTopInclusion_fac, ← Category.assoc, stageTopSumMap_fac,
    Category.assoc, stageTopInclusion_fac, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_map]

lemma stageBoundarySumInclusion_mono : Mono (stageBoundarySumInclusion F n) := by
  have he : stageBoundarySumInclusion F n = Limits.Sigma.map
      (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => (lengthBoundary F n a.val).ι) := by
    apply Sigma.hom_ext
    intro a
    rw [stageBoundarySumInclusion_fac, Sigma.ι_map]
  rw [he]
  infer_instance

end SerrePositivity.EInfinity.Hammock
