module
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LengthStagePushout
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LengthBoundaryNaturality

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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G) (n : ℕ)

def stageBoundarySumMap : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySum F n ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySum G n :=
  Limits.Sigma.map (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n a.val)

def stageTopSumMap : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopSum F n ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopSum G n :=
  Limits.Sigma.map (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => η.app a.val)

lemma stageBoundarySumMap_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n) :
    Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary F n a.val).toFunctor) a ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumMap η n = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n a.val ≫
      Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary G n a.val).toFunctor) a :=
  Sigma.ι_map _ _

lemma stageTopSumMap_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n) :
    Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => F.obj a.val) a ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopSumMap η n =
      η.app a.val ≫ Sigma.ι (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => G.obj a.val) a :=
  Sigma.ι_map _ _

lemma stageBoundarySumMap_inclusion :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumInclusion F n ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopSumMap η n =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumMap η n ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumInclusion G n := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumInclusion_fac, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopSumMap_fac]
  rw [← Category.assoc (Sigma.ι _ a) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumMap η n),
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumMap_fac, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumInclusion_fac]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n a.val), _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap_ι]
  exact (Category.assoc _ _ _).symm

lemma stageBoundarySumMap_attach (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) (hG : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram G) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundaryAttach n hF ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η n =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumMap η n ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundaryAttach n hG := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundaryAttach_fac, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumMap_fac, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundaryAttach_fac,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap_attach]

lemma stageTopSumMap_inclusion :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopInclusion F n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageMap η (n + 1) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopSumMap η n ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopInclusion G n := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopInclusion_fac, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopSumMap_fac,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageTopInclusion_fac, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_map]

lemma stageBoundarySumInclusion_mono : Mono (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumInclusion F n) := by
  have he : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumInclusion F n = Limits.Sigma.map
      (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MaximalAlternating n => (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary F n a.val).ι) := by
    apply Sigma.hom_ext
    intro a
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.stageBoundarySumInclusion_fac, Sigma.ι_map]
  rw [he]
  infer_instance

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
