module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointPairingBaseComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoPairingProjections
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoWhiskerHEq
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：元の全端点比較の同じ値と、その逆の二射影。
方針：端点の型の等式を外し、元の同型の組の二射影の法則を使う。
規約：元の augmentation と標的置換の全同型の同じ値を保持する。
使われ方：補正された全 pairing の指定端点比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
open HomotopicalAlgebra
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
variable (A : Type u) [CommRing A]
local instance jointPairingProjectionValuesModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointPairingProjectionValuesFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance jointPairingProjectionValuesBase : Quasicategory ((CAlg_R A).op ⊗ CAlg_R A) :=
  quasicategory_tensor _ _

private lemma jointPairingProjectionEqMpHeq {α β γ : Sort _} (h : α = β) (a : α) (b : γ) :
    HEq (Eq.mp h a) b ↔ HEq a b := by cases h; rfl

/-- 元の全端点比較の値は、元の二つの全同型の組と型の輸送を除いて一致する。 -/
lemma strictBETotJointSourceNativePairingBaseIso_pair_value :
    HEq (strictBETotJointSourceNativePairingBaseIso A)
      (functorIsoPair (strictBETotJointSourceAugmentationDomainIso A)
        (strictBETotJointSourceTargetReplacementIso A)) := by
  unfold strictBETotJointSourceNativePairingBaseIso
  simp only [jointPairingProjectionEqMpHeq]
  rfl

/-- 元の全端点比較の逆の第一射影は、元の augmentation 同型の同じ逆。 -/
lemma strictBETotJointSourceNativePairingBaseIso_symm_fst :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (strictBETotJointSourceNativePairingBaseIso A).symm
      (fst (CAlg_R A).op (CAlg_R A)))
      (strictBETotJointSourceAugmentationDomainIso A).symm := by
  have hs := functorIso_symm_heq_of_heq
    (functorIsoPair (strictBETotJointSourceAugmentationDomainIso A)
      (strictBETotJointSourceTargetReplacementIso A))
    (strictBETotJointSourceNativePairingBaseIso A)
    (strictBETotJointSourceNativePairingBase_eq_lift A).symm
    (strictBETotJointSourceOriginalNativeEndpoints_eq A) (strictBETotJointSourceNativePairingBaseIso_pair_value A)
  have hp := functorIso_postcomp_heq_of_heq
    (functorIsoPair (strictBETotJointSourceAugmentationDomainIso A)
      (strictBETotJointSourceTargetReplacementIso A)).symm
    (strictBETotJointSourceNativePairingBaseIso A).symm
    (strictBETotJointSourceOriginalNativeEndpoints_eq A)
    (strictBETotJointSourceNativePairingBase_eq_lift A).symm hs
    (fst (CAlg_R A).op (CAlg_R A))
  simpa only [functorIso_postcomp_symm, functorIsoPair_postcomp_fst] using hp

/-- 元の全端点比較の逆の第二射影は、元の標的置換同型の同じ逆。 -/
lemma strictBETotJointSourceNativePairingBaseIso_symm_snd :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (strictBETotJointSourceNativePairingBaseIso A).symm
      (snd (CAlg_R A).op (CAlg_R A)))
      (strictBETotJointSourceTargetReplacementIso A).symm := by
  have hs := functorIso_symm_heq_of_heq
    (functorIsoPair (strictBETotJointSourceAugmentationDomainIso A)
      (strictBETotJointSourceTargetReplacementIso A))
    (strictBETotJointSourceNativePairingBaseIso A)
    (strictBETotJointSourceNativePairingBase_eq_lift A).symm
    (strictBETotJointSourceOriginalNativeEndpoints_eq A) (strictBETotJointSourceNativePairingBaseIso_pair_value A)
  have hp := functorIso_postcomp_heq_of_heq
    (functorIsoPair (strictBETotJointSourceAugmentationDomainIso A)
      (strictBETotJointSourceTargetReplacementIso A)).symm
    (strictBETotJointSourceNativePairingBaseIso A).symm
    (strictBETotJointSourceOriginalNativeEndpoints_eq A)
    (strictBETotJointSourceNativePairingBase_eq_lift A).symm hs
    (snd (CAlg_R A).op (CAlg_R A))
  simpa only [functorIso_postcomp_symm, functorIsoPair_postcomp_snd] using hp

end SerrePositivity.EInfinity.BarrattEccles

end
