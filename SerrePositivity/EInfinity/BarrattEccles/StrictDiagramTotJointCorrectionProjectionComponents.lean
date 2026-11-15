module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointCorrectionProjectionValues
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoComponentPost
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoComponentTransport

/-!
概要：同じ全補正比較の成分を射影した値は、元の全端点比較の同じ成分。
方針：全同型の指定値の照合と、既存の成分評価・後合成の法則を使う。
規約：元の全同型と同じ成分の像を保持する。
使われ方：元の corrected pairing の単位ラベルの像の計算。
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
local instance jointCorrectionProjectionComponentsModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointCorrectionProjectionComponentsFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance jointCorrectionProjectionComponentsBase : Quasicategory ((CAlg_R A).op ⊗ CAlg_R A) :=
  quasicategory_tensor _ _

/-- 元の全補正比較の同じ成分の左射影は、元の augmentation 同型の逆の同じ成分。 -/
lemma strictBETotJointSourceCorrectionIso_left_component (t : StrictBETotJointSourceElements A) :
    HEq (VertexIso.map ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t))
      (edgewiseLeft (CAlg_R A)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        (strictBETotJointSourceAugmentationDomainIso A).symm (nerveVertex t)) := by
  have h₀ := functorIso_app_postcomp_heq (strictBETotJointSourceCorrectedPairingIso A)
    (edgewiseLeft (CAlg_R A)) (nerveVertex t)
  have h₁ := functorIso_app_heq_of_heq
    ((strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseLeft (CAlg_R A)))
    (strictBETotJointSourceAugmentationDomainIso A).symm
    (strictBETotJointSourceCorrectedPairing_left A) (strictBETotJointSourceNativePairing_left A)
    (strictBETotJointSourceCorrectionIso_left_value A) (nerveVertex t)
  exact h₀.symm.trans h₁

/-- 元の全補正比較の同じ成分の右射影は、元の標的置換同型の逆の同じ成分。 -/
lemma strictBETotJointSourceCorrectionIso_right_component (t : StrictBETotJointSourceElements A) :
    HEq (VertexIso.map ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t))
      (edgewiseRight (CAlg_R A)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        (strictBETotJointSourceTargetReplacementIso A).symm (nerveVertex t)) := by
  have h₀ := functorIso_app_postcomp_heq (strictBETotJointSourceCorrectedPairingIso A)
    (edgewiseRight (CAlg_R A)) (nerveVertex t)
  have h₁ := functorIso_app_heq_of_heq
    ((strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseRight (CAlg_R A)))
    (strictBETotJointSourceTargetReplacementIso A).symm
    (strictBETotJointSourceCorrectedPairing_right A) (strictBETotJointSourceNativePairing_right A)
    (strictBETotJointSourceCorrectionIso_right_value A) (nerveVertex t)
  exact h₀.symm.trans h₁

end SerrePositivity.EInfinity.BarrattEccles

end
