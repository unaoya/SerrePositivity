module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointCorrectionProjectionValues
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoComponentPost
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoComponentTransport

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
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

namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory _root_.CategoryTheory.MonoidalClosed
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped _root_.Simplicial
open _root_.HomotopicalAlgebra
open _root_.SerrePositivity.EInfinity.BarrattEccles
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange
open _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
variable (A : Type u) [CommRing A]
local instance jointCorrectionProjectionComponentsModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointCorrectionProjectionComponentsFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance jointCorrectionProjectionComponentsBase : Quasicategory ((_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op ⊗ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) :=
  quasicategory_tensor _ _

/-- 元の全補正比較の同じ成分の左射影は、元の augmentation 同型の逆の同じ成分。 -/
lemma strictBETotJointSourceCorrectionIso_left_component (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    HEq (VertexIso.map ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t))
      (edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationDomainIso A).symm (nerveVertex t)) := by
  have h₀ := functorIso_app_postcomp_heq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A)
    (edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) (nerveVertex t)
  have h₁ := functorIso_app_heq_of_heq
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationDomainIso A).symm
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing_left A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing_left A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectionIso_left_value A) (nerveVertex t)
  exact h₀.symm.trans h₁

/-- 元の全補正比較の同じ成分の右射影は、元の標的置換同型の逆の同じ成分。 -/
lemma strictBETotJointSourceCorrectionIso_right_component (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    HEq (VertexIso.map ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t))
      (edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceTargetReplacementIso A).symm (nerveVertex t)) := by
  have h₀ := functorIso_app_postcomp_heq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A)
    (edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) (nerveVertex t)
  have h₁ := functorIso_app_heq_of_heq
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceTargetReplacementIso A).symm
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing_right A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing_right A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectionIso_right_value A) (nerveVertex t)
  exact h₀.symm.trans h₁

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

end
