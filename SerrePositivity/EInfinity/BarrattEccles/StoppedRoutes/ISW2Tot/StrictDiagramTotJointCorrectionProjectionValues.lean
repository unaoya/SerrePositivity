module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointPairingProjectionValues
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointPairingCorrection
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquarePrecompositionCoherence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEndpointProjection
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoChainTransport

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じ補正 pairing の全同型の二射影と、元の全端点比較の同じ値。
方針：元の指定 path の厳密な像から端点の型の等式を外し、同じ全同型の二射影を使う。
規約：高次単体を持つ元の全同型の値を保持する。点ごとの同値で代用しない。
使われ方：元の単位と roof の全族の端点比較の接続。
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
local instance jointCorrectionProjectionValuesModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointCorrectionProjectionValuesFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance jointCorrectionProjectionValuesBase : Quasicategory ((_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op ⊗ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) :=
  quasicategory_tensor _ _

/-- 同じ元の全補正比較の射影の指定値を、元の全端点比較の同じ値へ回収する。 -/
lemma strictBETotJointSourceCorrectionIso_projection_value {E : SSet.{u+1}}
    (q : (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op ⊗ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A ⟶ E) :
    HEq (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).postcomp
      (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))).postcomp q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairingBaseIso A).symm q) := by
  have hn := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairingCorrection A).exactComponentIso_postcomp_normalized
  change functorIsoOfEq
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).postcomp (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing_projection A) rfl =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairingBasePathIso A at hn
  have h₀ := functorIsoOfEq_postcomp_heq_of_eq _ _ _ _ hn q
  have h₁ := functorIsoOfEq_postcomp_heq
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairingBaseIso A).symm rfl
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing_projection A).symm q
  exact h₀.symm.trans h₁

/-- 同じ元の全補正比較の射影の指定値を、元の全端点比較の同じ値へ回収する。 -/
lemma strictBETotJointSourceCorrectionIso_left_value :
    HEq ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationDomainIso A).symm := by
  have h := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectionIso_projection_value A (fst (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))).trans
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairingBaseIso_symm_fst A)
  have hm := functorIso_postcomp_heq_of_map_eq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A)
    (twistedArrowProjection_fst (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
  have hc := functorIso_postcomp_postcomp (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A)
    (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) (fst (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
  exact hm.trans ((heq_of_eq hc.symm).trans h)

/-- 同じ元の全補正比較の射影の指定値を、元の全端点比較の同じ値へ回収する。 -/
lemma strictBETotJointSourceCorrectionIso_right_value :
    HEq ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceTargetReplacementIso A).symm := by
  have h := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectionIso_projection_value A (snd (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))).trans
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairingBaseIso_symm_snd A)
  have hm := functorIso_postcomp_heq_of_map_eq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A)
    (twistedArrowProjection_snd (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
  have hc := functorIso_postcomp_postcomp (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A)
    (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) (snd (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
  exact hm.trans ((heq_of_eq hc.symm).trans h)

/-- 同じ元の全 pairing の射影を、元の端点の全図式へ厳密に合わせる。 -/
lemma strictBETotJointSourceCorrectedPairing_left :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing A ≫ edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceOriginalNativeDomain A := by
  rw [← twistedArrowProjection_fst, ← Category.assoc,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing_projection,
    ← _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceOriginalNativeEndpoints_eq, lift_fst]

/-- 同じ元の全 pairing の射影を、元の端点の全図式へ厳密に合わせる。 -/
lemma strictBETotJointSourceNativePairing_left :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A ≫ edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeDomain A := by
  rw [← twistedArrowProjection_fst, ← Category.assoc,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing_projection,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairingBase_eq_lift, lift_fst]

/-- 同じ元の全 pairing の射影を、元の端点の全図式へ厳密に合わせる。 -/
lemma strictBETotJointSourceCorrectedPairing_right :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing A ≫ edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceOriginalNativeCodomain A := by
  rw [← twistedArrowProjection_snd, ← Category.assoc,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing_projection,
    ← _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceOriginalNativeEndpoints_eq, lift_snd]

/-- 同じ元の全 pairing の射影を、元の端点の全図式へ厳密に合わせる。 -/
lemma strictBETotJointSourceNativePairing_right :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A ≫ edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeCodomain A := by
  rw [← twistedArrowProjection_snd, ← Category.assoc,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing_projection,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairingBase_eq_lift, lift_snd]

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

end
