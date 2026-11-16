module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointPairingProjectionValues
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointPairingCorrection
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquarePrecompositionCoherence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEndpointProjection
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoChainTransport

/-!
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
local instance jointCorrectionProjectionValuesModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointCorrectionProjectionValuesFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance jointCorrectionProjectionValuesBase : Quasicategory ((CAlg_R A).op ⊗ CAlg_R A) :=
  quasicategory_tensor _ _

/-- 同じ元の全補正比較の射影の指定値を、元の全端点比較の同じ値へ回収する。 -/
lemma strictBETotJointSourceCorrectionIso_projection_value {E : SSet.{u+1}}
    (q : (CAlg_R A).op ⊗ CAlg_R A ⟶ E) :
    HEq (((strictBETotJointSourceCorrectedPairingIso A).postcomp
      (twistedArrowProjection (CAlg_R A))).postcomp q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (strictBETotJointSourceNativePairingBaseIso A).symm q) := by
  have hn := (strictBETotJointSourcePairingCorrection A).exactComponentIso_postcomp_normalized
  change functorIsoOfEq
    ((strictBETotJointSourceCorrectedPairingIso A).postcomp (twistedArrowProjection (CAlg_R A)))
    (strictBETotJointSourceCorrectedPairing_projection A) rfl =
      strictBETotJointSourcePairingBasePathIso A at hn
  have h₀ := functorIsoOfEq_postcomp_heq_of_eq _ _ _ _ hn q
  have h₁ := functorIsoOfEq_postcomp_heq
    (strictBETotJointSourceNativePairingBaseIso A).symm rfl
    (strictBETotJointSourceNativePairing_projection A).symm q
  exact h₀.symm.trans h₁

/-- 同じ元の全補正比較の射影の指定値を、元の全端点比較の同じ値へ回収する。 -/
lemma strictBETotJointSourceCorrectionIso_left_value :
    HEq ((strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseLeft (CAlg_R A)))
      (strictBETotJointSourceAugmentationDomainIso A).symm := by
  have h := (strictBETotJointSourceCorrectionIso_projection_value A (fst (CAlg_R A).op (CAlg_R A))).trans
    (strictBETotJointSourceNativePairingBaseIso_symm_fst A)
  have hm := functorIso_postcomp_heq_of_map_eq (strictBETotJointSourceCorrectedPairingIso A)
    (twistedArrowProjection_fst (CAlg_R A))
  have hc := functorIso_postcomp_postcomp (strictBETotJointSourceCorrectedPairingIso A)
    (twistedArrowProjection (CAlg_R A)) (fst (CAlg_R A).op (CAlg_R A))
  exact hm.trans ((heq_of_eq hc.symm).trans h)

/-- 同じ元の全補正比較の射影の指定値を、元の全端点比較の同じ値へ回収する。 -/
lemma strictBETotJointSourceCorrectionIso_right_value :
    HEq ((strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseRight (CAlg_R A)))
      (strictBETotJointSourceTargetReplacementIso A).symm := by
  have h := (strictBETotJointSourceCorrectionIso_projection_value A (snd (CAlg_R A).op (CAlg_R A))).trans
    (strictBETotJointSourceNativePairingBaseIso_symm_snd A)
  have hm := functorIso_postcomp_heq_of_map_eq (strictBETotJointSourceCorrectedPairingIso A)
    (twistedArrowProjection_snd (CAlg_R A))
  have hc := functorIso_postcomp_postcomp (strictBETotJointSourceCorrectedPairingIso A)
    (twistedArrowProjection (CAlg_R A)) (snd (CAlg_R A).op (CAlg_R A))
  exact hm.trans ((heq_of_eq hc.symm).trans h)

/-- 同じ元の全 pairing の射影を、元の端点の全図式へ厳密に合わせる。 -/
lemma strictBETotJointSourceCorrectedPairing_left :
    strictBETotJointSourceCorrectedPairing A ≫ edgewiseLeft (CAlg_R A) =
      strictBETotJointSourceOriginalNativeDomain A := by
  rw [← twistedArrowProjection_fst, ← Category.assoc,
    strictBETotJointSourceCorrectedPairing_projection,
    ← strictBETotJointSourceOriginalNativeEndpoints_eq, lift_fst]

/-- 同じ元の全 pairing の射影を、元の端点の全図式へ厳密に合わせる。 -/
lemma strictBETotJointSourceNativePairing_left :
    strictBETotJointSourceNativePairing A ≫ edgewiseLeft (CAlg_R A) =
      strictBETotJointSourceNativeDomain A := by
  rw [← twistedArrowProjection_fst, ← Category.assoc,
    strictBETotJointSourceNativePairing_projection,
    strictBETotJointSourceNativePairingBase_eq_lift, lift_fst]

/-- 同じ元の全 pairing の射影を、元の端点の全図式へ厳密に合わせる。 -/
lemma strictBETotJointSourceCorrectedPairing_right :
    strictBETotJointSourceCorrectedPairing A ≫ edgewiseRight (CAlg_R A) =
      strictBETotJointSourceOriginalNativeCodomain A := by
  rw [← twistedArrowProjection_snd, ← Category.assoc,
    strictBETotJointSourceCorrectedPairing_projection,
    ← strictBETotJointSourceOriginalNativeEndpoints_eq, lift_snd]

/-- 同じ元の全 pairing の射影を、元の端点の全図式へ厳密に合わせる。 -/
lemma strictBETotJointSourceNativePairing_right :
    strictBETotJointSourceNativePairing A ≫ edgewiseRight (CAlg_R A) =
      strictBETotJointSourceNativeCodomain A := by
  rw [← twistedArrowProjection_snd, ← Category.assoc,
    strictBETotJointSourceNativePairing_projection,
    strictBETotJointSourceNativePairingBase_eq_lift, lift_snd]

end SerrePositivity.EInfinity.BarrattEccles

end
