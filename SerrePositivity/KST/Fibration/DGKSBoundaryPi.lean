module
public import SerrePositivity.KST.SConstruction.DGKFixedSConstruction
public import SerrePositivity.KST.Spectra.StageComparisonNaturality
public import SerrePositivity.KST.Spectra.PointedHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-! # 固定 dg K の非負次数を、ν(P) の一段 S• 境界商で計算する

比較は同じ正段の前向き弱比較の逆と、元の段比較から作る。
入力射についても元の S• 境界商射を保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]

/-- ν(P) の同じ一段 S• 境界商の、元の基点を持つ Ex∞ Kan 値。 -/
abbrev dgKSBoundaryKan (P : PerfDGInput.{u, v} A) : PointedSimplicialSet.{max (u + 1) v} :=
  ((presentedPerfectDGBoundaryKanEnrichedFunctor A 0).obj P).obj

instance dgKSBoundaryKan_kanComplex (P : PerfDGInput.{u, v} A) :
    KanComplex (dgKSBoundaryKan A P).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 同じ元の境界 Kan 値から固定 K(P) の第一正段への実比較。 -/
def dgKSBoundaryStageMap (P : PerfDGInput.{u, v} A) :
    dgKSBoundaryKan A P ⟶ ((dgKInputSpectrum A P).level 1).space :=
  (presentedPerfectDGBFPositiveStage A 0).comparison P

/-- 同じ前向き比較は、零次数を含む全ての元の基点固定 π 集合で全単射。 -/
def dgKSBoundaryStagePiEquiv (P : PerfDGInput.{u, v} A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (dgKSBoundaryKan A P).right n (dgKSBoundaryKan A P).basepoint ≃
      OmegaSpectrum.levelHomotopy (dgKInputSpectrum A P) 1 n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism n (dgKSBoundaryStageMap A P).right
    (presentedPerfectDGBFStageComparison_piIsomorphism A 0
      (presentedPerfectDGBFPositiveStage A 0) P)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)

/-- 元の入力射の境界商作用と第一正段の作用は、同じ実比較で可換。 -/
theorem dgKSBoundaryStagePiEquiv_naturality {P Q : PerfDGInput.{u, v} A}
    (f : P ⟶ Q) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (dgKSBoundaryKan A P).right n (dgKSBoundaryKan A P).basepoint) :
    dgKSBoundaryStagePiEquiv A Q n
        (pointedHomotopyMap n (presentedPerfectDGBoundaryKanMap A 0 f).hom a) =
      OmegaSpectrum.levelMap (dgKInputSpectrumMap A f) 1 n
        (dgKSBoundaryStagePiEquiv A P n a) := by
  have h := congrArg (fun g => pointedHomotopyMap n g a)
    (dgKInputSBoundaryKanComparison_naturality A 0 f)
  rw [pointedHomotopyMap_comp, pointedHomotopyMap_comp] at h
  simp only [dgKSBoundaryStagePiEquiv, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism_apply]
  exact h

/-- 非負次数の固定 BF K 群を、同じ元の一段 S• 境界商の π_(j+1) で表示する。 -/
def dgKBFBoundaryPiEquiv (P : PerfDGInput.{u, v} A) (j : ℤ) (hj : 0 ≤ j) :
    OmegaSpectrum.homotopyGroup (dgKInputSpectrum A P) j ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (dgKSBoundaryKan A P).right (OmegaSpectrum.degree j 1)
        (dgKSBoundaryKan A P).basepoint :=
  (OmegaSpectrum.homotopyGroupEquivAt (dgKInputSpectrum A P) j 1 (by omega)).toEquiv.trans
    (dgKSBoundaryStagePiEquiv A P (OmegaSpectrum.degree j 1)).symm

/-- 同じ非負次数の表示は、元の実 BF 射と元の境界商射に関して自然。 -/
theorem dgKBFBoundaryPiEquiv_naturality {P Q : PerfDGInput.{u, v} A}
    (f : P ⟶ Q) (j : ℤ) (hj : 0 ≤ j)
    (a : OmegaSpectrum.homotopyGroup (dgKInputSpectrum A P) j) :
    dgKBFBoundaryPiEquiv A Q j hj (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) j a) =
      pointedHomotopyMap (OmegaSpectrum.degree j 1) (presentedPerfectDGBoundaryKanMap A 0 f).hom
        (dgKBFBoundaryPiEquiv A P j hj a) := by
  apply (dgKSBoundaryStagePiEquiv A Q (OmegaSpectrum.degree j 1)).injective
  rw [dgKSBoundaryStagePiEquiv_naturality]
  change (dgKSBoundaryStagePiEquiv A Q _)
      ((dgKSBoundaryStagePiEquiv A Q _).symm _) =
    OmegaSpectrum.levelMap (dgKInputSpectrumMap A f) 1 _
      ((dgKSBoundaryStagePiEquiv A P _) ((dgKSBoundaryStagePiEquiv A P _).symm _))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact OmegaSpectrum.homotopyGroupEquivAt_natural (dgKInputSpectrumMap A f) j 1 _ a

end SerrePositivity.KST.Fibration
