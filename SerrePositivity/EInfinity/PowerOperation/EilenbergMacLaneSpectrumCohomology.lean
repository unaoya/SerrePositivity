module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSpectrumFunctor
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor

/-!
# 実 Eilenberg–Mac Lane スペクトルの整数 π/H 比較

DAG XIII §2.2 のスペクトル忘却への前段。指定単射置換から元の Γ の段への
実射影を、標準計算段の π 同型として使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (OmegaSpectrum KanSequence)
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets
variable (A : Type u) [CommRing A]

/-- 同じ実スペクトルの整数 π_j は、元の複体の H^{-j} である。 -/
def eilenbergMacLaneSpectrumPiCohomologyEquiv (M : Complex A) (j : ℤ) :
    OmegaSpectrum.homotopyGroup ((eilenbergMacLaneSpectrumFunctor A).obj M) j ≃*
      Multiplicative (M.homology (-j)) := by
  let X := (eilenbergMacLaneSpectrumFunctor A).obj M
  let r := OmegaSpectrum.canonicalLevel j
  let n := OmegaSpectrum.degree j r - 1
  have hn : n + 1 = OmegaSpectrum.degree j r := by
    have := OmegaSpectrum.canonicalDegree_pos j
    dsimp only [n, r]
    omega
  have hj : (n : ℤ) + 1 = j + (r : ℤ) := by
    have ha := OmegaSpectrum.canonicalLevel_admissible j
    have he := congrArg (fun k : ℕ => (k : ℤ)) hn
    dsimp only [OmegaSpectrum.degree] at he
    dsimp only [r] at *
    omega
  let p := (KanSequence.replacementProjection (eilenbergMacLaneSequence A M)).app r
  change OmegaSpectrum.levelHomotopy X r (OmegaSpectrum.degree j r) ≃* _
  refine (OmegaSpectrum.levelHomotopyCongr X (k := r) (l := r)
    (n := OmegaSpectrum.degree j r) (m := n + 1) rfl hn.symm).trans ?_
  exact (KanHomotopyGroup.equivOfPiIsomorphism n p.right
    (KanSequence.replacementProjection_piIsomorphism (eilenbergMacLaneSequence A M) r)
    (pointedMap_basepoint p)).trans
      (levelPiCohomologyEquivAt A M j r n hj)

end SerrePositivity.EInfinity.PowerOperation
