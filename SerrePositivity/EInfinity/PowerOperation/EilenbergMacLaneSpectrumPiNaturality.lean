module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneSpectrumLevelNaturality
public import SerrePositivity.KST.Spectra.StageComparisonNaturality

/-!
# 実 EM スペクトルの整数 π/H 比較の自然性

DAG XIII §2.2 のスペクトル忘却の比較。標準計算段への同じ次数の移送を使い、
整数次数の比較が全鎖写像に対して自然であることを示す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (OmegaSpectrum pointedGroupMap)
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
variable (A : Type u) [CommRing A]

/-- 正次数の段の誘導準同型は、同じ点つき射の誘導準同型である。 -/
lemma omegaLevelMap_succ {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (r n : ℕ) :
    OmegaSpectrum.levelMap f r (n + 1) = pointedGroupMap n (f.app r) := rfl

/-- 同じ整数比較の順写像を、指定計算段の比較へ戻す。 -/
lemma eilenbergMacLaneSpectrumPiCohomologyEquiv_apply (M : Complex A) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup ((eilenbergMacLaneSpectrumFunctor A).obj M) j) :
    let r := OmegaSpectrum.canonicalLevel j
    let n := OmegaSpectrum.degree j r - 1
    let hn : n + 1 = OmegaSpectrum.degree j r := by
      have := OmegaSpectrum.canonicalDegree_pos j
      dsimp only [n, r]
      omega
    let hj : (n : ℤ) + 1 = j + (r : ℤ) := by
      have ha := OmegaSpectrum.canonicalLevel_admissible j
      have he := congrArg (fun k : ℕ => (k : ℤ)) hn
      dsimp only [OmegaSpectrum.degree] at he
      dsimp only [r] at *
      omega
    eilenbergMacLaneSpectrumPiCohomologyEquiv A M j a =
      eilenbergMacLaneSpectrumLevelPiCohomologyEquivAt A M j r n hj
        (OmegaSpectrum.levelHomotopyCongr ((eilenbergMacLaneSpectrumFunctor A).obj M)
          (k := r) (l := r) (n := OmegaSpectrum.degree j r) (m := n + 1) rfl hn.symm a) := rfl

/-- 整数次数の実スペクトルの比較は、指定した元の鎖写像と可換する。 -/
lemma eilenbergMacLaneSpectrumPiCohomologyEquiv_naturality
    {M N : Complex A} (f : M ⟶ N) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup ((eilenbergMacLaneSpectrumFunctor A).obj M) j) :
    eilenbergMacLaneSpectrumPiCohomologyEquiv A N j
      (OmegaSpectrum.homotopyMap ((eilenbergMacLaneSpectrumFunctor A).map f) j a) =
      Multiplicative.ofAdd ((HomologicalComplex.homologyMap f (-j)).hom
        (Multiplicative.toAdd (eilenbergMacLaneSpectrumPiCohomologyEquiv A M j a))) := by
  rw [eilenbergMacLaneSpectrumPiCohomologyEquiv_apply,
    eilenbergMacLaneSpectrumPiCohomologyEquiv_apply]
  let X := (eilenbergMacLaneSpectrumFunctor A).obj M
  let Y := (eilenbergMacLaneSpectrumFunctor A).obj N
  let sf := (eilenbergMacLaneSpectrumFunctor A).map f
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
  have hcast := OmegaSpectrum.levelHomotopyCongr_natural sf
    (k := r) (l := r) (n := OmegaSpectrum.degree j r) (m := n + 1) rfl hn.symm a
  have hmap := OmegaSpectrum.homotopyMap_eq_levelMap sf j
  rw [← hmap] at hcast
  rw [omegaLevelMap_succ] at hcast
  have h₁ := congrArg (eilenbergMacLaneSpectrumLevelPiCohomologyEquivAt A N j r n hj) hcast
  have h₂ := eilenbergMacLaneSpectrumLevelPiCohomologyEquivAt_naturality A f j r n hj
    (OmegaSpectrum.levelHomotopyCongr X rfl hn.symm a)
  have h := h₁.trans h₂
  dsimp only [X, Y, sf, r, n] at h
  exact h

end SerrePositivity.EInfinity.PowerOperation
