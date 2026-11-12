module
public import SerrePositivity.KST.Fibration.DGKSBoundaryPi
public import SerrePositivity.KST.Fibration.DGKPiComparison

/-! # 固定 K の元の Sp π 作用と、ν の一段 S• 境界商の π 作用

固定頂点・辺の比較を通じ、同じ入力射について可換な実全単射を構成する。
この自然性は入力射についての主張であり、四角形全体の比較を代用しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]

/-- 固定 K の実頂点の非負次数 π を、ν(P) の同じ境界商の π 集合へ同定。 -/
def dgKNativeSBoundaryPiEquiv (P : PerfDGInput.{u, v} A) (j : ℤ) (hj : 0 ≤ j) :
    ((SpectrumHo.piFunctor j).obj (HomotopyCategory.mk
      ((dgKInputK A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P)))) ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (dgKSBoundaryKan A P).right (OmegaSpectrum.degree j 1)
        (dgKSBoundaryKan A P).basepoint :=
  (dgKPiComparison A P j).commGroupIsoToMulEquiv.toEquiv.trans
    (dgKBFBoundaryPiEquiv A P j hj)

/-- 同じ元の K 辺の π 作用は、元の S• 境界商射の π 作用と可換。 -/
theorem dgKNativeSBoundaryPiEquiv_naturality {P Q : PerfDGInput.{u, v} A}
    (f : P ⟶ Q) (j : ℤ) (hj : 0 ≤ j)
    (a : (SpectrumHo.piFunctor j).obj (HomotopyCategory.mk
      ((dgKInputK A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P)))) :
    dgKNativeSBoundaryPiEquiv A Q j hj
        (((SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk
          (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK A)).toTruncated))).hom a) =
      pointedHomotopyMap (OmegaSpectrum.degree j 1) (presentedPerfectDGBoundaryKanMap A 0 f).hom
        (dgKNativeSBoundaryPiEquiv A P j hj a) := by
  have h := congrArg (fun m => m.hom a) (dgKPiComparison_naturality A f j)
  change (dgKPiComparison A Q j).hom.hom
      (((SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK A)).toTruncated))).hom a) =
    OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) j
      ((dgKPiComparison A P j).hom.hom a) at h
  change dgKBFBoundaryPiEquiv A Q j hj ((dgKPiComparison A Q j).hom.hom _) = _
  rw [h]
  exact dgKBFBoundaryPiEquiv_naturality A f j hj _

/-- 元の K 辺の非負次数 π 全単射性は、同じ一段 S• 境界商射で検査できる。 -/
theorem dgKNativePiMap_bijective_iff_sBoundary {P Q : PerfDGInput.{u, v} A}
    (f : P ⟶ Q) (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (((SpectrumHo.piFunctor j).map
      (Truncated.HomotopyCategory.homMk
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK A)).toTruncated))).hom) ↔
      Function.Bijective (pointedHomotopyMap (OmegaSpectrum.degree j 1)
        (presentedPerfectDGBoundaryKanMap A 0 f).hom) := by
  let eP := dgKNativeSBoundaryPiEquiv A P j hj
  let eQ := dgKNativeSBoundaryPiEquiv A Q j hj
  let m := ((SpectrumHo.piFunctor j).map (Truncated.HomotopyCategory.homMk
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK A)).toTruncated))).hom
  let b := pointedHomotopyMap (OmegaSpectrum.degree j 1)
    (presentedPerfectDGBoundaryKanMap A 0 f).hom
  have he : eQ ∘ m = b ∘ eP := by
    funext a
    exact dgKNativeSBoundaryPiEquiv_naturality A f j hj a
  change Function.Bijective m ↔ Function.Bijective b
  calc
    Function.Bijective m ↔ Function.Bijective (eQ ∘ m) :=
      (Function.Bijective.of_comp_iff' eQ.bijective _).symm
    _ ↔ Function.Bijective (b ∘ eP) := by rw [he]
    _ ↔ Function.Bijective b := Function.Bijective.of_comp_iff _ eP.bijective

end SerrePositivity.KST.Fibration
