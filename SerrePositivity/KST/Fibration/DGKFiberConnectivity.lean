module
public import SerrePositivity.KST.Fibration.DGKPiZeroCofinality
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFConnectivity
public import SerrePositivity.KST.Spectra.HomotopyFiberVanishing

/-! # 固定 K の同じ dg 商射の実 BF homotopy fiber の連結性

元の K₀ 全射性と両端の負次数消滅を、元の BF 長完全列に適用する。
この fiber を K(D) と同定する fibration 定理は入力せず、別工程に残す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]

/-- 固定 K の同じ元の BF 射に対して構成済みの実 homotopy fiber。 -/
abbrev dgKBFHomotopyFiber {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :=
  OmegaSpectrum.homotopyFiber (dgKInputSpectrumMap A f)

/-- 同じ固定 K の実頂点の全負整数 π 群は、元の BF 比較により零群。 -/
theorem dgKPi_negative_subsingleton (P : PerfDGInput.{u, v} A) (j : ℤ) (hj : j < 0) :
    Subsingleton ((SpectrumHo.piFunctor j).obj
      (HomotopyCategory.mk ((dgKInputK A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P)))) := by
  have := presentedPerfectDGBFOmegaSpectrum_negative_subsingleton A P j hj
  exact (dgKPiComparison A P j).commGroupIsoToMulEquiv.injective.subsingleton

/-- 同じ dg 射の K₀ 全射性から、元の実 BF fiber の全負整数群が消える。 -/
theorem dgKBFHomotopyFiber_negative_subsingleton_of_kZero_surjective
    {Q R : PerfDGInput.{u, v} A} (g : Q ⟶ R)
    (hs : Function.Surjective (dgNuKZeroMap A g))
    (j : ℤ) (hj : j < 0) :
    Subsingleton (OmegaSpectrum.homotopyGroup (dgKBFHomotopyFiber A g) j) := by
  have := presentedPerfectDGBFOmegaSpectrum_negative_subsingleton A Q j hj
  apply OmegaSpectrum.homotopyFiberGroup_subsingleton_of_injective_surjective
    (dgKInputSpectrumMap A g) j (fun _ _ _ => Subsingleton.elim _ _)
  by_cases he : j + 1 = 0
  · rw [he]
    exact (dgKZeroBFMap_surjective_iff A g).mpr hs
  · have := presentedPerfectDGBFOmegaSpectrum_negative_subsingleton A R (j + 1) (by omega)
    intro a
    exact ⟨1, Subsingleton.elim _ _⟩

/-- ν 像が Verdier 列なら、同じ固定 K 商射の実 BF fiber の全負整数群は消える。 -/
theorem dgKBFHomotopyFiber_negative_subsingleton_of_verdier
    {P Q R : PerfDGInput.{u, v} A} (f : P ⟶ Q) (g : Q ⟶ R)
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue A P) (dgKInputStableValue A Q) from dgKInputNuMap A f)
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue A Q) (dgKInputStableValue A R) from dgKInputNuMap A g))
    (j : ℤ) (hj : j < 0) :
    Subsingleton (OmegaSpectrum.homotopyGroup (dgKBFHomotopyFiber A g) j) :=
  dgKBFHomotopyFiber_negative_subsingleton_of_kZero_surjective A g
    (dgNuKZeroMap_surjective_of_verdier A f g h) j hj

end SerrePositivity.KST.Fibration
