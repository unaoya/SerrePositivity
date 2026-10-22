module
public import SerrePositivity.KST.Fibration.DGNuKZeroCofinality
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFKZero

/-! # 固定 ν の同じ dg 辺の K₀ 作用と、固定 K の同じ BF 射の零次群作用を照合する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]

/-- 固定 ν の実三角圏 K₀ と、同じ固定 K の BF 零次群との既存の加法的比較。 -/
def dgKZeroBFComparison (P : PerfDGInput.{u, v} A) :
    TriangulatedK0 (hoFunctor.obj (dgKInputStableValue A P).obj) ≃+
      Additive (OmegaSpectrum.homotopyGroup (dgKInputSpectrum A P) 0) :=
  presentedPerfectDGBFKZeroEquiv A P

/-- 元の ν の同じ辺による K₀ 作用は、既存の S• 入力射による作用そのもの。 -/
theorem dgNuKZeroMap_eq_sourceMap {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    dgNuKZeroMap A f = triangulatedKZeroSourceMap (presentedPerfectDGBFInputStableMap A f) := by
  rw [dgNuKZeroMap_eq]
  rfl

/-- 同じ比較は、固定した元の dg 入力辺の ν 作用と BF K 作用に対して可換。 -/
theorem dgKZeroBFComparison_naturality {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q)
    (a : TriangulatedK0 (hoFunctor.obj (dgKInputStableValue A P).obj)) :
    dgKZeroBFComparison A Q (dgNuKZeroMap A f a) =
      (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) 0).toAdditive
        (dgKZeroBFComparison A P a) := by
  rw [dgNuKZeroMap_eq_sourceMap]
  exact presentedPerfectDGBFKZeroEquiv_naturality A f a

/-- 元の零次群の基礎集合も、同じ対象 K₀ と同じ比較で照合する。 -/
def dgKZeroBFEquiv (P : PerfDGInput.{u, v} A) :
    TriangulatedK0 (hoFunctor.obj (dgKInputStableValue A P).obj) ≃
      OmegaSpectrum.homotopyGroup (dgKInputSpectrum A P) 0 :=
  (dgKZeroBFComparison A P).toEquiv.trans Additive.toMul

/-- 基礎集合での比較も、同じ元の二つの準同型を結ぶ。 -/
theorem dgKZeroBFEquiv_naturality {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q)
    (a : TriangulatedK0 (hoFunctor.obj (dgKInputStableValue A P).obj)) :
    dgKZeroBFEquiv A Q (dgNuKZeroMap A f a) =
      OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) 0 (dgKZeroBFEquiv A P a) :=
  congrArg Additive.toMul (dgKZeroBFComparison_naturality A f a)

end SerrePositivity.KST.Fibration
