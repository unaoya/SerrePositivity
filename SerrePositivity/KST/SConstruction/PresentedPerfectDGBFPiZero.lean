module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFKZero
public import SerrePositivity.KST.SConstruction.KHomotopyZeroPiZero

/-! # 新 BF K の零空間の π₀ と元の三角圏 K₀ の自然比較
概要：同じ実 BF K の零空間の連結成分を、元の Perf 三角圏 K₀ と自然に同定する。
方針：整数零次群の零段表示と Kan の π₀ 比較を、既存の自然な K₀ 同型へ合成する。
規約：同じ元の実 BF 入力射を保持する。使われ方：L1e の π₀ K = K₀。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ実 BF K の整数零次群は、同じ零空間の π₀ と同値。 -/
def presentedPerfectDGBFZeroPiZeroEquiv (X : PerfDGInput.{u, v} A) :
    OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) 0 ≃
      π₀ (((presentedPerfectDGBFOmegaSpectrum A X).level 0).space).right :=
  (OmegaSpectrum.homotopyGroupEquivAt (presentedPerfectDGBFOmegaSpectrum A X) 0 0
    (by decide)).toEquiv.trans _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero

/-- 同じ零次群と零空間 π₀ の比較は、元の実 BF 射に自然。 -/
lemma presentedPerfectDGBFZeroPiZeroEquiv_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
    (a : OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) 0) :
    presentedPerfectDGBFZeroPiZeroEquiv A Y
        (OmegaSpectrum.homotopyMap (presentedPerfectDGBFMap A f) 0 a) =
      mapπ₀ ((presentedPerfectDGBFMap A f).app 0).right
        (presentedPerfectDGBFZeroPiZeroEquiv A X a) := by
  have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
    (OmegaSpectrum.homotopyGroupEquivAt_natural (presentedPerfectDGBFMap A f) 0 0 (by decide) a)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map ((presentedPerfectDGBFMap A f).app 0).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint ((presentedPerfectDGBFMap A f).app 0))
    (OmegaSpectrum.homotopyGroupEquivAt (presentedPerfectDGBFOmegaSpectrum A X) 0 0 (by decide) a))

/-- 元の Perf 三角圏 K₀ と、同じ新 BF K 零空間の π₀ の自然比較の同値。 -/
def presentedPerfectDGBFKZeroPiZeroEquiv (X : PerfDGInput.{u, v} A) :
    TriangulatedK0
        (hoFunctor.obj (stableCategoryModel (presentedPerfectDGStableCategory A X)).carrier) ≃
      π₀ (((presentedPerfectDGBFOmegaSpectrum A X).level 0).space).right :=
  ((presentedPerfectDGBFKZeroEquiv A X).toEquiv.trans Additive.toMul).trans
    (presentedPerfectDGBFZeroPiZeroEquiv A X)

/-- π₀ K = K₀ の同じ同値は、元の通常 dg 入力射について自然。 -/
lemma presentedPerfectDGBFKZeroPiZeroEquiv_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
    (a : TriangulatedK0
      (hoFunctor.obj (stableCategoryModel (presentedPerfectDGStableCategory A X)).carrier)) :
    presentedPerfectDGBFKZeroPiZeroEquiv A Y
        (triangulatedKZeroSourceMap (presentedPerfectDGBFInputStableMap A f) a) =
      mapπ₀ ((presentedPerfectDGBFMap A f).app 0).right
        (presentedPerfectDGBFKZeroPiZeroEquiv A X a) := by
  have h := congrArg Additive.toMul (presentedPerfectDGBFKZeroEquiv_naturality A f a)
  exact (congrArg (presentedPerfectDGBFZeroPiZeroEquiv A Y) h).trans
    (presentedPerfectDGBFZeroPiZeroEquiv_naturality A f
      (presentedPerfectDGBFKZeroEquiv A X a).toMul)

end SerrePositivity.KST.SConstruction
