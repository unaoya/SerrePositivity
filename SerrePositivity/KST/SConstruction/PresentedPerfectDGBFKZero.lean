module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAIntegerNaturality
public import SerrePositivity.KST.SConstruction.TriangulatedKZeroEquiv
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # 同じ新 BF K の零次群と元の Perf 三角圏 K₀ の自然比較
概要：実厳密豊穣 BF K の零次群は、同じ小さい Perf 模型の三角圏 K₀ と自然同型。
方針：元の三角圏比較と、同じ実 SOA→新 BF 比較射の自然な整数群同型を合成する。
規約：元の入力射と比較射の作用を保持する。使われ方：L1e の新 Sp 値関手への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ新 BF K の零次群と元のラベル付き Perf 三角圏 K₀ の加法群同型。 -/
def presentedPerfectDGBFKZeroEquiv (X : PerfDGInput.{u, v} A) :
    TriangulatedK0
        (hoFunctor.obj (stableCategoryModel (presentedPerfectDGStableCategory A X)).carrier) ≃+
      Additive (OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) 0) :=
  (triangulatedKZeroEquiv (stableCategoryModel (presentedPerfectDGStableCategory A X))).trans
    (MulEquiv.toAdditive (presentedPerfectDGBFSOAGroupEquiv A X 0))

/-- 同じ零次比較は、元の通常 dg 入力射に対して厳密に自然。 -/
lemma presentedPerfectDGBFKZeroEquiv_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
    (a : TriangulatedK0
      (hoFunctor.obj (stableCategoryModel (presentedPerfectDGStableCategory A X)).carrier)) :
    presentedPerfectDGBFKZeroEquiv A Y
        (triangulatedKZeroSourceMap (presentedPerfectDGBFInputStableMap A f) a) =
      (OmegaSpectrum.homotopyMap (presentedPerfectDGBFMap A f) 0).toAdditive
        (presentedPerfectDGBFKZeroEquiv A X a) := by
  change Additive.ofMul (presentedPerfectDGBFSOAGroupEquiv A Y 0
    (triangulatedKZeroEquiv (stableCategoryModel (presentedPerfectDGStableCategory A Y))
      (triangulatedKZeroSourceMap (presentedPerfectDGBFInputStableMap A f) a)).toMul) = _
  rw [triangulatedKZeroEquiv_naturality]
  exact congrArg Additive.ofMul (presentedPerfectDGBFSOAGroupEquiv_naturality A f 0
    (triangulatedKZeroEquiv (stableCategoryModel (presentedPerfectDGStableCategory A X)) a).toMul)

/-- 同じ零次比較は、元の対象類の SOA 比較による像を回収する。 -/
lemma presentedPerfectDGBFKZeroEquiv_vertex (X : PerfDGInput.{u, v} A)
    (x : (stableCategoryModel (presentedPerfectDGStableCategory A X)).carrier.obj
      (Opposite.op (SimplexCategory.mk 0))) :
    presentedPerfectDGBFKZeroEquiv A X (TriangulatedK0.mk (SSet.HomotopyCategory.mk x)) =
      Additive.ofMul (presentedPerfectDGBFSOAGroupEquiv A X 0
        (objectKClass (stableCategoryModel (presentedPerfectDGStableCategory A X)) x).toMul) := by
  change Additive.ofMul (presentedPerfectDGBFSOAGroupEquiv A X 0
    (triangulatedKZeroEquiv (stableCategoryModel (presentedPerfectDGStableCategory A X))
      (TriangulatedK0.mk (SSet.HomotopyCategory.mk x))).toMul) = _
  rw [triangulatedKZeroEquiv_vertex]

end SerrePositivity.KST.SConstruction
