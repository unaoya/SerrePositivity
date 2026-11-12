module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFEnrichedFunctor
public import SerrePositivity.KST.Spectra.CoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-! # 厳密 dg BF K の γ1 による Sp 値 ∞ 関手
概要：全高次 Hom を保持する実 BF 豊穣関手の coherent nerve を取る。
方針：γ1 の coherentNerveMap をそのまま適用し、対象の頂点を照合する。
規約：元の dgK との比較と Morita の移送は別工程。使われ方：K-基盤の Sp 値入力。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 値域は元の BF スペクトルの同じ実単体的圏。 -/
local instance presentedPerfectDGBFInfinityTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 元の実 BF 厳密豊穣関手の γ1 による Sp 値 ∞ 関手。 -/
def presentedPerfectDGBFInfinityFunctor :
    perfDGInputInfinity.{u, v} A ⟶ Sp.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (presentedPerfectDGBFEnrichedFunctor A)

/-- 同じ ∞ 関手は、元の実 BF Ω スペクトルを対象の像に持つ。 -/
lemma presentedPerfectDGBFInfinityFunctor_vertex (X : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFInfinityFunctor A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (presentedPerfectDGBFOmegaSpectrum A X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (presentedPerfectDGBFEnrichedFunctor A) X

end SerrePositivity.KST.SConstruction
