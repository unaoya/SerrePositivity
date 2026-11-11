module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFMapWeakEquivalence
public import SerrePositivity.KST.SConstruction.ExInfinityPointedWeakEquivalence
public import SerrePositivity.KST.SConstruction.BoundaryRealizationInvariance

/-! # 元の実 Perf 反復実現から同じ新 BF 射の不変性へ
概要：元の正の反復実現が弱同値なら、同じ新 BF 射は全段・全整数 π 同型。
方針：元の全境界商射を同じ Ex∞ に移し、実 BF 段の前向き弱比較を使う。
規約：元の入力射と実 BF 射を保持する。使われ方：新 BF 関手の Morita 不変性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 元の同じラベル付き Perf 作用を、反復実現の安定入力射として保持する。 -/
def presentedPerfectDGBFInputStableMap {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) :
    stableCategoryModel (presentedPerfectDGStableCategory A X) ⟶
      stableCategoryModel (presentedPerfectDGStableCategory A Y) :=
  ⟨(presentedPerfectDGExactMap A f).hom,
    preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A f).hom⟩

/-- 元の正の反復実現の弱同値性は、同じ元の Ex∞ 境界射へ移る。 -/
lemma presentedPerfectDGBoundaryKanMap_piIsomorphism_of_realization
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (r : ℕ)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (presentedPerfectDGBFInputStableMap A f)))) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (presentedPerfectDGBoundaryKanMap A r f).hom.right :=
  exInfinityPointedKanMap_piIsomorphism_of_localized _
    (boundaryReducedRealizationMap_localized_isIso (presentedPerfectDGBFInputStableMap A f) r hf)

/-- 同じ実 BF 射は、元の全正反復実現の弱同値性から全段で全基点 π 同型。 -/
lemma presentedPerfectDGBFMap_levelwise_of_realization
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
    (hf : ∀ r, IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (presentedPerfectDGBFInputStableMap A f)))) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((presentedPerfectDGBFMap A f).app n).right :=
  presentedPerfectDGBFMap_levelwise_of_boundary A f
    (fun r => presentedPerfectDGBoundaryKanMap_piIsomorphism_of_realization A f r (hf r)) n

/-- 元の全正反復実現の弱同値性は、同じ新 BF 射の全整数 π 同型性を与える。 -/
lemma presentedPerfectDGBFMap_piIsomorphism_of_realization
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
    (hf : ∀ r, IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (presentedPerfectDGBFInputStableMap A f)))) :
    OmegaSpectrum.PiIsomorphism (presentedPerfectDGBFMap A f) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _
    (presentedPerfectDGBFMap_levelwise_of_realization A f hf)

end SerrePositivity.KST.SConstruction
