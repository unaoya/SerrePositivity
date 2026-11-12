module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMoritaAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFRealizationInvariance

/-! # 同じ新 BF 厳密豊穣 K 射の Morita 不変性
概要：元の主 Perf 作用が同値なら、同じ新 BF 射は全段・全整数 π 同型。
方針：元のラベル付き Perf 作用を順方向に保つ完全同値から、全正反復実現へ移す。
規約：同じ元の実 BF 射を結論する。使われ方：厳密豊穣 K の Morita 不変性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A] {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
  [(quasiEquivalencePerfectExtension A X Y f.down).IsEquivalence]

/-- 元の同じラベル付き Perf 作用を順方向に保持する Morita の完全同値。 -/
def presentedPerfectDGBFMoritaStableEquivalence :
    StableModelEquivalence
      (stableCategoryModel (presentedPerfectDGStableCategory A X))
      (stableCategoryModel (presentedPerfectDGStableCategory A Y)) := by
  let e := (presentedPerfectDGMoritaAction_isQCatEquivalence A X Y f.down).choose
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact ⟨presentedPerfectDGBFInputStableMap A f,
    ⟨e.inv, preservesCofiberData_of_isExactFunctor e.inv⟩, e.homInvIso, e.invHomIso⟩

/-- Morita の完全同値は、元の同じ実 Perf 入力射を保持する。 -/
lemma presentedPerfectDGBFMoritaStableEquivalence_hom :
    (presentedPerfectDGBFMoritaStableEquivalence A f).hom =
      presentedPerfectDGBFInputStableMap A f := rfl

/-- 元の Morita 同値は、同じ元の全正有限反復実現射を局所化同型へ送る。 -/
lemma presentedPerfectDGBFMoritaRealization_localized_isIso (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (presentedPerfectDGBFInputStableMap A f))) :=
  multiRealization_map_localized_isIso_of_equivalence r
    (presentedPerfectDGBFMoritaStableEquivalence A f)

/-- 同じ新 BF Morita 射は零段を含む全段で全基点 π 同型。 -/
lemma presentedPerfectDGBFMap_morita_levelwise (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((presentedPerfectDGBFMap A f).app n).right :=
  presentedPerfectDGBFMap_levelwise_of_realization A f
    (presentedPerfectDGBFMoritaRealization_localized_isIso A f) n

/-- 同じ元の新 BF Morita 射は全整数次数で π 同型。 -/
lemma presentedPerfectDGBFMap_morita_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (presentedPerfectDGBFMap A f) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _ (presentedPerfectDGBFMap_morita_levelwise A f)

/-- 新 BF K 群の Morita 同型は、同じ元の実 BF 射の作用を使う。 -/
def presentedPerfectDGBFMoritaGroupEquiv (j : ℤ) :
    OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) j ≃*
      OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A Y) j :=
  (presentedPerfectDGBFMap_morita_piIsomorphism A f).groupEquiv j

/-- 新 BF Morita 群同型の順方向は、元の同じ実 BF 射の作用そのもの。 -/
lemma presentedPerfectDGBFMoritaGroupEquiv_apply (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) j) :
    presentedPerfectDGBFMoritaGroupEquiv A f j a =
      OmegaSpectrum.homotopyMap (presentedPerfectDGBFMap A f) j a := rfl

end SerrePositivity.KST.SConstruction
