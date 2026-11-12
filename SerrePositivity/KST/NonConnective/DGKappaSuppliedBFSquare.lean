module
public import SerrePositivity.KST.SConstruction.DGKappaNativeCoherentBFPositiveComparison
public import SerrePositivity.KST.SConstruction.DGKappaNativeCoherentBFArrowComparison

/-!
概要：K-S•-S3 の実四角形・全正段比較・指定整数群同型との可換性を直接消費する。
方針：新 BF 四対象を保持し、元の全 S• 比較と旧 K-cof の群作用へ接続する。
規約：旧 BF 四対象との厳密等式や実 Sp 同型をここから推論しない。
使われ方：供給済み有限 BF 四角形を K-6・K-7 の実比較へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance suppliedBFCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：供給済み実 BF 四角形の同じ全正段を元の全 S• 図式へ戻す。
方針：元の境界商比較と K-S•-S3 の同じ全四角形比較を合成する。
規約：辺や対象だけの比較で代用せず、hBF の存在仮定を取らない。
使われ方：未完備 fibration から実 BF 正段の引き戻しへの接続。 -/
def dgKappaSuppliedBFMultiSquareIso (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} r))
      (dgKappaNativeCoherentBFSquare R D I ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))) :=
  (stableBoundaryQuotientKanIso r).precomp (dgKappaNativeVerdierDiagram R D I).square ≪≫
    (dgKappaNativeCoherentBFPositiveComparison R D I r).symm

/-- 概要：同じ未完備全 S• 比較に条件付きで、実供給 BF 正段は引き戻し。
方針：供給された全図式同型へ同じ引き戻し性を移す。
規約：旧 BF 辺への変更や固定連結 K の Sp 引き戻し性は主張しない。
使われ方：実 fiber 比較の同じ第一正段への受け渡し。 -/
theorem dgKappaSuppliedBF_spaceEvaluation_isPullback (r : ℕ)
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((dgKappaNativeVerdierDiagram R D I).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} r))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (dgKappaNativeCoherentBFSquare R D I ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation.{max (u + 1) v} (r + 1))) :=
  hS.of_functorIso (dgKappaSuppliedBFMultiSquareIso R D I r)

/-- 概要：実供給 BF 四辺の π 全単射性は旧 K 射の同じ性質と同値。
方針：指定始域・終域群同型と実供給の全整数可換式で同じ合成を消去する。
規約：異なる BF 対象の群を等号で同一視しない。
使われ方：旧 K-cof の正次数全単射を実 coherent 辺へ移す。 -/
theorem dgKappaSuppliedBFArrow_bijective_iff (e : Fin 4) (j : ℤ) :
    Function.Bijective
      (OmegaSpectrum.homotopyMap (dgKappaNativeCoherentBFArrow R D I e).hom j) ↔
    Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap (sInputExactMap
      (dgKappaNativeBFFiniteNativeArrow R D I e).hom.hom)) j) := by
  let a := dgKappaNativeCoherentBFArrowSourceIntegerEquiv R D I e j
  let b := dgKappaNativeCoherentBFArrowTargetIntegerEquiv R D I e j
  have h : (fun x => OmegaSpectrum.homotopyMap
      (dgKappaNativeCoherentBFArrow R D I e).hom j (a x)) =
      (fun x => b (OmegaSpectrum.homotopyMap (kSpectrumMap (sInputExactMap
        (dgKappaNativeBFFiniteNativeArrow R D I e).hom.hom)) j x)) := by
    funext x
    exact DFunLike.congr_fun (dgKappaNativeCoherentBFArrow_homotopyMap_eq R D I e j) x
  exact (Function.Bijective.of_comp_iff _ a.bijective).symm.trans
    ((iff_of_eq (congrArg Function.Bijective h)).trans
      (Function.Bijective.of_comp_iff' b.bijective _))

/-- 概要：実供給 BF 四辺の π 単射性は旧 K 射の同じ性質と同値。
方針：同じ指定整数群同型と可換式を使う。
規約：零次も含むが全射性を新たに要求しない。
使われ方：旧 K-cof の零次単射を実 coherent 辺へ移す。 -/
theorem dgKappaSuppliedBFArrow_injective_iff (e : Fin 4) (j : ℤ) :
    Function.Injective
      (OmegaSpectrum.homotopyMap (dgKappaNativeCoherentBFArrow R D I e).hom j) ↔
    Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap (sInputExactMap
      (dgKappaNativeBFFiniteNativeArrow R D I e).hom.hom)) j) := by
  let a := dgKappaNativeCoherentBFArrowSourceIntegerEquiv R D I e j
  let b := dgKappaNativeCoherentBFArrowTargetIntegerEquiv R D I e j
  have h : (fun x => OmegaSpectrum.homotopyMap
      (dgKappaNativeCoherentBFArrow R D I e).hom j (a x)) =
      (fun x => b (OmegaSpectrum.homotopyMap (kSpectrumMap (sInputExactMap
        (dgKappaNativeBFFiniteNativeArrow R D I e).hom.hom)) j x)) := by
    funext x
    exact DFunLike.congr_fun (dgKappaNativeCoherentBFArrow_homotopyMap_eq R D I e j) x
  exact (Function.Injective.of_comp_iff' _ a.bijective).symm.trans
    ((iff_of_eq (congrArg Function.Injective h)).trans
      (Function.Injective.of_comp_iff b.injective _))

/-- 概要：同じ実四辺へ旧 K-cof の正次数全単射・零次単射を移す。
方針：元の完全射の完備化認証へ共終性を適用し、指定群同型で実供給辺へ戻す。
規約：完備化認証と共終性に条件付きで、実商射の完備化性は主張しない。
使われ方：新 coherent BF 四辺と旧 K-cof の直接の接続。 -/
theorem dgKappaSuppliedBFArrow_cofinal
    (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
        (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
          Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
    (e : Fin 4)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion
      (sInputExactMap (dgKappaNativeBFFiniteNativeArrow R D I e).hom.hom).val) :
    (∀ j : ℤ, 0 < j → Function.Bijective
      (OmegaSpectrum.homotopyMap (dgKappaNativeCoherentBFArrow R D I e).hom j)) ∧
      Function.Injective
        (OmegaSpectrum.homotopyMap (dgKappaNativeCoherentBFArrow R D I e).hom 0) := by
  have h := hcofinal _ _ _ hf
  exact ⟨fun j hj => (dgKappaSuppliedBFArrow_bijective_iff R D I e j).mpr (h.1 j hj),
    (dgKappaSuppliedBFArrow_injective_iff R D I e 0).mpr h.2⟩

end SerrePositivity.KST.NonConnective
