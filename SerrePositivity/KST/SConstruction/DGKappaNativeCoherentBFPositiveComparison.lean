module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFPositiveComparison

/-!
概要：同じ実 BF 四角形の全正段を元の未完備 native 全四角形と比較する。
方針：有限入力の全図式同型を元二胞体へ前合成し、基点忘却する。
規約：元の二単体を同じ図式内に保持。使われ方：K-B の有限 Φ の正段指定比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra
open Fibration
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

local instance nativeCoherentBFPositiveTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 概要：同じ有限入力上の元正段の全図式は元 native 全図式を回収する。
方針：豊穣合成の nerve と元の充満制限の包含式を使う。
規約：全二胞体の等式。使われ方：実正段同型の元図式への照合。 -/
lemma dgKappaNativeBFFiniteBoundarySquare_eq (r : ℕ) :
    dgKappaNativeBFFiniteSquare.{u, v} R D I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
      (dgKappaNativeBFFiniteBoundaryKanFunctor.{u, v} R D I r) =
        dgKappaNativeBFPointedStageSquare.{u, v} R D I r := by
  unfold dgKappaNativeBFFiniteBoundaryKanFunctor
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, ← Category.assoc, dgKappaNativeBFFiniteSquare_inclusion]
  rfl

/-- 概要：実 BF 全四角形の評価は同じ実段の全四角形。
方針：元の全 Hom 評価式を同じ二胞体へ適用する。
規約：新しい充填を選ばない。使われ方：全正段の指定比較。 -/
lemma dgKappaNativeCoherentBFSquare_pointedEvaluation (n : ℕ) :
    dgKappaNativeCoherentBFSquare.{u, v} R D I ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n) =
      dgKappaNativeBFFiniteSquare.{u, v} R D I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
        (dgKappaNativeBFFiniteLevelKanFunctor.{u, v} R D I n) := by
  exact (Category.assoc (dgKappaNativeBFFiniteSquare.{u, v} R D I)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgKappaNativeBFEnrichedFunctor.{u, v} R D I))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n))).trans
      (congrArg (fun f => dgKappaNativeBFFiniteSquare.{u, v} R D I ≫ f)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp (dgKappaNativeBFEnrichedFunctor.{u, v} R D I)
          (spectrumKanEvaluation n)).symm.trans
          (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
            (dgKappaNativeBFFiniteLevelKanFunctor_eq_evaluation.{u, v} R D I n))))

/-- 概要：元正段の全二胞体と実 BF 全二胞体の指定点つき比較。
方針：同じ有限入力の全族同型を元の四角形へ制限する。
規約：元の全二単体を保持。使われ方：基点忘却前の群比較。 -/
def dgKappaNativeCoherentBFPointedPositiveComparison (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaNativeBFPointedStageSquare.{u, v} R D I r)
      (dgKappaNativeCoherentBFSquare.{u, v} R D I ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1))) := by
  have h := dgKappaNativeCoherentBFSquare_pointedEvaluation.{u, v} R D I (r + 1)
  have hb := dgKappaNativeBFFiniteBoundarySquare_eq.{u, v} R D I r
  exact h.symm ▸ hb ▸ (dgKappaNativeBFFinitePositiveFunctorIso.{u, v} R D I r).precomp
    (dgKappaNativeBFFiniteSquare.{u, v} R D I)

/-- 概要：実 Φ の全正段は元未完備 native 全四角形の S• 正段と指定同型。
方針：同じ点つき全図式比較を反転し、基点忘却する。
規約：辺の成分比較で代用しない。使われ方：K-B へ供給する全正段比較。 -/
def dgKappaNativeCoherentBFPositiveComparison (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaNativeCoherentBFSquare.{u, v} R D I ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation (r + 1)))
      (dgKappaNativeBFStageSquare.{u, v} R D I r) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
    (dgKappaNativeCoherentBFPointedPositiveComparison.{u, v} R D I r).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanForgetEnriched)
  have he : (dgKappaNativeCoherentBFSquare.{u, v} R D I ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanForgetEnriched =
      dgKappaNativeCoherentBFSquare.{u, v} R D I ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation (r + 1)) :=
    (Category.assoc (dgKappaNativeCoherentBFSquare.{u, v} R D I)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation (r + 1)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanForgetEnriched)).trans
      (congrArg (fun f => dgKappaNativeCoherentBFSquare.{u, v} R D I ≫ f)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp (spectrumKanEvaluation (r + 1))
          pointedKanForgetEnriched).symm)
  exact he ▸ (dgKappaNativeBFPointedStageSquare_forget.{u, v} R D I r) ▸ h

end SerrePositivity.KST.SConstruction
