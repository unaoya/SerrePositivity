module
public import SerrePositivity.KST.SConstruction.PointedSOAExInfinityComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFOmegaSpectrum
public import SerrePositivity.KST.SConstruction.KOmegaSpectrum

/-! # 同じ Perf 上の元の SOA K 列と新 BF 列の全段比較
概要：同じ全境界商の旧 Kan 模型から、実再帰 BF 列への前向き弱比較を作る。
方針：元の SOA 単位の延長と、既存の全正段への前向き比較を合成する。
規約：構造射の整合性は別工程。使われ方：元の dgK とのスペクトル比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 同じ実再帰段の Kan 性を、全段比較の型にも保持する。 -/
local instance presentedPerfectDGBFSOAComparisonLevel_kanComplex
    (n : ℕ) (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGBFLevelFunctor A n).obj C).obj).right :=
  presentedPerfectDGBFLevel_kanComplex A n C

/-- 同じ Ex∞ 境界値は元の Kan 複体。 -/
local instance presentedPerfectDGBFSOAComparisonBoundary_kanComplex
    (r : ℕ) (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGBFBoundaryFunctor A r).obj C).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 同じ元の境界商の SOA Kan 値から、その Ex∞ Kan 値への比較。 -/
def presentedPerfectDGBFBoundarySOAComparison (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (boundaryKanRealizationFunctor r).obj
        (stableCategoryModel (presentedPerfectDGStableCategory A C)) ⟶
      ((presentedPerfectDGBFBoundaryFunctor A r).obj C).obj :=
  pointedSOAExInfinityComparison ((presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj C)

/-- 元の SOA 境界 Kan 値から同じ Ex∞ への比較は全基点 π 同型。 -/
lemma presentedPerfectDGBFBoundarySOAComparison_piIsomorphism
    (r : ℕ) (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (presentedPerfectDGBFBoundarySOAComparison A r C).right :=
  pointedSOAExInfinityComparison_piIsomorphism _

/-- 同じ Perf の元の K 候補列から実再帰 BF 列への全段の前向き比較。 -/
def presentedPerfectDGBFRawSOAComparison (C : PerfDGInput.{u, v} A) : (n : ℕ) →
    ((kKanSequence (stableCategoryModel (presentedPerfectDGStableCategory A C))).level n).space ⟶
      ((presentedPerfectDGBFOmegaSpectrum A C).level n).space
  | 0 => (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
      (presentedPerfectDGBFBoundarySOAComparison A 0 C)
  | r + 1 => presentedPerfectDGBFBoundarySOAComparison A r C ≫
      (presentedPerfectDGBFPositiveStage A r).comparison C

/-- 同じ元の K 候補列からの全段比較は全基点 π 同型。 -/
lemma presentedPerfectDGBFRawSOAComparison_piIsomorphism
    (C : PerfDGInput.{u, v} A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (presentedPerfectDGBFRawSOAComparison A C n).right := by
  cases n with
  | zero => exact pointedSOAExInfinityComparison_loop_piIsomorphism _
  | succ r =>
      let : KanComplex (((presentedPerfectDGBFPositiveStage A r).functor.obj C).obj).right :=
        (presentedPerfectDGBFPositiveStage A r).kan C
      have hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
          (show ((presentedPerfectDGBFBoundaryFunctor A r).obj C).obj ⟶
            (((presentedPerfectDGBFPositiveStage A r).functor).obj C).obj from
              (presentedPerfectDGBFPositiveStage A r).comparison C).right :=
        kanPiIsomorphism_of_localized_isIso _ ((presentedPerfectDGBFPositiveStage A r).weak C)
      exact (presentedPerfectDGBFBoundarySOAComparison_piIsomorphism A r C).comp hp

/-- 同じ Perf の元の実単射 BF K スペクトルから新 BF 列への全段比較。 -/
def presentedPerfectDGBFSOAComparison (C : PerfDGInput.{u, v} A) (n : ℕ) :
    ((kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A C))).level n).space ⟶
      ((presentedPerfectDGBFOmegaSpectrum A C).level n).space :=
  (monicKKanSequenceProjection
    (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n ≫
      presentedPerfectDGBFRawSOAComparison A C n

/-- 元の実単射 BF K スペクトルからの同じ全段比較は全基点 π 同型。 -/
lemma presentedPerfectDGBFSOAComparison_piIsomorphism
    (C : PerfDGInput.{u, v} A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (presentedPerfectDGBFSOAComparison A C n).right :=
  (monicKKanSequenceProjection_piIsomorphism
    (stableCategoryModel (presentedPerfectDGStableCategory A C)) n).comp
    (presentedPerfectDGBFRawSOAComparison_piIsomorphism A C n)

/-- 元の実 BF 零段の比較は、同じ境界商の二 Kan 模型の loop 比較そのもの。 -/
lemma presentedPerfectDGBFSOAComparison_zero (C : PerfDGInput.{u, v} A) :
    presentedPerfectDGBFSOAComparison A C 0 =
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
        (presentedPerfectDGBFBoundarySOAComparison A 0 C) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

end SerrePositivity.KST.SConstruction
