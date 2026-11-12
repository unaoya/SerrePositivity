module
public import SerrePositivity.KST.SConstruction.PointedSOAExInfinityComparison
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFOmegaSpectrum
public import SerrePositivity.KST.SConstruction.KOmegaSpectrum

/-! # 同じ有限 native 入力 上の元の SOA K 列と新 BF 列の全段比較
概要：同じ全境界商の旧 Kan 模型から、実再帰 BF 列への前向き弱比較を作る。
方針：元の SOA 単位の延長と、既存の全正段への前向き比較を合成する。
規約：構造射の整合性は別工程。使われ方：元の K とのスペクトル比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra DifferentialGraded NonConnective Fibration
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ実再帰段の Kan 性を、全段比較の型にも保持する。
方針：同じ元境界商と実再帰段の比較を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
local instance dgKappaNativeBFSOAComparisonLevel_kanComplex
    (n : ℕ) (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).obj C).obj).right :=
  dgKappaNativeBFFiniteLevel_kanComplex.{u, v} R D I n C

/-- 概要：同じ Ex∞ 境界値は元の Kan 複体。
方針：同じ元境界商と実再帰段の比較を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
local instance dgKappaNativeBFSOAComparisonBoundary_kanComplex
    (r : ℕ) (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 概要：同じ元の境界商の SOA Kan 値から、その Ex∞ Kan 値への比較。
方針：同じ元境界商と実再帰段の比較を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
def dgKappaNativeBFBoundarySOAComparison (r : ℕ) (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (boundaryKanRealizationFunctor r).obj
        (sInputModel C.obj) ⟶
      ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj :=
  pointedSOAExInfinityComparison ((stableBoundaryPointedEnrichedFunctor r).obj C.obj)

/-- 概要：元の SOA 境界 Kan 値から同じ Ex∞ への比較は全基点 π 同型。
方針：同じ元境界商と実再帰段の比較を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFBoundarySOAComparison_piIsomorphism
    (r : ℕ) (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (dgKappaNativeBFBoundarySOAComparison.{u, v} R D I r C).right :=
  pointedSOAExInfinityComparison_piIsomorphism _

/-- 概要：同じ有限 native 入力の元の K 候補列から実再帰 BF 列への全段の前向き比較。
方針：同じ元境界商と実再帰段の比較を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
def dgKappaNativeBFRawSOAComparison (C : DGKappaNativeBFFiniteInput.{u, v} R D I) : (n : ℕ) →
    ((kKanSequence (sInputModel C.obj)).level n).space ⟶
      ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C).level n).space
  | 0 => (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
      (dgKappaNativeBFBoundarySOAComparison.{u, v} R D I 0 C)
  | r + 1 => dgKappaNativeBFBoundarySOAComparison.{u, v} R D I r C ≫
      (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).comparison C

/-- 概要：同じ元の K 候補列からの全段比較は全基点 π 同型。
方針：同じ元境界商と実再帰段の比較を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFRawSOAComparison_piIsomorphism
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (dgKappaNativeBFRawSOAComparison.{u, v} R D I C n).right := by
  cases n with
  | zero => exact pointedSOAExInfinityComparison_loop_piIsomorphism _
  | succ r =>
      let : KanComplex
          (((dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).functor.obj C).obj).right :=
        (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).kan C
      have hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
          (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj ⟶
            (((dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).functor).obj C).obj from
              (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).comparison C).right :=
        kanPiIsomorphism_of_localized_isIso _
          ((dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).weak C)
      exact (dgKappaNativeBFBoundarySOAComparison_piIsomorphism.{u, v} R D I r C).comp hp

/-- 概要：同じ有限 native 入力の元の実単射 BF K スペクトルから新 BF 列への全段比較。
方針：同じ元境界商と実再帰段の比較を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
def dgKappaNativeBFSOAComparison (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (n : ℕ) :
    ((kOmegaSpectrum (sInputModel C.obj)).level n).space ⟶
      ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C).level n).space :=
  (monicKKanSequenceProjection
    (sInputModel C.obj)).app n ≫
      dgKappaNativeBFRawSOAComparison.{u, v} R D I C n

/-- 概要：元の実単射 BF K スペクトルからの同じ全段比較は全基点 π 同型。
方針：同じ元境界商と実再帰段の比較を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFSOAComparison_piIsomorphism
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (dgKappaNativeBFSOAComparison.{u, v} R D I C n).right :=
  (monicKKanSequenceProjection_piIsomorphism
    (sInputModel C.obj) n).comp
    (dgKappaNativeBFRawSOAComparison_piIsomorphism.{u, v} R D I C n)

/-- 概要：元の実 BF 零段の比較は、同じ境界商の二 Kan 模型の loop 比較そのもの。
方針：同じ元境界商と実再帰段の比較を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFSOAComparison_zero (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    dgKappaNativeBFSOAComparison.{u, v} R D I C 0 =
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
        (dgKappaNativeBFBoundarySOAComparison.{u, v} R D I 0 C) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

end SerrePositivity.KST.SConstruction
