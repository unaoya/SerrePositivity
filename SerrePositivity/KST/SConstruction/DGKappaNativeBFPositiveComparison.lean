module
public import SerrePositivity.KST.SConstruction.DGKappaNativeCoherentBFSquare
public import SerrePositivity.KST.SConstruction.PointedEnrichedKanLift
public import SerrePositivity.KST.SConstruction.StrictSimplicialTransformationComponent
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedEquivalences
public import SerrePositivity.KST.Fibration.SpectrumSpaceEvaluation

/-!
概要：同じ native 全二胞体の元正段と実 BF 正段を指定同型で比較する。
方針：実再帰段の全 Hom 自然な前向き弱比較を Kan 全部分圏で反転する。
規約：頂点ごとの比較だけで代用しない。使われ方：K-B の同じ有限 BF 四角形。
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

local instance nativeBFPositiveTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 概要：同じ元境界商の有限入力上の点つき Kan 関手。
方針：元の豊穣包含と元境界商の Kan 関手を合成する。
規約：全 Hom を保持。使われ方：同じ前向き比較の始域。 -/
def dgKappaNativeBFFiniteBoundaryKanFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedKanObject.{max (u + 1) v} :=
  (dgKappaNativeBFFiniteInclusion.{u, v} R D I).comp SSet
    (stableSBoundaryKanEnrichedFunctor r)

/-- 概要：同じ BF 実段を Kan 全部分圏へ保持する。
方針：証明済みの各段 Kan 性だけを束ねる。
規約：同じ実段作用。使われ方：全スペクトル評価との照合。 -/
def dgKappaNativeBFFiniteLevelKanFunctor (n : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedKanObject.{max (u + 1) v} :=
  pointedEnrichedKanLift (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n)
    (dgKappaNativeBFFiniteLevel_kanComplex.{u, v} R D I n)

/-- 概要：同じ実段関手はスペクトルの全 Hom 評価に一致する。
方針：実写像塔の評価式を使う。
規約：全高次入力の等式。使われ方：全図式の正段比較。 -/
lemma dgKappaNativeBFFiniteLevelKanFunctor_eq_evaluation (n : ℕ) :
    (dgKappaNativeBFEnrichedFunctor.{u, v} R D I).comp SSet (spectrumKanEvaluation n) =
      dgKappaNativeBFFiniteLevelKanFunctor.{u, v} R D I n := by
  apply EnrichedFunctor.ext SSet
  case h_obj => intro C; rfl
  case h_map =>
    intro C E
    exact dgKappaNativeBFEnrichedFunctor_evaluation.{u, v} R D I C E n

/-- 概要：元正段から実 BF 正段への全 Hom 自然な指定変換。
方針：同じ帰納比較を Kan 全部分圏で束ねる。
規約：元の比較成分を保持。使われ方：全四角形の同型。 -/
def dgKappaNativeBFFinitePositiveTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (dgKappaNativeBFFiniteBoundaryKanFunctor.{u, v} R D I r)
      (dgKappaNativeBFFiniteLevelKanFunctor.{u, v} R D I (r + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _
    (fun C => ObjectProperty.homMk
      ((dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).comparison C))
    (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).naturality

/-- 概要：元正段と同じ実 BF 正段の全 coherent 図式同型。
方針：同じ全族変換と実比較の π 同型性を使う。
規約：別の成分を選ばない。使われ方：元二胞体の比較。 -/
def dgKappaNativeBFFinitePositiveFunctorIso (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
      (dgKappaNativeBFFiniteBoundaryKanFunctor.{u, v} R D I r))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgKappaNativeBFFiniteLevelKanFunctor.{u, v} R D I (r + 1))) :=
  StrictEnrichedTransformation.functorIso _ _
    (dgKappaNativeBFFinitePositiveTransformation.{u, v} R D I r) (by
      intro C
      have h := strictSimplicialTransformation_componentHom
        (dgKappaNativeBFFiniteBoundaryKanFunctor.{u, v} R D I r)
        (dgKappaNativeBFFiniteLevelKanFunctor.{u, v} R D I (r + 1))
        (dgKappaNativeBFFinitePositiveTransformation.{u, v} R D I r) C
        (ObjectProperty.homMk
          ((dgKappaNativeBFFinitePositiveStage.{u, v} R D I r).comparison C)) rfl
      rw [h]
      exact pointedKanObject_edge_isInvertible_of_piIsomorphism _
        (dgKappaNativeBFFiniteStageComparison_piIsomorphism.{u, v} R D I r
          (dgKappaNativeBFFinitePositiveStage.{u, v} R D I r) C))

end SerrePositivity.KST.SConstruction
