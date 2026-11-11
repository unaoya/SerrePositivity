module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFFirstStage
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderComponents
public import SerrePositivity.KST.SConstruction.PointedCylinderOmegaCriterion

/-!
概要：有限 native BF 再帰の最初の構造射・比較射と実 Ω 条件を証明する。
方針：同じ評価の円柱置換の単射性・anodyne 比較・基点固定成分を使う。
規約：元の零段 ΩB₀ を保つ。使われ方：同じ四辺の同時再帰の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories
open NonConnective Spectra SimplicialModel
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：有限入力の同じ元の B₀ は Kan 複体。
方針：同じ Ex∞ の Kan 性を使う。
規約：追加 instance 仮定なし。使われ方：最初の Ω 条件。 -/
instance dgKappaNativeBFFiniteBase_kanComplex (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj C).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 概要：同じ最初の実 BF 段は Kan 複体。
方針：同じ豊穣単射置換の Kan 性を使う。
規約：元の値を保持する。使われ方：最初の比較と次段の入力。 -/
instance dgKappaNativeBFFiniteFirst_kanComplex (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj C).obj).right :=
  pointedEnrichedMonicReplacement_kanComplex
    (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
    (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
    (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I) C

/-- 概要：元の同じ零段からの最初の実構造射。
方針：元の評価の単射置換の源射を使う。
規約：元の suspension を保持。使われ方：有限 BF 列の最初の構造射。 -/
def dgKappaNativeBFFiniteFirstStructureMap (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I).obj C ⟶
      (dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj C :=
  pointedEnrichedMonicReplacementSource
    (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
    (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
    (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I) C

/-- 概要：同じ B₀ から最初の実 BF 段への前向き比較。
方針：同じ円柱置換の標的包含を使う。
規約：元の比較を保持。使われ方：次段の比較データ。 -/
def dgKappaNativeBFFiniteFirstComparison (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj C ⟶
      (dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj C :=
  pointedEnrichedMonicReplacementTarget
    (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
    (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
    (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I) C

/-- 概要：同じ最初の構造射は基礎単体集合上で単射。
方針：既存の実単射置換の源射の単射性を使う。
規約：追加仮定なし。使われ方：有限 BF 再帰の構造条件。 -/
lemma dgKappaNativeBFFiniteFirstStructureMap_mono
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    Mono (show ((dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I).obj C).obj ⟶
      ((dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj C).obj from
        dgKappaNativeBFFiniteFirstStructureMap.{u, v} R D I C).right :=
  pointedEnrichedMonicReplacementSource_mono
    (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
    (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
    (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I) C

/-- 概要：同じ B₀ 比較は anodyne 射。
方針：実円柱置換の標的包含の性質を使う。
規約：元の比較を保つ。使われ方：元の正段への弱比較。 -/
lemma dgKappaNativeBFFiniteFirstComparison_anodyne
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    anodyneExtensions (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj C).obj ⟶
      ((dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj C).obj from
        dgKappaNativeBFFiniteFirstComparison.{u, v} R D I C).right :=
  pointedEnrichedMonicReplacementTarget_anodyne
    (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
    (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
    (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I) C

/-- 概要：同じ最初の比較は全基点 π 同型。
方針：Kan 値間の元の anodyne 比較を使う。
規約：全次数を保持。使われ方：最初の実 Ω 条件。 -/
lemma dgKappaNativeBFFiniteFirstComparison_piIsomorphism
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj C).obj ⟶
        ((dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj C).obj from
          dgKappaNativeBFFiniteFirstComparison.{u, v} R D I C).right :=
  kanPiIsomorphism_of_anodyne _ (dgKappaNativeBFFiniteFirstComparison_anodyne.{u, v} R D I C)

/-- 概要：同じ元の零段の Kan 性。
方針：同じ B₀ の loop の Kan 性を使う。
規約：元の零段を保持。使われ方：最初の構造随伴の型。 -/
lemma dgKappaNativeBFFiniteZero_kanComplex (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((dgKappaNativeBFFiniteZeroFunctor.{u, v} R D I).obj C).obj).right :=
  loopSpace_kanComplex _

end SerrePositivity.KST.SConstruction
