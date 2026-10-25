module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFFiniteInput
public import SerrePositivity.KST.SConstruction.PointedStandardLoopEvaluation
public import SerrePositivity.KST.SConstruction.PointedEnrichedMonicReplacementProperties
public import SerrePositivity.KST.SConstruction.PointedEnrichedMonicReplacementTransformations

/-!
概要：同じ未完備 native 一四角形の有限入力上で、元の零段と最初の BF 段を作る。
方針：同じ境界商 B₀ の評価 ΣΩB₀→B₀ に既存の豊穣単射置換を適用する。
規約：一般安定圏の BF 関手を構成しない。使われ方：新四辺の同時再帰の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
open LocalizingInvariants NonConnective Spectra Fibration
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ有限入力の元の境界商を Ex∞ に送る点つき全段関手。
方針：有限豊穣包含に元の境界商と同じ Kan 置換を後合成する。
規約：全 Hom を保持。使われ方：有限 BF 再帰の元の正段。 -/
def dgKappaNativeBFFiniteBoundaryFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedSSetObject.{max (u + 1) v} :=
  (dgKappaNativeBFFiniteInclusion.{u, v} R D I).comp SSet
    ((stableBoundaryPointedEnrichedFunctor r).comp SSet exInfinityPointedEnrichedFunctor)

/-- 概要：同じ元の B₀ の loop を零段とする。
方針：同じ標準点つき loop 関手を合成する。
規約：B₀ 自体を零段にしない。使われ方：有限 BF 再帰の零段。 -/
def dgKappaNativeBFFiniteZeroFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedSSetObject.{max (u + 1) v} :=
  (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).comp SSet
    pointedStandardLoopEnrichedFunctor

/-- 概要：同じ元の零段の suspension ΣΩB₀。
方針：標準 suspension-loop 関手を同じ B₀ に合成する。
規約：同じ元の円を使う。使われ方：最初の構造射の始域。 -/
def dgKappaNativeBFFiniteZeroSuspensionFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedSSetObject.{max (u + 1) v} :=
  (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).comp SSet
    pointedStandardSuspensionLoopFunctor

/-- 概要：同じ B₀ 上の元の評価 ΣΩB₀→B₀。
方針：標準点つき loop 評価を有限入力の各値で使う。
規約：元の評価を保持。使われ方：最初の単射置換への入力。 -/
def dgKappaNativeBFFiniteZeroEvaluation (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I).obj C ⟶
      (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj C :=
  pointedStandardLoopEvaluation ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj C)

/-- 概要：同じ零段評価は有限入力の全 Hom に厳密に自然。
方針：標準評価の全 Hom 自然性を同じ境界商作用で前合成する。
規約：全高次パラメータを保持。使われ方：四辺の同時単射置換。 -/
lemma dgKappaNativeBFFiniteZeroEvaluation_whisker
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I).map C E ≫
        eHomWhiskerLeft SSet
          ((dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I).obj C)
          (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I E) =
      (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).map C E ≫
        eHomWhiskerRight SSet (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I C)
          ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj E) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun q => (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).map C E ≫ q)
      (pointedStandardLoopEvaluation_whisker
        ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj C)
        ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj E)))

/-- 概要：同じ有限入力上の最初の実 Kan BF 段。
方針：元の評価に一般の厳密豊穣単射置換を適用する。
規約：元の全 Hom と四角形を保つ。使われ方：次の正段再帰の基底。 -/
def dgKappaNativeBFFiniteFirstFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedSSetObject.{max (u + 1) v} :=
  pointedEnrichedMonicReplacementFunctor
    (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
    (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
    (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I)

end SerrePositivity.KST.SConstruction
