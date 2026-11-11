module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeKanInclusion
public import SerrePositivity.KST.SConstruction.PointedSOAExInfinityComparison
public import SerrePositivity.KST.Spectra.LoopHomotopyNaturality

/-!
概要：元の core S 実現と全零境界の一方向実現を同じ指定射で照合する。
方針：一重 S の元の全図式の一致と境界商への元の自然な射を使う。
規約：元の指定完全射と全次数を保持する。
使われ方：元の Kan 包含の次数条件を元の境界 K 空間へ移す。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories

open scoped Simplicial

/-- 概要：一重反復実現の元の射は元の core S 実現の射に一致する。
方針：零回反復と元の後合成の定義を計算する。
規約：元の同じ完全射の射の等号。
使われ方：境界商との元の可換正方形。 -/
lemma singleRealization_map_eq_coreS {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (multiRealizationFunctor 1).map f = coreSRealizationFunctor.map f := rfl

/-- 概要：元の core S 実現から境界商への元の射は完全射と可換。
方針：同じ一重実現を元の境界商の自然性へ代入する。
規約：Kan 置換や基点の選択の前の射の等号。
使われ方：Ex∞ と元の SOA Kan 置換の比較。 -/
lemma coreSBoundaryQuotient_naturality {X Y : StableModel.{u}} (f : X ⟶ Y) :
    coreSRealizationFunctor.map f ≫ boundaryReductionQuotient 0 Y =
      boundaryReductionQuotient 0 X ≫ ((boundaryReducedRealizationFunctor 0).map f).right :=
  (boundaryReductionNat 0).naturality f

end SerrePositivity.KST.SConstruction.Cofinality
