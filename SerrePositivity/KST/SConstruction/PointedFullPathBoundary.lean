module
public import SerrePositivity.KST.SConstruction.InnerZeroBoundaryNaturality
public import SerrePositivity.KST.SConstruction.CanonicalIteratedPathBoundary

/-! # 既存の全零境界商を標的とする点つき反復経路境界
概要：可縮な点つき反復経路から既存の全零境界商とその Kan 模型へ実際の境界射を作る。
方針：内側の零列の商の境界に全零境界商への比較を合成する。
規約：商射影に戻すと既存の境界射そのものを得る。使われ方：homotopy fiber と loop の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 概要：点つき反復経路から全零境界商への自然な境界。
方針：内側の零列の商への自然な境界と比較の自然変換を合成する。
規約：入力の全ての射について厳密に自然。使われ方：既存の標的の境界図式。 -/
def pointedFullIteratedPathBoundaryNat (r : ℕ) :
    pointedIteratedPathFunctor.{u} r ⟶ boundaryReducedRealizationFunctor r :=
  pointedIteratedPathBoundaryNat r ≫ innerZeroToFullBoundaryComparisonNat r

/-- 概要：点つき反復経路から既存の全零境界商への境界射。
方針：内側の零列の商を標的とする境界に比較写像を合成する。
規約：基点を厳密に保存。使われ方：既存の実現の loop との比較。 -/
def pointedFullIteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    pointedIteratedPathRealization r X ⟶ boundaryReducedRealization r X :=
  pointedIteratedPathBoundary r X ≫ innerZeroToFullBoundaryComparison r X

/-- 概要：全零境界商への点つき境界は既存の底の境界射を厳密に回収する。
方針：二つの商写像の回収式を合成する。
規約：点つき化により元の射は変わらない。使われ方：既存の境界との照合。 -/
lemma pointedFullIteratedPathBoundary_quotient (r : ℕ) (X : StableModel.{u}) :
    pointedIteratedPathQuotient r X ≫ (pointedFullIteratedPathBoundary r X).right =
      reducedIteratedPathBoundary r X := by
  change pointedIteratedPathQuotient r X ≫ (pointedIteratedPathBoundary r X).right ≫
    (innerZeroToFullBoundaryComparison r X).right = _
  rw [← Category.assoc, pointedIteratedPathBoundary_quotient, Category.assoc,
    innerZeroToFullBoundaryComparison_quotient]
  rfl

/-- 概要：点つき反復経路の全零境界への自然な境界の Kan 置換。
方針：自然な境界を点つき Kan 置換で写す。
規約：源は既存の可縮 Kan な反復経路。使われ方：自然な Kan 境界図式。 -/
def pointedFullIteratedPathKanBoundaryNat (r : ℕ) :
    pointedIteratedPathKanFunctor.{u} r ⟶ boundaryKanRealizationFunctor r :=
  Functor.whiskerRight (pointedFullIteratedPathBoundaryNat r) Spectra.PointedKanReplacement.functor

/-- 概要：可縮 Kan な点つき反復経路から既存の Kan な反復実現への境界射。
方針：全零境界商への点つき境界を既存の点つき Kan 置換で写す。
規約：源の可縮 Kan 性は既証明。使われ方：homotopy fiber の全空間。 -/
def pointedFullIteratedPathKanBoundary (r : ℕ) (X : StableModel.{u}) :
    (pointedIteratedPathKanFunctor r).obj X ⟶ (boundaryKanRealizationFunctor r).obj X :=
  Spectra.PointedKanReplacement.map (pointedFullIteratedPathBoundary r X)

/-- 概要：Kan な点つき境界も元の Kan 標的への境界射を厳密に回収する。
方針：Kan 置換の単位の自然性と商射影の回収式を使う。
規約：元の経路からの比較は商射影と Kan 置換の単位の合成。使われ方：既存模型との照合。 -/
lemma pointedFullIteratedPathKanBoundary_quotient (r : ℕ) (X : StableModel.{u}) :
    pointedIteratedPathQuotient r X ≫
      (Spectra.PointedKanReplacement.unit.app (pointedIteratedPathRealization r X)).right ≫
      (pointedFullIteratedPathKanBoundary r X).right = kanIteratedPathBoundary r X := by
  have hn := congrArg (fun f => f.right)
    (Spectra.PointedKanReplacement.unit.naturality (pointedFullIteratedPathBoundary r X))
  calc
    _ = pointedIteratedPathQuotient r X ≫
        (pointedFullIteratedPathBoundary r X).right ≫
        (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right := by
      exact congrArg (fun f => pointedIteratedPathQuotient r X ≫ f) hn.symm
    _ = reducedIteratedPathBoundary r X ≫
        (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right := by
      rw [← Category.assoc, pointedFullIteratedPathBoundary_quotient]
    _ = _ := rfl

end SerrePositivity.KST.SConstruction
