module
public import SerrePositivity.KST.SConstruction.DiagonalIterationRealization
public import SerrePositivity.KST.SConstruction.BoundaryReduction

/-! # 既存の反復実現を標的とする経路境界
概要：反復経路の境界を既存の多重実現、全零境界商、その Kan 模型へ接続する。
方針：座標の実際の同型に続けて既存の商写像と Kan 置換の単位を合成する。
規約：ここでの射は底の単体集合の射。使われ方：Ω 条件の homotopy fiber 比較の境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 概要：弱可縮な反復経路から既存の多重 core S の実現への境界射。
方針：元の境界射を、証明済みの全単体的な座標同型で移す。
規約：標的は既存の multiDiagonalCoreSConstruction。使われ方：既存の実現における fiber 比較。 -/
def canonicalIteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ multiDiagonalCoreSConstruction (r + 1) X :=
  iteratedPathRealizationBoundary r X ≫ (iteratedSRealizationCoordinateIso r X).hom

/-- 概要：反復経路から既存の全零境界商への境界射。
方針：既存の多重実現への境界に商写像を合成する。
規約：単体集合の射として構成する。使われ方：点つき実現の模型との比較。 -/
def reducedIteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ (boundaryReducedRealization r X).right :=
  canonicalIteratedPathBoundary r X ≫ boundaryReductionQuotient r X

/-- 概要：反復経路から既存の全零境界商の Kan 模型への境界射。
方針：商への境界を既存の点つき Kan 置換の単位と合成する。
規約：射自体の源の Kan 性は不要。使われ方：Kan な delooping 空間の homotopy fiber。 -/
def kanIteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ ((boundaryKanRealizationFunctor r).obj X).right :=
  reducedIteratedPathBoundary r X ≫
    (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right

end SerrePositivity.KST.SConstruction
