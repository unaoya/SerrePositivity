module
public import SerrePositivity.KST.SConstruction.PointedFullPathBoundary

/-! # 元の反復境界から既存の点つき Kan 境界への比較
概要：元の経路・標的の実現から既存の点つき Kan 模型への比較を、可換な局所化同型として構成する。
方針：経路商射影・反復座標同型・全零境界商・Kan 単位の既存の式を合成する。
規約：底の単体集合の実際の射。使われ方：零行の homotopy fiber 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 元の反復経路から既存の点つき Kan 経路模型への比較。 -/
def iteratedPathToKan (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ ((pointedIteratedPathKanFunctor r).obj X).right :=
  pointedIteratedPathQuotient r X ≫
    (Spectra.PointedKanReplacement.unit.app (pointedIteratedPathRealization r X)).right

/-- 元の反復標的から既存の全零境界商の Kan 模型への比較。 -/
def iteratedRealizationToKan (r : ℕ) (X : StableModel.{u}) :
    iteratedSRealization r X ⟶ ((boundaryKanRealizationFunctor r).obj X).right :=
  (iteratedSRealizationCoordinateIso r X).hom ≫ boundaryReductionQuotient r X ≫
    (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right

/-- 経路の Kan 比較は局所化同型。 -/
lemma iteratedPathToKan_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (iteratedPathToKan r X)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hq := pointedIteratedPathQuotient_image_isIso Q
    (Localization.inverts Q anodyneExtensions) r X
  have hu : IsIso (Q.map
      (Spectra.PointedKanReplacement.unit.app (pointedIteratedPathRealization r X)).right) :=
    (Localization.inverts Q anodyneExtensions) _ (Spectra.PointedKanReplacement.unit_anodyne _)
  rw [iteratedPathToKan, Q.map_comp]
  infer_instance

/-- 標的の Kan 比較は局所化同型。 -/
lemma iteratedRealizationToKan_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (iteratedRealizationToKan r X)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hq := boundaryReductionQuotient_image_isIso Q
    (Localization.inverts Q anodyneExtensions) r X
  have hu : IsIso (Q.map
      (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right) :=
    (Localization.inverts Q anodyneExtensions) _ (Spectra.PointedKanReplacement.unit_anodyne _)
  rw [iteratedRealizationToKan, Q.map_comp, Q.map_comp]
  infer_instance

/-- 元の反復境界と既存の点つき Kan 境界の比較は厳密に可換。 -/
lemma iteratedBoundaryToKan_comm (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealizationBoundary r X ≫ iteratedRealizationToKan r X =
      iteratedPathToKan r X ≫ (pointedFullIteratedPathKanBoundary r X).right :=
  (pointedFullIteratedPathKanBoundary_quotient r X).symm

/-- 標的の零列は Kan 比較により既存の基点へ厳密に潰れる。 -/
lemma iteratedRealizationToKan_zeroColumn (r : ℕ) (X : StableModel.{u}) :
    diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫ iteratedRealizationToKan r X =
      toUnit ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
        ((boundaryKanRealizationFunctor r).obj X).hom := by
  let c := innerZeroToFullBoundaryComparison r X ≫
    Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)
  have he : iteratedRealizationToKan r X =
      diagonalReductionQuotient (iteratedSRealizationDiagram r X) ≫ c.right := by
    rw [iteratedRealizationToKan]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫
        (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization r X)).right)
        (innerZeroToFullBoundaryComparison_quotient r X).symm)
  have hq : diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫
      diagonalReductionQuotient (iteratedSRealizationDiagram r X) =
    toUnit ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
      (reducedDiagonal (iteratedSRealizationDiagram r X)).hom :=
    PointedObject.cofiberQuotient_condition _
  have hw : (reducedDiagonal (iteratedSRealizationDiagram r X)).hom ≫ c.right =
      ((boundaryKanRealizationFunctor r).obj X).hom := Under.w c
  rw [he, ← Category.assoc, hq, Category.assoc, hw]

end SerrePositivity.KST.SConstruction
