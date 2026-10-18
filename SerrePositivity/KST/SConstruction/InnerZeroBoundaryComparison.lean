module
public import SerrePositivity.KST.SConstruction.InnerZeroColumn
public import SerrePositivity.KST.SConstruction.PointedIteratedPath

/-! # 内側の零列の商から全零境界の商への比較
概要：内側の零列だけを潰した反復実現を、既存の全零境界商へ写す。
方針：零列の像の包含と cofiber の普遍性を使う。
規約：基点を厳密に保存する実際の写像。使われ方：点つき反復経路の標的の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：内側の零列の商から全零境界商への点つき比較。
方針：零列の境界への持ち上げで cofiber の降下条件を示す。
規約：既存の座標同型と境界商を使う。使われ方：反復経路の境界の標的の照合。 -/
def innerZeroToFullBoundaryComparison (r : ℕ) (X : StableModel.{u}) :
    reducedDiagonal (iteratedSRealizationDiagram r X) ⟶ boundaryReducedRealization r X :=
  PointedObject.cofiberDesc (diagonalZeroColumn (iteratedSRealizationDiagram r X))
    (boundaryReducedRealization r X)
    ((iteratedSRealizationCoordinateIso r X).hom ≫ boundaryReductionQuotient r X) (by
      calc
        _ = (iteratedZeroColumnFatBoundaryLift r X ≫
            (zeroDirectionsFatBoundary (r + 1) X).ι) ≫ boundaryReductionQuotient r X := by
          rw [iteratedZeroColumnFatBoundaryLift_ι, Category.assoc]
        _ = iteratedZeroColumnFatBoundaryLift r X ≫
            toUnit (zeroDirectionsFatBoundary (r + 1) X : SSet.{u}) ≫
            (boundaryReducedRealization r X).hom := by
          rw [Category.assoc]
          exact congrArg (fun f => iteratedZeroColumnFatBoundaryLift r X ≫ f)
            (PointedObject.cofiberQuotient_condition (zeroDirectionsFatBoundary (r + 1) X).ι)
        _ = _ := by rw [← Category.assoc, comp_toUnit])

/-- 概要：点つき比較を商射影に戻すと既存の座標同型と全零境界の商射影を得る。
方針：cofiber の普遍性の回収式。
規約：底の単体的写像の厳密等号。使われ方：比較の弱同値性と自然性。 -/
lemma innerZeroToFullBoundaryComparison_quotient (r : ℕ) (X : StableModel.{u}) :
    diagonalReductionQuotient (iteratedSRealizationDiagram r X) ≫
      (innerZeroToFullBoundaryComparison r X).right =
        (iteratedSRealizationCoordinateIso r X).hom ≫ boundaryReductionQuotient r X :=
  PointedObject.cofiberQuotient_desc _ _ _ _

/-- 概要：内側の零列から全零境界への比較は全 anodyne 反転関手で可逆。
方針：両方の商射影の弱同値性と座標同型から合成の打ち消しを使う。
規約：商の Kan 性は不要。使われ方：既存の標的との弱同値比較。 -/
lemma innerZeroToFullBoundaryComparison_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) (r : ℕ) (X : StableModel.{u}) :
    IsIso (L.map (innerZeroToFullBoundaryComparison r X).right) := by
  have hq : IsIso (L.map (diagonalReductionQuotient (iteratedSRealizationDiagram r X))) :=
    cofiberQuotient_image_isIso_of_localized_toPoint L hL _
      (multiRealization_toPoint_localized_isIso_of_contractible r (sStableModel 0 X)
        (sConstructionZero_isContractibleKan X.carrier))
  have hf := boundaryReductionQuotient_image_isIso L hL r X
  have hc : IsIso (L.map (diagonalReductionQuotient (iteratedSRealizationDiagram r X) ≫
      (innerZeroToFullBoundaryComparison r X).right)) := by
    rw [innerZeroToFullBoundaryComparison_quotient, CategoryTheory.Functor.map_comp]
    infer_instance
  rw [CategoryTheory.Functor.map_comp] at hc
  exact (isIso_comp_left_iff _ _).mp hc

end SerrePositivity.KST.SConstruction
