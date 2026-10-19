module
public import SerrePositivity.KST.SConstruction.MultiInnerSCoordinateCore
public import SerrePositivity.KST.SConstruction.MultiMovingSBoundary

/-! # 既存の全零境界商上の巡回自己同型
概要：元の座標比較と元の S 巡回交換の差は、標準反復の全零境界とその既存の商を保つ。
方針：全多次数の座標比較と交換が同じ独立な零境界を標準境界へ送ることを使う。
規約：元の全零境界商の自己同型として構成。使われ方：元の suspension 構造射と経路模型の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 元の結合子の座標比較は独立な全零方向の境界を標準の全零境界へ写す。 -/
lemma multiInnerSCoordinateRealizationIso_fatBoundary (r : ℕ) (X : StableModel.{u}) :
    (coordinateZeroBoundary Finset.univ ∅ (multiInnerSCoreConstruction r X)).image
      (multiInnerSCoordinateRealizationIso r X).hom = zeroDirectionsFatBoundary (r + 1) X := by
  change (coordinateZeroBoundary Finset.univ ∅ (multiInnerSCoreConstruction r X)).image
    (simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal (r + 1))
      (multiInnerSCoordinateCoreIso r X).hom) ≫
      (coordinatePermutationDiagonalIso (finRotate (r + 1))
        (multiCoreSConstruction (r + 1) X)).hom) = _
  rw [Subcomplex.image_comp, coordinateZeroBoundary_image_iso,
    coordinateZeroBoundary_permutation]
  rfl

/-- 元の座標比較と巡回交換の差で与えられる標準反復実現の自己同型。 -/
def cyclicRealizationIso (r : ℕ) (X : StableModel.{u}) :
    multiDiagonalCoreSConstruction (r + 1) X ≅ multiDiagonalCoreSConstruction (r + 1) X :=
  (iteratedSRealizationCoordinateIso r X).symm ≪≫ iteratedSRealizationCyclicIso r X

/-- 巡回自己同型は全多次数の座標比較の逆と全多次数の交換の合成。 -/
lemma cyclicRealizationIso_hom (r : ℕ) (X : StableModel.{u}) :
    (cyclicRealizationIso r X).hom = (multiInnerSCoordinateRealizationIso r X).inv ≫
      simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal (r + 1))
        (multiMovingSCoreIso r X).hom) := by
  have hc : (iteratedSRealizationCoordinateIso r X).inv ≫
      (iteratedSMultiInnerRealizationIso r X).hom =
      (multiInnerSCoordinateRealizationIso r X).inv := by
    apply (cancel_mono (multiInnerSCoordinateRealizationIso r X).hom).mp
    rw [Category.assoc, multiInnerSCoordinateCoreIso_realization,
      Iso.inv_hom_id, Iso.inv_hom_id]
  change (iteratedSRealizationCoordinateIso r X).inv ≫
    (iteratedSRealizationCyclicIso r X).hom = _
  rw [← multiMovingSCoreIso_realization, ← Category.assoc, hc]

/-- 元の巡回自己同型は標準の全零境界を厳密に保存する。 -/
lemma cyclicRealizationIso_fatBoundary (r : ℕ) (X : StableModel.{u}) :
    (zeroDirectionsFatBoundary (r + 1) X).image (cyclicRealizationIso r X).hom =
      zeroDirectionsFatBoundary (r + 1) X := by
  rw [cyclicRealizationIso_hom, Subcomplex.image_comp,
    subcomplex_image_iso_inv _ _ (multiInnerSCoordinateRealizationIso r X)
      (multiInnerSCoordinateRealizationIso_fatBoundary r X)]
  exact multiMovingSCoreIso_fatBoundary r X

/-- 元の標準反復の全零境界商上の巡回自己同型。 -/
def cyclicBoundaryIso (r : ℕ) (X : StableModel.{u}) :
    boundaryReducedRealization r X ≅ boundaryReducedRealization r X :=
  subcomplexCofiberIso _ _ (cyclicRealizationIso r X) (cyclicRealizationIso_fatBoundary r X)

/-- 商上の巡回自己同型を元の実現へ引き戻す式。 -/
lemma cyclicBoundaryIso_quotient (r : ℕ) (X : StableModel.{u}) :
    boundaryReductionQuotient r X ≫ (cyclicBoundaryIso r X).hom.right =
      (cyclicRealizationIso r X).hom ≫ boundaryReductionQuotient r X :=
  subcomplexCofiberMap_quotient _ _ _ (cyclicRealizationIso_fatBoundary r X).le

/-- 元の座標比較と境界商に巡回自己同型を合成すると、元の巡回交換の商写像になる。 -/
lemma cyclicBoundaryIso_coordinate_quotient (r : ℕ) (X : StableModel.{u}) :
    (iteratedSRealizationCoordinateIso r X).hom ≫ boundaryReductionQuotient r X ≫
        (cyclicBoundaryIso r X).hom.right =
      (iteratedSRealizationCyclicIso r X).hom ≫ boundaryReductionQuotient r X := by
  rw [cyclicBoundaryIso_quotient]
  change (iteratedSRealizationCoordinateIso r X).hom ≫
    ((iteratedSRealizationCoordinateIso r X).inv ≫
      (iteratedSRealizationCyclicIso r X).hom) ≫ boundaryReductionQuotient r X = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.KST.SConstruction
