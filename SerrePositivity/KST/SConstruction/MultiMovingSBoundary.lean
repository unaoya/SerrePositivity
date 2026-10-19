module
public import SerrePositivity.KST.SConstruction.MultiMovingSCore
public import SerrePositivity.KST.SConstruction.CoordinateZeroIso
public import SerrePositivity.KST.SConstruction.SubcomplexCofiberIso

/-! # 全多次数の巡回交換と全零方向の境界商
概要：最内側を先頭添字にした全多次数図式の各零方向と元の反復図式の各零方向を比較する。
方針：core の全多単体的自然同型の境界保存と既存の cofiber 商の同型を合成する。
規約：境界は独立な零方向の包含の像の合併。使われ方：既存の巡回交換の商への降下の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 全多次数の巡回交換は独立な全零方向の境界を元の全零境界へ厳密に対応させる。 -/
lemma multiMovingSCoreIso_fatBoundary (r : ℕ) (X : StableModel.{u}) :
    (coordinateZeroBoundary Finset.univ ∅ (multiInnerSCoreConstruction r X)).image
      (simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal (r + 1))
        (multiMovingSCoreIso r X).hom)) = zeroDirectionsFatBoundary (r + 1) X :=
  coordinateZeroBoundary_image_iso Finset.univ ∅ (multiMovingSCoreIso r X)

/-- 独立な全零方向の境界商から元の全零境界商への巡回交換の同型。 -/
def multiMovingSBoundaryIso (r : ℕ) (X : StableModel.{u}) :
    PointedObject.cofiber
      (coordinateZeroBoundary Finset.univ ∅ (multiInnerSCoreConstruction r X)).ι ≅
        boundaryReducedRealization r X :=
  subcomplexCofiberIso _ _
    (simplicialDiagonalFunctor.mapIso (Functor.isoWhiskerLeft (multiIndexDiagonal (r + 1))
      (multiMovingSCoreIso r X))) (multiMovingSCoreIso_fatBoundary r X)

/-- 元の巡回交換と商射を、独立な全零方向の商を通して厳密に回収する。 -/
lemma multiMovingSBoundaryIso_quotient (r : ℕ) (X : StableModel.{u}) :
    (iteratedSMultiInnerRealizationIso r X).hom ≫ PointedObject.cofiberQuotient
        (coordinateZeroBoundary Finset.univ ∅ (multiInnerSCoreConstruction r X)).ι ≫
        (multiMovingSBoundaryIso r X).hom.right =
      (iteratedSRealizationCyclicIso r X).hom ≫ boundaryReductionQuotient r X := by
  have hq : PointedObject.cofiberQuotient
      (coordinateZeroBoundary Finset.univ ∅ (multiInnerSCoreConstruction r X)).ι ≫
        (multiMovingSBoundaryIso r X).hom.right =
      simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal (r + 1))
        (multiMovingSCoreIso r X).hom) ≫ boundaryReductionQuotient r X :=
    subcomplexCofiberMap_quotient _ _ _ (multiMovingSCoreIso_fatBoundary r X).le
  rw [hq, ← Category.assoc, multiMovingSCoreIso_realization]

end SerrePositivity.KST.SConstruction
