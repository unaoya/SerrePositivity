module
public import SerrePositivity.InfinityCategories.Derived.DGClosedVerdierRoofDiagram
public import SerrePositivity.InfinityCategories.Derived.DGClosedPinchedFunctorMap
public import SerrePositivity.InfinityCategories.Derived.DGQuotientRelativeFillerRefinement

/-! # 元の厳密屋根図式から商内の実 pinched 図式への比較

概要：同じ元の実分母を添字として、その始域の商像からの実写像空間を取る。
方針：dg 商関手の全 Hom 写像の自然変換を、指定分母の始域へ制限する。
規約：図式はまだ通常の厳密分母圏上。実 ∞ over 圏との比較は別途必要。
使われ方：有限実相対充填を屋根の写像空間比較へ接続する入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGQuotient DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 同じ元の分母添字の下で、商像の始域からの実 pinched Hom を取る図式。 -/
def dgQuotientRoofDiagram (P : Set D) (x y : D) :
    (DGClosedVerdierDenominators A D P x)ᵒᵖ ⥤ SSet.{max u v} :=
  (dgClosedVerdierDenominatorSource A D P x).op ⋙
    ((inclusion A D P).onClosed.op ⋙
      dgClosedPinchedRepresentable A (QuotientObject D P) ((inclusion A D P).obj y))

/-- 元の各厳密屋根の実写像空間を、その商内の実写像空間へ送る自然変換。 -/
def dgQuotientRoofComparison (P : Set D) (x y : D) :
    dgClosedVerdierRoofDiagram A D P x y ⟶ dgQuotientRoofDiagram A D P x y :=
  Functor.whiskerLeft (dgClosedVerdierDenominatorSource A D P x).op
    (dgClosedPinchedFunctorMap A D (QuotientObject D P) (inclusion A D P) y)

/-- 指定分母での比較は、元の商関手の Hom 鎖写像の実 pinched 写像。 -/
lemma dgQuotientRoofComparison_app (P : Set D) (x y : D)
    (s : DGClosedVerdierDenominators A D P x) :
    (dgQuotientRoofComparison A D P x y).app (op s) =
      pinchedHomChainMap ((inclusion A D P).map
        (ForgetEnrichment.to (Complex A) s.obj.left) y) := rfl

/-- 比較の自然性は、全ての厳密屋根の細分の実写像に対する可換性。 -/
lemma dgQuotientRoofComparison_naturality (P : Set D) (x y : D)
    {s t : DGClosedVerdierDenominators A D P x} (r : s ⟶ t) :
    (dgClosedVerdierRoofDiagram A D P x y).map r.op ≫
      (dgQuotientRoofComparison A D P x y).app (op s) =
    (dgQuotientRoofComparison A D P x y).app (op t) ≫
      (dgQuotientRoofDiagram A D P x y).map r.op :=
  (dgQuotientRoofComparison A D P x y).naturality r.op

end SerrePositivity.InfinityCategories
