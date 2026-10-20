module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonContraction
public import SerrePositivity.InfinityCategories.Derived.PinchedPrecompositionMaps

/-! # 合成閉分母の商前合成

概要：元の二閉分母の合成と、その商像による全単体前合成を厳密に照合する。
方針：閉射の像の合成則を Hom 鎖写像上で使い、pinched Hom へ移す。
規約：商の対象を明示して閉零圏との強制変換を固定する。使われ方：骨格段の比較の更新。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商像の二前合成は、元の合成閉射の商像による前合成と一致する。 -/
lemma dgQuotientPrecomposition_comp (P : Set D) {p q x y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj q) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map s) ≫
    pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj p) (x := (inclusion A D P).obj q)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map r) =
    pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj p) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map (r ≫ s)) := by
  change pinchedHomChainMap (dgClosedPrecomposition A (QuotientObject D P)
    (q := (inclusion A D P).obj q) (x := (inclusion A D P).obj x)
    (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map s)) ≫
    pinchedHomChainMap (dgClosedPrecomposition A (QuotientObject D P)
    (q := (inclusion A D P).obj p) (x := (inclusion A D P).obj q)
    (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map r)) = _
  rw [← pinchedHomChainMap_comp, dgClosedPrecomposition_map_comp]
  rfl

end SerrePositivity.InfinityCategories
