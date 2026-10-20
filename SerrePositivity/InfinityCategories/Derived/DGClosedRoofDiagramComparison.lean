module
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofDiagramTransports
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofHomComparison

/-! # 一般係数比較の実商屋根への移送

概要：一般対の境界固定係数比較を、同じ実分母上の実商屋根の比較へ移す。
方針：商 Hom 包含で後合成し、元の包含と商比較の可換性で終端を照合する。
規約：指定部分の全時刻固定と実分母への定値射影を保つ。使われ方：相対輸送三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {s' s : DGClosedVerdierDenominators A D P x} (R : s' ⟶ s)
variable {L K : SSet.{max u v}} (i : L ⟶ K)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
  ((inclusion A D P).obj y))
variable (t : K ⟶ DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y)
variable (C : SSet.Homotopy
  (g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
    (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map R.hom.left))
  (t ≫ pinchedHomChainMap ((inclusion A D P).map
    (ForgetEnrichment.to (Complex A) s'.obj.left) y)))

/-- 一般係数比較を同じ実分母の商屋根へ移す。 -/
def dgClosedRoofDiagramComparison : SSet.Homotopy
    (g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map R.hom.left) ≫
        dgQuotientClosedRoofHomInclusion A D P x y s')
    (t ≫ dgClosedRoofHomInclusion A D P x y s' ≫ dgRoofCorrespondenceMap A D P x y) :=
  stableHomotopyRetarget
    (functorHomotopyPostcomp C (dgQuotientClosedRoofHomInclusion A D P x y s'))
    (Category.assoc _ _ _) (by rw [Category.assoc, ← dgClosedRoofHomInclusion_comparison])

/-- 係数比較の全時間の射は、同じ商 Hom 包含による後合成。 -/
lemma dgClosedRoofDiagramComparison_h :
    (dgClosedRoofDiagramComparison A D P x y R g t C).h =
      C.h ≫ dgQuotientClosedRoofHomInclusion A D P x y s' :=
  homotopyRetarget_h _ _ _

/-- 実商屋根内の比較も指定部分を全時刻固定する。 -/
lemma dgClosedRoofDiagramComparison_fixed
    (hC : (i ▷ (Δ[1] : SSet.{max u v})) ≫ C.h =
      fst L Δ[1] ≫ i ≫ g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
        (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map R.hom.left)) :
    (i ▷ Δ[1]) ≫ (dgClosedRoofDiagramComparison A D P x y R g t C).h =
      fst L Δ[1] ≫ i ≫ g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
        (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map R.hom.left) ≫
          dgQuotientClosedRoofHomInclusion A D P x y s' := by
  rw [dgClosedRoofDiagramComparison_h, ← Category.assoc, hC]
  simp only [Category.assoc]

/-- 比較の全時刻は同じ細分後の実分母に厳密に射影される。 -/
lemma dgClosedRoofDiagramComparison_projection :
    (dgClosedRoofDiagramComparison A D P x y R g t C).h ≫
      dgQuotientRoofCorrespondenceProjection A D P x y =
      SSet.const (dgClosedVerdierDenominatorVertex A D P x s') := by
  rw [dgClosedRoofDiagramComparison_h, Category.assoc,
    dgQuotientClosedRoofHomInclusion_projection, SSet.comp_const]

end SerrePositivity.InfinityCategories
