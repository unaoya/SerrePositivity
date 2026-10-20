module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingRoofFamilyRealization
public import SerrePositivity.InfinityCategories.Derived.DGInvertingHomActionFamily
public import SerrePositivity.InfinityCategories.Derived.DGFiniteRoofPresentation
public import SerrePositivity.InfinityCategories.Derived.WeakRoofDescentTransportEvaluation
/-!
概要：実閉分母表示の指定評価族を、全降下選択空間上の商 Hom 作用族へ接続する。
方針：実屋根内の評価ホモトピーと表示の輸送を、同じ二段降下の比較へ代入する。
規約：任意パラメータ・全選択空間を保持する。使われ方：三評価族の合成整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {K Y : SSet.{max u v}} [Quasicategory Y]
variable (F : dgNerve A D ⟶ Y) (a : K ⟶ dgRoofCorrespondence A D P x y)
variable (R : DGFiniteRoofPresentation A D P x y a)
variable (e : DGInvertingPinchedFamilyEvaluation A D F R.denominator.obj.hom R.coefficient)
variable (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
  ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y))
variable (HQ : SSet.Homotopy (a ≫ dgRoofCorrespondenceMap A D P x y)
  (b ≫ dgQuotientFixedHomRoofMap A D P x y))
/-- 指定評価族への実比較は、全降下選択空間上で同じ評価族への一つの関手同型を与える。 -/
def dgPresentedFamilyEvaluationIso
    (C : DGInvertingRoofFamilyRealization A D P x y F R.denominator R.coefficient e) :
    FunctorIso (dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _)
      (SSet.const (functorVertex e.value)) :=
  weakRoofDescentTransportEvaluationIso (dgRoofCorrespondenceMap A D P x y)
    (dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgInvertingRoofFunctorMap A D P x y F) (dgQuotientFixedHomRoofMap A D P x y)
    (R.coefficient ≫ dgClosedRoofHomInclusion A D P x y R.denominator) a b e.value
    R.transport HQ C.homotopy
include HQ in
/-- 任意の指定実評価族は、表示の輸送とともに全選択空間上の作用族を同時に評価する。 -/
lemma dgPresentedFamilyEvaluationIso_nonempty :
    Nonempty (FunctorIso (dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _)
      (SSet.const (functorVertex e.value))) := by
  obtain ⟨C⟩ := dgInvertingRoofFamilyRealization_nonempty A D P x y F
    R.denominator R.coefficient e
  exact ⟨dgPresentedFamilyEvaluationIso A D P x y F a R e b HQ C⟩
end SerrePositivity.InfinityCategories
