module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientInvertingRoofIdentification
public import SerrePositivity.InfinityCategories.Derived.DGInvertingRoofFamilyRealization
public import SerrePositivity.InfinityCategories.Derived.DGFiniteRoofPresentation
public import SerrePositivity.InfinityCategories.Derived.WeakRoofFamilySpanComparison
/-!
概要：商関手自身の指定評価族を、元の商 Hom 族と実ホモトピーまで照合する。
方針：標準頂点の輸送後の実屋根比較と、固定商 Hom 包含の弱同値を使う。
規約：表示の全輸送と指定評価族を保つ。使われ方：三実評価族の商内の合成の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {K : SSet.{max u v}}
variable (r : DGClosedVerdierDenominators A D P x)
variable (n : K ⟶ DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) r.obj.left) y)
variable (e : DGInvertingPinchedFamilyEvaluation A D (dgQuotientNerveProjection A D P) r.obj.hom n)
/-- 商内の指定評価族を、標準商頂点間の同じ実 pinched Hom の族として表示する。 -/
def dgQuotientFamilyEvaluationValue :
    K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y) :=
  e.value ≫ (pinchedEndpointIso (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
    (dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)).hom
/-- 商内の指定評価族は、同じ実閉分母表示からの実商屋根内のホモトピーを持つ。 -/
def dgQuotientFamilyEvaluationHomotopy
    (C : DGInvertingRoofFamilyRealization A D P x y (dgQuotientNerveProjection A D P) r n e) :
    SSet.Homotopy
      ((n ≫ dgClosedRoofHomInclusion A D P x y r) ≫ dgRoofCorrespondenceMap A D P x y)
      (dgQuotientFamilyEvaluationValue A D P x y r n e ≫ dgQuotientFixedHomRoofMap A D P x y) :=
  stableHomotopyRetarget (functorHomotopyPostcomp C.homotopy
    (dgQuotientInvertingRoofIso A D P x y).hom)
    ((Category.assoc _ _ _).trans (congrArg (fun f =>
      (n ≫ dgClosedRoofHomInclusion A D P x y r) ≫ f)
        (dgQuotientInvertingRoofIso_comparison A D P x y)))
    (((Category.assoc _ _ _).trans (congrArg (fun f => e.value ≫ f)
      (dgQuotientInvertingRoofIso_fixedHom A D P x y))).trans (Category.assoc _ _ _).symm)
/-- 任意の輸送付き表示の指定商評価族は、元の商 Hom 族と全パラメータで比較できる。 -/
lemma dgQuotientPresentedFamilyEvaluation_homotopy (hP : DGQuotient.localKFlat A D P)
    (a : K ⟶ dgRoofCorrespondence A D P x y) (R : DGFiniteRoofPresentation A D P x y a)
    (E : DGInvertingPinchedFamilyEvaluation A D (dgQuotientNerveProjection A D P)
      R.denominator.obj.hom R.coefficient)
    (b : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y))
    (HQ : SSet.Homotopy (a ≫ dgRoofCorrespondenceMap A D P x y)
      (b ≫ dgQuotientFixedHomRoofMap A D P x y)) :
    Nonempty (SSet.Homotopy
      (dgQuotientFamilyEvaluationValue A D P x y R.denominator R.coefficient E) b) := by
  obtain ⟨C⟩ := dgInvertingRoofFamilyRealization_nonempty A D P x y
    (dgQuotientNerveProjection A D P) R.denominator R.coefficient E
  exact weakRoofFamilySpanComparison (dgQuotientFixedHomRoofMap A D P x y)
    (dgQuotientFixedHomRoofMap_isWeakHomotopyEquivalence A D P hP x y)
    _ _ b _ (functorHomotopyPostcomp R.transport (dgRoofCorrespondenceMap A D P x y)) HQ
      (dgQuotientFamilyEvaluationHomotopy A D P x y R.denominator R.coefficient E C)
end SerrePositivity.InfinityCategories
