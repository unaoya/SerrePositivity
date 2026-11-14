module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientInvertingRoofIdentification
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGInvertingRoofFamilyRealization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGFiniteRoofPresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.WeakRoofFamilySpanComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {K : SSet.{max u v}}
variable (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x)
variable (n : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) r.obj.left) y)
variable (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingPinchedFamilyEvaluation A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) r.obj.hom n)
/-- 商内の指定評価族を、標準商頂点間の同じ実 pinched Hom の族として表示する。 -/
def dgQuotientFamilyEvaluationValue :
    K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) :=
  e.value ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex (DGQuotient.inclusion A D P) y)).hom
/-- 商内の指定評価族は、同じ実閉分母表示からの実商屋根内のホモトピーを持つ。 -/
def dgQuotientFamilyEvaluationHomotopy
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofFamilyRealization A D P x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) r n e) :
    SSet.Homotopy
      ((n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y r) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
      (dgQuotientFamilyEvaluationValue A D P x y r n e ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp C.homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientInvertingRoofIso A D P x y).hom)
    ((Category.assoc _ _ _).trans (congrArg (fun f =>
      (n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y r) ≫ f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientInvertingRoofIso_comparison A D P x y)))
    (((Category.assoc _ _ _).trans (congrArg (fun f => e.value ≫ f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientInvertingRoofIso_fixedHom A D P x y))).trans (Category.assoc _ _ _).symm)
/-- 任意の輸送付き表示の指定商評価族は、元の商 Hom 族と全パラメータで比較できる。 -/
lemma dgQuotientPresentedFamilyEvaluation_homotopy (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y) (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofPresentation A D P x y a)
    (E : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingPinchedFamilyEvaluation A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      R.denominator.obj.hom R.coefficient)
    (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
    (HQ : SSet.Homotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
      (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y)) :
    Nonempty (SSet.Homotopy
      (dgQuotientFamilyEvaluationValue A D P x y R.denominator R.coefficient E) b) := by
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFamilyRealization_nonempty A D P x y
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) R.denominator R.coefficient E
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofFamilySpanComparison (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap_isWeakHomotopyEquivalence A D P hP x y)
    _ _ b _ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp R.transport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)) HQ
      (dgQuotientFamilyEvaluationHomotopy A D P x y R.denominator R.coefficient E C)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
