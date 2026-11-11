module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofFamilyRealization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingHomActionFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofPresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.WeakRoofDescentTransportEvaluation
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x y : D) {K Y : SSet.{max u v}} [Quasicategory Y]
variable (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y)
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofPresentation A D P x y a)
variable (e : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingPinchedFamilyEvaluation A D F R.denominator.obj.hom R.coefficient)
variable (b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
variable (HQ : SSet.Homotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
  (b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y))
/-- 指定評価族への実比較は、全降下選択空間上で同じ評価族への一つの関手同型を与える。 -/
def dgPresentedFamilyEvaluationIso
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofFamilyRealization A D P x y F R.denominator R.coefficient e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e.value)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescentTransportEvaluationIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y)
    (R.coefficient ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y R.denominator) a b e.value
    R.transport HQ C.homotopy
include HQ in
/-- 任意の指定実評価族は、表示の輸送とともに全選択空間上の作用族を同時に評価する。 -/
lemma dgPresentedFamilyEvaluationIso_nonempty :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x y F ≫ (pre b).app _)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e.value))) := by
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFamilyRealization_nonempty A D P x y F
    R.denominator R.coefficient e
  exact ⟨dgPresentedFamilyEvaluationIso A D P x y F a R e b HQ C⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
