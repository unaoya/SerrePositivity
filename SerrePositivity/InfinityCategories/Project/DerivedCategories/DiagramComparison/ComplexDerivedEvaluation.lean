module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SemifreePointComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGModuleResolvedInvertsQuasiIso
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictDiagramEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictComplexDiagram

/-!
概要：元の通常複体とstrict図式の全nerveを、既存の半自由模型D(A)へ評価する。
方針：元の閉零射の表示、一点dg加群の指定分解、既存の一点評価同値を合成する。
規約：全単体を持つ実写像を作り、局所化後の図式圏同値はここでは主張しない。
使われ方：3b-3 R5、HTT 4.2.4.4の元のstrict図式の評価との比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A]

/-- 元の複体と元の鎖写像を、それを表す閉次数零射として読む。 -/
def complexClosedPresentation : Complex A ⥤ ClosedCategory A (Complex A) where
  obj X := ForgetEnrichment.of (Complex A) X
  map {X Y} f := (complexClosedHomEquiv A X Y).symm f
  map_id X := by
    apply (complexClosedHomEquiv A X X).injective
    rw [Equiv.apply_symm_apply, complexClosedHomEquiv_id]
  map_comp {X Y Z} f g := by
    apply (complexClosedHomEquiv A X Z).injective
    rw [Equiv.apply_symm_apply, complexClosedHomEquiv_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- 元の全複体のnerveから、指定された既存D(A)の模型への実評価。 -/
def complexDerivedEvaluation : nerve (Complex A) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  nerveMap (complexClosedPresentation A) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A) ≫
    dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
      (semifreePointEquivalence A).hom

/-- 元のstrict複体図式の全射列と添字の全射列を同時に評価する。 -/
def strictComplexDerivedEvaluation (d : StrictDiagramDirection) :
    strictComplexDiagramNerve A d ⊗
        (SSet.uliftFunctor.{u + 1, 0}).obj (nerve (strictDiagramIndex d)) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A :=
  strictDiagramEvaluation (strictDiagramIndex d) (Complex A) ≫ complexDerivedEvaluation A

/-- 元のstrict複体図式の全パラメーターを、同じD(A)の図式の全族へ送る。 -/
def strictComplexDiagramFamily (d : StrictDiagramDirection) :
    strictComplexDiagramNerve A d ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, 0}).obj (nerve (strictDiagramIndex d)))).obj
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) :=
  curry ((β_ _ _).hom ≫ strictComplexDerivedEvaluation A d)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
