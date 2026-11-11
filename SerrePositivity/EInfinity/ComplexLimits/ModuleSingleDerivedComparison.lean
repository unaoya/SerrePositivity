module

public import SerrePositivity.EInfinity.ComplexLimits.SemifreeClosedDerivedComparison
public import SerrePositivity.EInfinity.ComplexLimits.DerivedNatTransIso

/-!
# 元の加群の零次複体と既存半自由解像の全比較

概要：実通常導来源による零次複体の像を、元の加群の既存解像と全関手同型で比較する。
方針：元の自然な augmentation を全成分で反転し、半自由閉源の比較を合成する。
規約：全加群と全加群射、元の関手的解像を保持する。
使われ方：離散可換代数の U 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A]

lemma moduleResolutionDerivedSource_eq :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A) ≫
      complexOrdinaryDerivedSource A =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A) ≫
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A) ≫ complexOrdinaryDerivedSource A) := by
  have h : nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro Γ
    change Γ ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A) =
      (Γ ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A) ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A
    exact (Functor.assoc _ _ _).symm
  rw [h, Category.assoc]

def moduleSingleOrdinaryDerivedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (HomologicalComplex.single (ModuleCat A) (.up ℤ) 0) ≫
      complexOrdinaryDerivedSource A)
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A)) := by
  have e := complexOrdinaryDerivedNatTransIso A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionAugmentation A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionAugmentation_quasiIso A)
  exact e.symm ≪≫ eqToIso
    (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
      (moduleResolutionDerivedSource_eq A)) ≪≫
    (semifreeClosedDerivedSourceIso A).precomp (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A))

end SerrePositivity.EInfinity.ComplexLimits
