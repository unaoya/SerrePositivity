module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgUnderlyingDerivedComparison
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ModuleSingleDerivedComparison

/-!
# 離散 CAlg_R 入力と既存 D(R) 埋め込みの全関手比較

概要：元の環の下の可換環を CAlg_R へ送り、同じ U との合成を既存埋め込みと比較する。
方針：元の通常忘却と零次複体の全射を照合し、元の加群解像の全比較を使う。
規約：既存 discreteEmbedding と同じ Under 源・全単体を保持する。
使われ方：E2b の離散入力と G1′ の BS 界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
open scoped Simplicial
variable (A : Type u) [CommRing A]

def discreteCAlgUnderEmbedding : nerve (Under (CommRingCat.of A)) ⟶ CAlg_R A :=
  nerveMap (commAlgCatEquivUnder (CommRingCat.of A)).inverse ≫ discreteCAlgEmbedding A

lemma discreteCAlgUnderForgetNerve_eq :
    nerveMap (commAlgCatEquivUnder (CommRingCat.of A)).inverse ≫
      nerveMap (discreteAlgebraFunctor A) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)) =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A) ≫
      nerveMap (HomologicalComplex.single (ModuleCat A) (.up ℤ) 0) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change (Γ ⋙ (commAlgCatEquivUnder (CommRingCat.of A)).inverse) ⋙
      (discreteAlgebraFunctor A ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)) =
    (Γ ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A) ⋙ HomologicalComplex.single (ModuleCat A) (.up ℤ) 0
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma discreteModuleResolutionNerve_eq :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change (Γ ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A) ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A =
    Γ ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor A)
  exact Functor.assoc _ _ _

def discreteUnderlyingDerivedSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (commAlgCatEquivUnder (CommRingCat.of A)).inverse ≫
      nerveMap (discreteAlgebraFunctor A) ≫ algebraUnderlyingDerivedSource A)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding A) := by
  have e := (_root_.SerrePositivity.ComplexLimits.moduleSingleOrdinaryDerivedIso A).precomp
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A))
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A) ≫
        nerveMap (HomologicalComplex.single (ModuleCat A) (.up ℤ) 0)) ≫
          _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding A) := by
    simpa only [← Category.assoc, discreteModuleResolutionNerve_eq, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding] using e
  have h : nerveMap (commAlgCatEquivUnder (CommRingCat.of A)).inverse ≫
      nerveMap (discreteAlgebraFunctor A) ≫ algebraUnderlyingDerivedSource A =
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A) ≫
        nerveMap (HomologicalComplex.single (ModuleCat A) (.up ℤ) 0)) ≫
          _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A := by
    simpa only [algebraUnderlyingDerivedSource, Category.assoc] using
      congrArg (fun f => f ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)
        (discreteCAlgUnderForgetNerve_eq A)
  exact eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) h) ≪≫ e'

def discreteCAlgUnderEmbedding_forgetIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (discreteCAlgUnderEmbedding A ≫ cAlgForgetDerived A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding A) := by
  have e := (discreteCAlgEmbedding_underlyingDerivedIso A).precomp
    (nerveMap (commAlgCatEquivUnder (CommRingCat.of A)).inverse)
  exact e ≪≫ discreteUnderlyingDerivedSourceIso A

end SerrePositivity.EInfinity.BarrattEccles
