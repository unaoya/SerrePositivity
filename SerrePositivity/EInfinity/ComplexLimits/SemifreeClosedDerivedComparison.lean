module

public import SerrePositivity.EInfinity.ComplexLimits.SemifreeResolutionRetract
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.DiscreteEmbedding
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.ClosedNerveFunctorNaturality

/-!
# 元の半自由閉零圏上の通常導来源の全比較

概要：通常の複体への忘却と実導来源の合成を、既存閉 nerve 包含と全関手同型で比較する。
方針：閉射の実 Hom 同値と全単体自然性から同じ解像の retract へ戻す。
規約：元の半自由対象と全閉射を保持する。
使われ方：離散可換代数の既存 D(R) 埋め込みとの全比較。
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

lemma semifreeClosedToComplex_comp_toClosed :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A ⋙ complexToClosed A =
      (dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A)).onClosed := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (complexClosedHomEquiv A X.val Y.val).symm
    ((complexClosedHomEquiv A X.val Y.val)
      ((dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A)).onClosed.map f)) = _
  exact Equiv.symm_apply_apply _ _

lemma semifreeClosedDerivedSource_eq :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A) ≫ complexOrdinaryDerivedSource A =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A)) ≫
          complexSemifreeResolutionInfinity A := by
  have h : nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A) ≫ nerveMap (complexToClosed A) =
      nerveMap (dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A)).onClosed := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro Γ
    change (Γ ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A) ⋙ complexToClosed A = _
    rw [Functor.assoc, semifreeClosedToComplex_comp_toClosed]
    rfl
  calc
    _ = (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A) ≫ nerveMap (complexToClosed A)) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A) ≫ complexSemifreeResolutionInfinity A := by
      simp only [complexOrdinaryDerivedSource, Category.assoc]
    _ = _ := by
      rw [h, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion_dgFunctor]
      rw [Category.assoc]

def semifreeClosedDerivedSourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex A) ≫ complexOrdinaryDerivedSource A)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A)) := by
  have e := (complexSemifreeResolutionRetractIso A).precomp
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A))
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A)) ≫
          complexSemifreeResolutionInfinity A)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory, Category.comp_id] using e
  exact eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (semifreeClosedDerivedSource_eq A)) ≪≫ e'

end SerrePositivity.EInfinity.ComplexLimits
