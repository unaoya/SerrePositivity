module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.DGSemifreeModules
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.ClosedNerveFunctorNaturality

import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.InfinityCategory

/-!
概要：全複体の評価を半自由複体の元の表示へ制限して比較する。
方針：半自由出力の包含後の比較を充満忠実性で戻し、入力前合成を照合する。
規約：指定されたD(A)と同じ宇宙を使い、別の導来圏模型を選ばない。
使われ方：3b-3 R5・R7、3b-1の半自由図式との接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories

variable (A : Type u) [CommRing A]

/-- 半自由出力を既に持つ定数加群関手の、実分解との全関手比較。 -/
def semifreeConstantResolvedIso :
    FunctorIso
      (dgModuleResolvedInfinity A (Semifree A) PUnit.{1}
        ((semifreePointConstant A).comp
          (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
            (dgModuleSemifreeProperty A PUnit.{1}))))
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (semifreePointConstant A)) := by
  let I := dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
    (dgModuleSemifreeProperty A PUnit.{1})
  have e := dgModuleResolvedInfinity_inclusionIso A (Semifree A) PUnit.{1}
    ((semifreePointConstant A).comp I)
    (fun X => dgSemifreeModule_isProjective A PUnit.{1} ((semifreePointConstant A).obj X))
  apply (dgSemifreeModulesInclusion_isFullyFaithful A PUnit.{1}).preimageFunctorIso
  simpa only [SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] using! e

/-- 半自由複体の元のdg包含。 -/
def semifreeComplexInclusion : DGFunctor A (Semifree A) (Complex A) :=
  dgFullSubcategoryInclusion A (Complex A) (Semifree.complexSemifree A)

/-- 半自由複体から定数加群へ進む二つの表示は同じdg関手。 -/
lemma semifreeComplexInclusion_constant :
    (semifreeComplexInclusion A).comp (ringConstantDG A) =
      (semifreePointConstant A).comp
        (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
          (dgModuleSemifreeProperty A PUnit.{1})) := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro X Y
  simp [semifreeComplexInclusion, semifreePointConstant, EnrichedFunctor.comp_map,
    dgFullSubcategoryInclusion]

/-- 全複体の指定分解を半自由入力へ制限すると、元の定数加群の全関手になる。 -/
def semifreeComplexResolvedIso :
    FunctorIso
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (semifreeComplexInclusion A) ≫
          dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A))
      (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (semifreePointConstant A)) := by
  have e := dgModuleResolvedInfinity_precompIso A (Semifree A) (Complex A) PUnit.{1}
    (semifreeComplexInclusion A) (ringConstantDG A)
  rw [semifreeComplexInclusion_constant] at e
  exact e.symm ≪≫ semifreeConstantResolvedIso A

/-- 定数一点加群をその点で評価すると、元の半自由複体に厳密に戻る。 -/
lemma semifreePointConstant_comp_evaluation :
    (semifreePointConstant A).comp (semifreePointEvaluation A) = DGFunctor.id (Semifree A) := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro X Y
  change (ringConstantHomIso A X.val Y.val).inv ≫
    (ringConstantHomIso A X.val Y.val).hom = 𝟙 _
  exact Iso.inv_hom_id _

/-- 同じD(A)への一点比較は、定数半自由入力の上で厳密に恒等となる。 -/
lemma semifreePointConstant_equivalence :
    SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (semifreePointConstant A) ≫ (semifreePointEquivalence A).hom =
        𝟙 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) := by
  change SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (semifreePointConstant A) ≫
    SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (semifreePointEvaluation A) = _
  rw [← SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
    semifreePointConstant_comp_evaluation,
    SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id]
  rfl

/-- 半自由の閉零射を、その元の通常の鎖写像として読む。 -/
def semifreeUnderlyingComplex : ClosedCategory A (Semifree A) ⥤ Complex A :=
  (semifreeComplexInclusion A).onClosed ⋙ closedToComplex A

/-- 通常の鎖写像への表示と閉零射への表示を通すと、元の同じ包含になる。 -/
lemma semifreeUnderlyingComplex_presentation :
    semifreeUnderlyingComplex A ⋙ complexClosedPresentation A =
      (semifreeComplexInclusion A).onClosed := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro X
    rfl
  intro X Y f
  change (complexClosedHomEquiv A _ _).symm
    (complexClosedHomEquiv A _ _ ((semifreeComplexInclusion A).onClosed.map f)) = _
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    (Equiv.symm_apply_apply (complexClosedHomEquiv A _ _)
      ((semifreeComplexInclusion A).onClosed.map f))

/-- 元の半自由複体の全nerveで、全複体評価は元の閉nerve包含と全関手同型。 -/
def complexDerivedEvaluation_semifreeIso :
    FunctorIso
      (nerveMap (semifreeUnderlyingComplex A) ≫ complexDerivedEvaluation A)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Semifree A)) := by
  have e := ((semifreeComplexResolvedIso A).postcomp (semifreePointEquivalence A).hom).precomp
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Semifree A))
  rw [Category.assoc, semifreePointConstant_equivalence] at e
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory] at e
  simp only [Category.comp_id] at e
  have he : nerveMap (semifreeUnderlyingComplex A) ≫ complexDerivedEvaluation A =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Semifree A) ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (semifreeComplexInclusion A) ≫
            dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
              (semifreePointEquivalence A).hom := by
    have hn : nerveMap (semifreeUnderlyingComplex A) ≫ nerveMap (complexClosedPresentation A) =
        nerveMap (semifreeComplexInclusion A).onClosed := by
      change nerveMap (semifreeUnderlyingComplex A ⋙ complexClosedPresentation A) = _
      rw [semifreeUnderlyingComplex_presentation]
    simp only [complexDerivedEvaluation, ← Category.assoc]
    rw [closedNerveInclusion_dgFunctor, hn]
  rw [he]
  exact e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
