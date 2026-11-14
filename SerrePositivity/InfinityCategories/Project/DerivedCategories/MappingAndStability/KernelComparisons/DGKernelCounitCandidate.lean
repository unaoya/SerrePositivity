module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGUniversalCommaCounit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedSectionIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelRightAdjointCandidate
/-!
概要：実入力切断の同じ比較を通じ、一般 kernel の右随伴候補に実余単位を戻す。
方針：入力射影と指定切断の全関手同型を、普遍余単位の全関手ホモトピーへ合成する。
規約：随伴の三角式は別工程。使われ方：元の一般 kernel ∞ 作用の ∞ 随伴判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の右随伴候補との合成を、同じ普遍余単位の合成へ比較する。 -/
def dgKernelRightAdjointCompositeIso (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelRightAdjointCandidate R D E P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCandidate R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P))
        (fun y => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionUniversalCounit R D E P y⟩) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P))) := by
  let C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P
  let T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F
  let R' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCandidate R T (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) G
    (fun y => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionUniversalCounit R D E P y⟩)
  have e := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedProjectionSectionIso R C E F).postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)).precomp R'
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((R' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F) (R' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement]
  simpa only [Category.assoc, Category.id_comp] using! e
/-- 元の kernel 作用の右随伴候補の、同じ実比較から得る h Fun の余単位。 -/
def dgKernelCounitCandidate (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelRightAdjointCandidate R D E P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      (𝟙 _) :=
  (dgKernelRightAdjointCompositeIso R D E P).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCounit R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P))
      (fun y => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionUniversalCounit R D E P y⟩)
/-- 同じ余単位の類を保つ、全関手ホモトピーの実代表。 -/
def dgKernelCounitCandidateHomotopy (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelRightAdjointCandidate R D E P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) (𝟙 _) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (dgKernelCounitCandidate R D E P)
/-- 選んだ実ホモトピーは、元の同じ全関手の余単位を回収する。 -/
lemma dgKernelCounitCandidateHomotopy_hom (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgKernelCounitCandidateHomotopy R D E P)) = dgKernelCounitCandidate R D E P :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
