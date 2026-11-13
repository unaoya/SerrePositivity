module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedSectionEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGUniversalRightAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelRightAdjointCandidate
/-!
概要：元の一般 kernel の実導来 ∞ 関手と同じ右随伴候補の随伴を構成する。
方針：厳密切断の全関手同値と、普遍余単位からの随伴を合成する。
規約：生の出力の射影性と大きい分解圏の Small 性は仮定しない。
使われ方：一般 RHom の実 ∞ 関手と三角恒等式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の一般 kernel 作用と同じ実右随伴による、両三角式付き ∞ 随伴。 -/
def dgKernelAdjunction (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelRightAdjointCandidate R D E P) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjunction R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) G (fun y => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionUniversalCounit R D E P y⟩)
  let b := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F).toAdjunction
  have q := b.comp a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F) _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement]
  exact q
end SerrePositivity.InfinityCategories.Project.DerivedCategories
