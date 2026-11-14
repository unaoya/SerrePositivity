module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGUniversalCommaNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelUniversalCounit
/-!
概要：一般 kernel の実普遍余単位の厳密切断から、元の導来 ∞ 圏間の右随伴候補を作る。
方針：実 comma の逆と始域射影を、元の実入力射影へ合成する。
規約：∞ 随伴・三角式の検証は別工程。使われ方：一般 RHom の coherent な実関手。
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
/-- 元の一般 kernel 作用の右随伴候補。実全単体の関手として構成する。 -/
def dgKernelRightAdjointCandidate (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCandidate R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P))
    (fun y => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionUniversalCounit R D E P y⟩) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
