module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelHomotopyAdjunction
/-!
概要：実 kernel 分解の半自由出力射影に、同じ telescope の H⁰ 右随伴を与える。
方針：実 augmentation の主導来比較と同じ入力射影の比較同値を使う。
規約：分解圏の Small 性は要求しない。使われ方：余単位の全 Hom 準同型性の検査。
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
/-- 実 kernel 分解の出力射影に対する、同じ telescope の H⁰ 右随伴。 -/
def dgKernelResolutionHomotopyRightAdjoint (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) ⥤
      HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R E).asEquivalence.functor ⋙
    _root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedHom R D E
      ((_root_.SerrePositivity.DifferentialGraded.bimoduleToDerived R E D).obj (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P)) ⋙
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R D).asEquivalence.inverse ⋙
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionSourceHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).inverse)
/-- 元の実 kernel 分解の出力射影の H⁰ 随伴。 -/
def dgKernelResolutionHomotopyAdjunction (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).onHomotopy ⊣
        dgKernelResolutionHomotopyRightAdjoint R D E P := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F
  let eP := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionSourceHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F
  let eD := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R D).asEquivalence
  let eE := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModuleToDerived R E).asEquivalence
  let K := (_root_.SerrePositivity.DifferentialGraded.bimoduleToDerived R E D).obj (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P)
  let T := _root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P
  have e : G.onHomotopy ⋙ eE.functor ≅ (eP.functor ⋙ eD.functor) ⋙ T :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionDerivedComparisonIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E F ≪≫
      Functor.isoWhiskerLeft eP.functor
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeClassicalDerivedFunctorIso R D E (Morita.kernelTensor R D E P)).symm ≪≫
      (Functor.associator _ _ _).symm
  have e' : G.onHomotopy ≅ ((eP.functor ⋙ eD.functor) ⋙ T) ⋙ eE.inverse :=
    CategoryTheory.Iso.isoCompInverse e
  let adjT := (_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedAdjunction R D E K).ofNatIsoLeft
    (_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimoduleIso R D E (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P))
  exact (((eP.toAdjunction.comp eD.toAdjunction).comp adjT).comp
    eE.symm.toAdjunction).ofNatIsoLeft e'.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
