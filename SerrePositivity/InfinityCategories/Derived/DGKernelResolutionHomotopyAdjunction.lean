module
public import SerrePositivity.InfinityCategories.Derived.DGKernelHomotopyAdjunction
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 実 kernel 分解の出力射影に対する、同じ telescope の H⁰ 右随伴。 -/
def dgKernelResolutionHomotopyRightAdjoint (P : Bimodule R E D) :
    HomotopyCategory R (SemifreeDGModules R E) ⥤
      HomotopyCategory R (DGModuleFunctorResolutionObject R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P)) :=
  (dgSemifreeModuleToDerived R E).asEquivalence.functor ⋙
    Morita.kernelDerivedHom R D E
      ((bimoduleToDerived R E D).obj (BimoduleCategory.of R E D P)) ⋙
    ((dgSemifreeModuleToDerived R D).asEquivalence.inverse ⋙
      (dgModuleResolutionSourceHomotopyEquivalence R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P)).inverse)
/-- 元の実 kernel 分解の出力射影の H⁰ 随伴。 -/
def dgKernelResolutionHomotopyAdjunction (P : Bimodule R E D) :
    (dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P)).onHomotopy ⊣
        dgKernelResolutionHomotopyRightAdjoint R D E P := by
  let F := dgSemifreeKernelModuleDG R D E P
  let G := dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E F
  let eP := dgModuleResolutionSourceHomotopyEquivalence R (SemifreeDGModules R D) E F
  let eD := (dgSemifreeModuleToDerived R D).asEquivalence
  let eE := (dgSemifreeModuleToDerived R E).asEquivalence
  let K := (bimoduleToDerived R E D).obj (BimoduleCategory.of R E D P)
  let T := Morita.kernelDerivedTensorOnBimodule R D E P
  have e : G.onHomotopy ⋙ eE.functor ≅ (eP.functor ⋙ eD.functor) ⋙ T :=
    dgModuleResolutionDerivedComparisonIso R (SemifreeDGModules R D) E F ≪≫
      Functor.isoWhiskerLeft eP.functor
        (dgSemifreeClassicalDerivedFunctorIso R D E (Morita.kernelTensor R D E P)).symm ≪≫
      (Functor.associator _ _ _).symm
  have e' : G.onHomotopy ≅ ((eP.functor ⋙ eD.functor) ⋙ T) ⋙ eE.inverse :=
    CategoryTheory.Iso.isoCompInverse e
  let adjT := (Morita.kernelDerivedAdjunction R D E K).ofNatIsoLeft
    (Morita.kernelDerivedTensorOnBimoduleIso R D E (BimoduleCategory.of R E D P))
  exact (((eP.toAdjunction.comp eD.toAdjunction).comp adjT).comp
    eE.symm.toAdjunction).ofNatIsoLeft e'.symm
end SerrePositivity.InfinityCategories
