module
public import SerrePositivity.InfinityCategories.Derived.DGUniversalCommaNerve
public import SerrePositivity.InfinityCategories.Derived.DGKernelUniversalCounit
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の一般 kernel 作用の右随伴候補。実全単体の関手として構成する。 -/
def dgKernelRightAdjointCandidate (P : Bimodule R E D) :
    dgModuleDerivedInfinityCategory R E ⟶ dgModuleDerivedInfinityCategory R D :=
  dgUniversalRightAdjointCandidate R
    (DGModuleFunctorResolutionObject R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P)) (SemifreeDGModules R E)
    (dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P))
    (fun y => ⟨dgKernelResolutionUniversalCounit R D E P y⟩) ≫
      dgNerve.map (dgModuleFunctorResolutionSource R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P))
end SerrePositivity.InfinityCategories
