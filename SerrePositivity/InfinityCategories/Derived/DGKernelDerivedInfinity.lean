module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeDerivedHomInfinity
public import SerrePositivity.DifferentialGraded.Morita.Kernel
/-!
概要：任意の双加群による tensor 作用を、実半自由模型間の ∞ 関手にする。
方針：半自由入力への実 dg 制限と全単体上の実出力分解を使う。
規約：元の出力の射影性を仮定しない。使われ方：β5 の一般双加群作用。
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
/-- 任意の同じ双加群の tensor dg 関手を半自由入力へ制限する。 -/
def dgSemifreeKernelModuleDG (P : Bimodule R E D) :
    DGFunctor R (SemifreeDGModules R D) (RightModule R E) :=
  (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)).comp
    (Morita.kernelTensor R D E P)
/-- 任意の双加群による、実導来加群 ∞ 圏間の全単体的作用。 -/
def dgKernelDerivedInfinity (P : Bimodule R E D) :
    dgModuleDerivedInfinityCategory R D ⟶ dgModuleDerivedInfinityCategory R E :=
  dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R
    (SemifreeDGModules R D)) ≫
  dgModuleOutputResolutionInfinity R (SemifreeDGModules R D) E (dgSemifreeKernelModuleDG R D E P) ≫
  dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
    (SemifreeDGModules R E))
end SerrePositivity.InfinityCategories
