module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleIsoNerve
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactor
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedInfinity
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
/-!
概要：元の双加群同型を実 tensor と半自由出力分解の全関手同型へ送る。
方針：指定の通常 tensor と全 Hom 自然な実同型、同じ出力分解を使う。
規約：元の Hom の平坦性と出力の射影性を仮定しない。
使われ方：一般 kernel の入力模型移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の双加群同型による、実 tensor dg 関手の nerve の全関手同型。 -/
def dgKernelTensorIsoNerveOfBimoduleIso {P Q : BimoduleCategory R E D} (e : P ≅ Q) :
    FunctorIso (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D P)))
      (dgNerve.map (Morita.kernelTensor R D E (BimoduleCategory.underlying R E D Q))) := by
  let J := BimoduleCategory.of R D (RightModule R D) (DGFunctor.id (RightModule R D))
  let ee : (P, J) ≅ (Q, J) := Iso.prod e (Iso.refl J)
  let ep := (BimoduleTensor.composeFunctor R E D (RightModule R D)).mapIso ee
  have h := dgBimoduleIsoNerve R E (RightModule R D) ep
  exact h
/-- 元の双加群同型による、同じ実導来作用の全関手同型。 -/
def dgKernelDerivedInfinity_bimoduleIso {P Q : BimoduleCategory R E D} (e : P ≅ Q) :
    FunctorIso (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D Q)) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)
  have h := (dgKernelTensorIsoNerveOfBimoduleIso R D E e).precomp (dgNerve.map I)
  apply dgModuleResolvedInfinity_isoOfRawFunctorIso R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P))
    (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q))
  simpa only [dgSemifreeKernelModuleDG, dgNerve.map_comp] using! h
end SerrePositivity.InfinityCategories
