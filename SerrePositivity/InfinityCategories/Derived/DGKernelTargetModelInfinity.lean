module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelAugmentation
public import SerrePositivity.InfinityCategories.Derived.DGKernelQuasiIsoComparison
/-!
概要：指定出力模型の実 kernel 作用と graph 延長の合成を、元の一般作用へ比較する。
方針：同じ全 Hom 自然な augmentation の準同型性と、実導来合成を使う。
規約：原 kernel の平坦性・射影性は不要。指定模型だけに右相対 K-flat 性を要求する。
使われ方：一般 kernel の出力模型移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D C E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C E)
  (P : BimoduleCategory R E D) (Q : BimoduleCategory R C D)
  (q : Q ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
/-- 指定右相対 K-flat 模型と準同値の graph による実作用は、元の同じ kernel の作用と同型。 -/
def dgKernelDerivedInfinity_targetModelIso (hF : QuasiEquivalence F)
    (hQ : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q))
    (hq : BimoduleCategory.quasiIso R C D q) :
    FunctorIso
      (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q) ≫
        dgModuleExtensionInfinity R C E F)
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P)) := by
  have a := FunctorIso.precomp (dgKernelDerivedInfinity_graphIso R C E F).symm
    (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))
  have b := dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D C E
    (BimoduleCategory.underlying R C D Q) (functorGraph R C E F) hQ
  have c := dgKernelDerivedInfinity_mapIso_of_quasiIso R D E
    (dgKernelTargetModelAugmentation R D C E F P Q q)
    (dgKernelTargetModelAugmentation_quasiIso R D C E F P Q q hF hQ hq)
  exact a ≪≫ b ≪≫ c
end SerrePositivity.InfinityCategories
