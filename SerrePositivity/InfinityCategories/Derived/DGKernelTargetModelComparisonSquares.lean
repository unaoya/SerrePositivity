module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomIsoPrecompExchange
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelAugmentationNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedComparisonCoherence
/-!
概要：元の出力模型比較の射が、実導来射作用の可換四角形を満たす。
方針：型付きの交換則・元の κ・実 augmentation の三つの四角形を合成する。
規約：指定比較・計算上限を変更しない。使われ方：一般 cell 模型の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D C E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C E)
lemma dgKernelDerivedInfinity_graph_precomp_square
    {Q Q' : BimoduleCategory R C D} (b : Q ⟶ Q') :
    functorHomPostcomp
        (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))
        (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))
        (dgModuleExtensionInfinity R C E F)
        ((dgKernelDerivedFunctorHomFunctor R D C).map b) ≫
      (FunctorIso.precomp (dgKernelDerivedInfinity_graphIso R C E F).symm
        (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))).hom =
    (FunctorIso.precomp (dgKernelDerivedInfinity_graphIso R C E F).symm
      (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))).hom ≫
    functorHomPostcomp
      (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))
      (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))
      (dgKernelDerivedInfinity R C E (functorGraph R C E F))
      ((dgKernelDerivedFunctorHomFunctor R D C).map b) :=
  functorHom_iso_precomp_exchange ((dgKernelDerivedFunctorHomFunctor R D C).map b)
    (dgKernelDerivedInfinity_graphIso R C E F).symm
lemma dgKernelDerivedInfinity_targetModel_comparison_square
    {P P' : BimoduleCategory R E D} {Q Q' : BimoduleCategory R C D}
    (q : Q ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q' : Q' ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P')
    (a : P ⟶ P') (b : Q ⟶ Q')
    (h : b ≫ q' = q ≫ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a)
    (hF : QuasiEquivalence F)
    (hQ : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q))
    (hQ' : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q'))
    (hq : BimoduleCategory.quasiIso R C D q)
    (hq' : BimoduleCategory.quasiIso R C D q') :
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R D E
      (dgKernelTargetModelAugmentation R D C E F P Q q)
      (dgKernelTargetModelAugmentation_quasiIso R D C E F P Q q hF hQ hq)).hom ≫
        (dgKernelDerivedFunctorHomFunctor R D E).map a =
    (dgKernelDerivedFunctorHomFunctor R D E).map
      (BimoduleTensor.composeMap R E C D
        (𝟙 (BimoduleCategory.of R E C (functorGraph R C E F))) b) ≫
      (dgKernelDerivedInfinity_mapIso_of_quasiIso R D E
        (dgKernelTargetModelAugmentation R D C E F P' Q' q')
        (dgKernelTargetModelAugmentation_quasiIso R D C E F P' Q' q' hF hQ' hq')).hom :=
  dgKernelDerivedInfinity_comparison_naturality R D E _ _
    (dgKernelTargetModelAugmentation_quasiIso R D C E F P Q q hF hQ hq)
    (dgKernelTargetModelAugmentation_quasiIso R D C E F P' Q' q' hF hQ' hq') _ a
    (dgKernelTargetModelAugmentation_naturality R D C E F q q' a b h).symm
end SerrePositivity.InfinityCategories
