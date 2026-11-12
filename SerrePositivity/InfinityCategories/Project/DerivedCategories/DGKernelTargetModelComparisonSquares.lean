module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomIsoPrecompExchange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTargetModelAugmentationNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedComparisonCoherence
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D C E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
lemma dgKernelDerivedInfinity_graph_precomp_square
    {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D} (b : Q ⟶ Q') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C E F)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D C).map b) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R C E F).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R C E F).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R C E (functorGraph R C E F))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D C).map b) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_iso_precomp_exchange ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D C).map b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R C E F).symm
lemma dgKernelDerivedInfinity_targetModel_comparison_square
    {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D}
    (q : Q ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q' : Q' ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P')
    (a : P ⟶ P') (b : Q ⟶ Q')
    (h : b ≫ q' = q ≫ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a)
    (hF : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q))
    (hQ' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q'))
    (hq : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q)
    (hq' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q') :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation R D C E F P Q q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_quasiIso R D C E F P Q q hF hQ hq)).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map a =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E C D
        (𝟙 (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F))) b) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation R D C E F P' Q' q')
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_quasiIso R D C E F P' Q' q' hF hQ' hq')).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_naturality R D E _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_quasiIso R D C E F P Q q hF hQ hq)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_quasiIso R D C E F P' Q' q' hF hQ' hq') _ a
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_naturality R D C E F q q' a b h).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
