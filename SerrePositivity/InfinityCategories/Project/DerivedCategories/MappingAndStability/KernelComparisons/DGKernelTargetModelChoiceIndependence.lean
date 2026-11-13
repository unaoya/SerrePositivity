module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelTargetModelNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomPostcompFaithfulTyped
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.IsoHomRightCancellation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGModuleMoritaInfinity
/-!
概要：同じ augmentation の四角形を満たす模型射の導来像は選択によらない。
方針：元の出力模型比較を消去し、準同値への後合成の充満忠実性で反映する。
規約：指定比較を変更しない。使われ方：一般 cell 模型の選択整合性。
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
lemma dgKernelDerivedInfinity_targetModel_map_independent
    {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D}
    (q : Q ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q' : Q' ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P')
    (a : P ⟶ P') (b b' : Q ⟶ Q')
    (h : b ≫ q' = q ≫ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a)
    (h' : b' ≫ q' = q ≫ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a)
    (hF : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q))
    (hQ' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q'))
    (hq : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q)
    (hq' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q') :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D C).map b =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D C).map b' := by
  have he := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity_isQCatEquivalence_of_quasiEquivalence R C E F
    hF).isFullyFaithful
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_injective_typed he
  have hb := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso_naturality R D C E F q q' a b h
    hF hQ hQ' hq hq'
  have hb' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso_naturality R D C E F q q' a b' h'
    hF hQ hQ' hq hq'
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.iso_hom_right_cancel_typed
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso R D C E F P' Q' q' hF hQ' hq')
  exact hb.symm.trans hb'
lemma dgKernelDerivedInfinity_targetModel_comparison_independent
    {P P' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q Q' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D}
    (q : Q ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q' : Q' ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P')
    (a : P ⟶ P') (b b' : Q ⟶ Q')
    (h : b ≫ q' = q ≫ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a)
    (h' : b' ≫ q' = q ≫ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a)
    (hF : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q))
    (hQ' : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q'))
    (hq : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q)
    (hq' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q')
    (hb : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D b)
    (hb' : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D b') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b hb =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b' hb' := by
  apply Iso.ext
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_hom]
  exact dgKernelDerivedInfinity_targetModel_map_independent R D C E F q q' a b b'
    h h' hF hQ hQ' hq hq'
end SerrePositivity.InfinityCategories.Project.DerivedCategories
