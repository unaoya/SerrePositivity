module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPostcompFaithfulTyped
public import SerrePositivity.InfinityCategories.Derived.IsoHomRightCancellation
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Derived.DGModuleMoritaInfinity
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D C E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C E)
lemma dgKernelDerivedInfinity_targetModel_map_independent
    {P P' : BimoduleCategory R E D} {Q Q' : BimoduleCategory R C D}
    (q : Q ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q' : Q' ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P')
    (a : P ⟶ P') (b b' : Q ⟶ Q')
    (h : b ≫ q' = q ≫ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a)
    (h' : b' ≫ q' = q ≫ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a)
    (hF : QuasiEquivalence F)
    (hQ : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q))
    (hQ' : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q'))
    (hq : BimoduleCategory.quasiIso R C D q)
    (hq' : BimoduleCategory.quasiIso R C D q') :
    (dgKernelDerivedFunctorHomFunctor R D C).map b =
      (dgKernelDerivedFunctorHomFunctor R D C).map b' := by
  have he := (dgModuleExtensionInfinity_isQCatEquivalence_of_quasiEquivalence R C E F
    hF).isFullyFaithful
  apply functorHomPostcomp_injective_typed he
  have hb := dgKernelDerivedInfinity_targetModelIso_naturality R D C E F q q' a b h
    hF hQ hQ' hq hq'
  have hb' := dgKernelDerivedInfinity_targetModelIso_naturality R D C E F q q' a b' h'
    hF hQ hQ' hq hq'
  apply iso_hom_right_cancel_typed
    (dgKernelDerivedInfinity_targetModelIso R D C E F P' Q' q' hF hQ' hq')
  exact hb.symm.trans hb'
lemma dgKernelDerivedInfinity_targetModel_comparison_independent
    {P P' : BimoduleCategory R E D} {Q Q' : BimoduleCategory R C D}
    (q : Q ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q' : Q' ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P')
    (a : P ⟶ P') (b b' : Q ⟶ Q')
    (h : b ≫ q' = q ≫ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a)
    (h' : b' ≫ q' = q ≫ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).map a)
    (hF : QuasiEquivalence F)
    (hQ : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q))
    (hQ' : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q'))
    (hq : BimoduleCategory.quasiIso R C D q)
    (hq' : BimoduleCategory.quasiIso R C D q')
    (hb : BimoduleCategory.quasiIso R C D b)
    (hb' : BimoduleCategory.quasiIso R C D b') :
    dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b hb =
      dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b' hb' := by
  apply Iso.ext
  rw [dgKernelDerivedInfinity_comparison_hom, dgKernelDerivedInfinity_comparison_hom]
  exact dgKernelDerivedInfinity_targetModel_map_independent R D C E F q q' a b b'
    h h' hF hQ hQ' hq hq'
end SerrePositivity.InfinityCategories
