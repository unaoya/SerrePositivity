module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelComparisonSquares
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedGraphCompositionNaturality
public import SerrePositivity.InfinityCategories.Derived.IsoThreeStepSquare
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
lemma dgKernelDerivedInfinity_targetModelIso_naturality
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
    (dgKernelDerivedInfinity_targetModelIso R D C E F P Q q hF hQ hq).hom ≫
        (dgKernelDerivedFunctorHomFunctor R D E).map a =
      functorHomPostcomp
        (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))
        (dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))
        (dgModuleExtensionInfinity R C E F)
        ((dgKernelDerivedFunctorHomFunctor R D C).map b) ≫
      (dgKernelDerivedInfinity_targetModelIso R D C E F P' Q' q' hF hQ' hq').hom := by
  let U := BimoduleCategory.of R E C (functorGraph R C E F)
  let L := dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q)
  let L' := dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q')
  let G := dgKernelDerivedInfinity R C E (functorGraph R C E F)
  let H := dgModuleExtensionInfinity R C E F
  let x := (dgKernelDerivedFunctorHomFunctor R D C).map b
  let j := functorHomPostcomp L L' G x
  let z := functorHomPostcomp L L' H x
  let A := (dgKernelDerivedInfinity_graphIso R C E F).symm
  let A0 := FunctorIso.precomp A L
  let A1 := FunctorIso.precomp A L'
  let K0 := dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D C E
    (BimoduleCategory.underlying R C D Q) (functorGraph R C E F) hQ
  let K1 := dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D C E
    (BimoduleCategory.underlying R C D Q') (functorGraph R C E F) hQ'
  let c0 := dgKernelTargetModelAugmentation R D C E F P Q q
  let c1 := dgKernelTargetModelAugmentation R D C E F P' Q' q'
  let hc0 := dgKernelTargetModelAugmentation_quasiIso R D C E F P Q q hF hQ hq
  let hc1 := dgKernelTargetModelAugmentation_quasiIso R D C E F P' Q' q' hF hQ' hq'
  let C0 := dgKernelDerivedInfinity_mapIso_of_quasiIso R D E c0 hc0
  let C1 := dgKernelDerivedInfinity_mapIso_of_quasiIso R D E c1 hc1
  let t := (dgKernelDerivedFunctorHomFunctor R D E).map
    (BimoduleTensor.composeMap R E C D (𝟙 U) b)
  have ha : z ≫ A1.hom = A0.hom ≫ j :=
    dgKernelDerivedInfinity_graph_precomp_square R D C E F b
  have hk : K0.hom ≫ t = j ≫ K1.hom :=
    dgKernelDerivedInfinity_comp_graph_hom_naturality R D C E F b hQ hQ'
  have hc : C0.hom ≫ (dgKernelDerivedFunctorHomFunctor R D E).map a = t ≫ C1.hom :=
    dgKernelDerivedInfinity_targetModel_comparison_square R D C E F q q' a b h
      hF hQ hQ' hq hq'
  exact iso_three_step_square A0 A1 K0 K1 C0 C1 z j t
    ((dgKernelDerivedFunctorHomFunctor R D E).map a) ha hk hc
end SerrePositivity.InfinityCategories
