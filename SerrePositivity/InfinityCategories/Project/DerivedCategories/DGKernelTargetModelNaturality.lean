module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTargetModelComparisonSquares
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedGraphCompositionNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.IsoThreeStepSquare
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
lemma dgKernelDerivedInfinity_targetModelIso_naturality
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
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso R D C E F P Q q hF hQ hq).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q'))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C E F)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D C).map b) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso R D C E F P' Q' q' hF hQ' hq').hom := by
  let U := _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F)
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q)
  let L' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D C (BimoduleCategory.underlying R C D Q')
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R C E (functorGraph R C E F)
  let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C E F
  let x := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D C).map b
  let j := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp L L' G x
  let z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp L L' H x
  let A := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R C E F).symm
  let A0 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp A L
  let A1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp A L'
  let K0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D C E
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q) (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F) hQ
  let K1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D C E
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q') (_root_.SerrePositivity.DifferentialGraded.functorGraph R C E F) hQ'
  let c0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation R D C E F P Q q
  let c1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation R D C E F P' Q' q'
  let hc0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_quasiIso R D C E F P Q q hF hQ hq
  let hc1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_quasiIso R D C E F P' Q' q' hF hQ' hq'
  let C0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E c0 hc0
  let C1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E c1 hc1
  let t := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R E C D (𝟙 U) b)
  have ha : z ≫ A1.hom = A0.hom ≫ j :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graph_precomp_square R D C E F b
  have hk : K0.hom ≫ t = j ≫ K1.hom :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comp_graph_hom_naturality R D C E F b hQ hQ'
  have hc : C0.hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map a = t ≫ C1.hom :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModel_comparison_square R D C E F q q' a b h
      hF hQ hQ' hq hq'
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.iso_three_step_square A0 A1 K0 K1 C0 C1 z j t
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map a) ha hk hc
end SerrePositivity.InfinityCategories.Project.DerivedCategories
