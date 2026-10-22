module
public import SerrePositivity.InfinityCategories.Derived.DGKernelGraphDiagonalUnit
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedLeftUnitCoherence
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelInfinity
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedComparisonCoherence
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoUnitTransport
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceRestrictionInfinity
/-!
概要：始域制限と出力模型の対角比較を指定導来単位へ接続する。
方針：実 graph 比較、元の K-flat 単位三角式と同じ交換則を使う。
規約：比較を選び直さない。使われ方：元の canonical cell 単位の整合性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  (F : DGFunctor R C D)
lemma dgKernelDerivedInfinity_sourceRestrictionIso_diagonal :
    dgKernelDerivedInfinity_sourceRestrictionIso R C D D F (Bimodule.diagonal R D) ≪≫
      dgKernelDerivedInfinity_graphIso R C D F =
    (dgKernelDerivedInfinity_identityIso R D).precomp (dgModuleExtensionInfinity R C D F) := by
  have hu := dgKernelDerivedInfinity_compIso_left_unit R C D (functorGraph R C D F)
    (dgFunctorGraph_rightRelativeKFlat R C D F)
  have ht := functorIso_unit_target_transport
    (dgModuleExtensionInfinity R C D F)
    (dgKernelDerivedInfinity R C D (functorGraph R C D F))
    (dgKernelDerivedInfinity_graphIso R C D F)
    (dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
    (dgKernelDerivedInfinity_identityIso R D)
  simpa only [dgKernelDerivedInfinity_sourceRestrictionIso,
    dgKernelDerivedInfinity_sourceGraphIso, dgKernelSourceGraphBimoduleIso_diagonal,
    Iso.trans_assoc, ← hu] using! ht
lemma dgKernelDerivedInfinity_targetModelIso_diagonal (hF : QuasiEquivalence F) :
    dgKernelDerivedInfinity_targetModelIso R C C D F
      (BimoduleCategory.of R D C (F.comp (Bimodule.diagonal R D)))
      (BimoduleCategory.of R C C (Bimodule.diagonal R C))
      (Bimodule.diagonalRestrictionMap R C D F) hF
      (Bimodule.diagonal_rightRelativeKFlat R C)
      ((Bimodule.diagonalRestrictionMap_quasiIso_iff R C D F).2 hF.1) ≪≫
      dgKernelDerivedInfinity_graphIso R C D F =
    (dgKernelDerivedInfinity_identityIso R C).postcomp (dgModuleExtensionInfinity R C D F) := by
  have hu := dgKernelDerivedInfinity_compIso_right_unit R C D (functorGraph R C D F)
    (dgFunctorGraph_rightRelativeKFlat R C D F)
  have hc := dgKernelDerivedInfinity_comparison_of_iso R C D
    (BimoduleTensor.rightBimoduleUnitIso R D C (functorGraph R C D F))
  have ht := functorIso_unit_source_transport
    (dgModuleExtensionInfinity R C D F)
    (dgKernelDerivedInfinity R C D (functorGraph R C D F))
    (dgKernelDerivedInfinity_graphIso R C D F)
    (dgKernelDerivedInfinity R C C (Bimodule.diagonal R C))
    (dgKernelDerivedInfinity_identityIso R C)
  simpa only [dgKernelDerivedInfinity_targetModelIso,
    dgKernelTargetModelAugmentation_diagonal, hc, Iso.trans_assoc, ← hu] using! ht
end
end SerrePositivity.InfinityCategories
