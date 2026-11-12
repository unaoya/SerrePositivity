module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelGraphDiagonalUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedLeftUnitCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTargetModelInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedComparisonCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoUnitTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelSourceRestrictionInfinity
/-!
概要：始域制限と出力模型の対角比較を指定導来単位へ接続する。
方針：実 graph 比較、元の K-flat 単位三角式と同じ交換則を使う。
規約：比較を選び直さない。使われ方：元の canonical cell 単位の整合性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (C D : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D)
lemma dgKernelDerivedInfinity_sourceRestrictionIso_diagonal :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso R C D D F (Bimodule.diagonal R D) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R C D F =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C D F) := by
  have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_left_unit R C D (functorGraph R C D F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGraph_rightRelativeKFlat R C D F)
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_unit_target_transport
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C D F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R C D (functorGraph R C D F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R C D F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceGraphIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelSourceGraphBimoduleIso_diagonal,
    Iso.trans_assoc, ← hu] using! ht
lemma dgKernelDerivedInfinity_targetModelIso_diagonal (hF : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso R C C D F
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D C (F.comp (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)))
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R C C (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R C))
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonalRestrictionMap R C D F) hF
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R C)
      ((_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonalRestrictionMap_quasiIso_iff R C D F).2 hF.1) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R C D F =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R C).postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C D F) := by
  have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_right_unit R C D (functorGraph R C D F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGraph_rightRelativeKFlat R C D F)
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_of_iso R C D
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R D C (_root_.SerrePositivity.DifferentialGraded.functorGraph R C D F))
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_unit_source_transport
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R C D F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R C D (functorGraph R C D F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R C D F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R C C (Bimodule.diagonal R C))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R C)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModelAugmentation_diagonal, hc, Iso.trans_assoc, ← hu] using! ht
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
