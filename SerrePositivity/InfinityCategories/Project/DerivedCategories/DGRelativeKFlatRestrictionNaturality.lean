module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatBimoduleSemifreeResolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelRestrictionNerve
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSquareTransport
/-!
概要：元の半自由制限比較 ρ と双加群同型の作用の自然性四角形を証明する。
方針：同じ raw factor の共役四角形を、全端点と指定値を保って輸送する。
規約：原 Hom の平坦性を追加しない。使われ方：K-flat 比較 ξ の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ双加群同型の作用に対し、元の半自由制限比較 ρ は全関手同型として自然。 -/
lemma dgRelativeKFlatKernelRestrictionNerveIso_bimodule_square
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (e : P ≅ Q)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R D E e ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q) hQ =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) hP ≪≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso R D E e hP hQ).postcomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E)).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_two_two_transport _ _ _ _ _ _ _ _ rfl rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_semifree_resolution R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_semifree_resolution R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D Q) hQ)
    (HEq.refl _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso_heq R D E (BimoduleCategory.underlying R E D Q) hQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelRestrictionNerveIso_heq R D E (BimoduleCategory.underlying R E D P) hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelBimoduleIso_semifree_resolution_heq R D E e hP hQ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso_rawFactor_square R D E e)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
