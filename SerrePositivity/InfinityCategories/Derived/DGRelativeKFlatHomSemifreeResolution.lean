module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedHomRawFactor
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelBimoduleHom
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelRestrictionNerve
public import SerrePositivity.InfinityCategories.Derived.FunctorHomLiftedRestrictionResolution
/-!
概要：指定された全関手射の制限と比較を、元の値を保って照合する。
方針：同じ端点・全関手圏の作用・実包含後の一致を使う。
規約：射の可逆性と追加の平坦性は不要。使われ方：ξ と κ の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
lemma dgRelativeKFlatKernelBimoduleHom_semifree_resolution_heq
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    HEq ((SSet.mapHomotopyCategory ((pre (dgSemifreeToRelativeKFlatNerve R D)).app
      (dgModuleDerivedInfinityCategory R E))).map
        ((SSet.mapHomotopyCategory ((ihom (dgRelativeKFlatModuleNerve R D)).map
          (dgRelativeKFlatResolution R E))).map
            (dgRelativeKFlatKernelBimoduleHom R D E f hP hQ)))
      ((dgKernelResolvedRawFunctorHomFunctor R D E).map f) := by
  exact functorHom_lifted_restriction_resolution_heq
    (dgRelativeKFlatKernelBimoduleHom R D E f hP hQ)
    ((dgKernelTensorFunctorHomFunctor R D E).map f)
    (dgRelativeKFlatModuleInclusion R D) (dgRelativeKFlatModuleInclusion R E)
    (dgSemifreeToRelativeKFlatNerve R D)
    (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
      (dgModuleSemifreeProperty R D)))
    (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
    (dgRelativeKFlatKernelNerve_inclusion R D E
      (BimoduleCategory.underlying R E D P) hP).symm
    (dgRelativeKFlatKernelNerve_inclusion R D E
      (BimoduleCategory.underlying R E D Q) hQ).symm
    (dgRelativeKFlatKernelBimoduleHom_inclusion_heq R D E f hP hQ)
    (dgSemifreeToRelativeKFlatNerve_inclusion R D)
end
end SerrePositivity.InfinityCategories
