module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatHomSemifreeResolution
public import SerrePositivity.InfinityCategories.Derived.FunctorHomSquareTransport
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
lemma dgRelativeKFlatKernelRestrictionNerveIso_hom_square
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
    (hQ : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D Q)) :
    (dgKernelDerivedFunctorHomFunctor R D E).map f ≫
      (dgRelativeKFlatKernelRestrictionNerveIso R D E
        (BimoduleCategory.underlying R E D Q) hQ).hom =
    (dgRelativeKFlatKernelRestrictionNerveIso R D E
      (BimoduleCategory.underlying R E D P) hP).hom ≫
      (SSet.mapHomotopyCategory ((pre (dgSemifreeToRelativeKFlatNerve R D)).app
        (dgModuleDerivedInfinityCategory R E))).map
          ((SSet.mapHomotopyCategory ((ihom (dgRelativeKFlatModuleNerve R D)).map
            (dgRelativeKFlatResolution R E))).map
              (dgRelativeKFlatKernelBimoduleHom R D E f hP hQ)) := by
  have hp := dgRelativeKFlatKernelNerve_semifree_resolution R D E
    (BimoduleCategory.underlying R E D P) hP
  have hq := dgRelativeKFlatKernelNerve_semifree_resolution R D E
    (BimoduleCategory.underlying R E D Q) hQ
  have erp := functorIso_hom_heq_of_endpoint_heq
    (dgRelativeKFlatKernelRestrictionNerveIso R D E
      (BimoduleCategory.underlying R E D P) hP)
    (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P))) rfl hp
    (dgRelativeKFlatKernelRestrictionNerveIso_heq R D E
      (BimoduleCategory.underlying R E D P) hP)
  have erq := functorIso_hom_heq_of_endpoint_heq
    (dgRelativeKFlatKernelRestrictionNerveIso R D E
      (BimoduleCategory.underlying R E D Q) hQ)
    (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q))) rfl hq
    (dgRelativeKFlatKernelRestrictionNerveIso_heq R D E
      (BimoduleCategory.underlying R E D Q) hQ)
  exact functorHom_two_two_eq_of_heq _ _ _ _ _ _ _ _ rfl rfl hp hq
    (HEq.refl _) erq erp
    (dgRelativeKFlatKernelBimoduleHom_semifree_resolution_heq R D E f hP hQ)
    (dgKernelDerivedFunctorHomFunctor_rawFactor_square R D E f)
end
end SerrePositivity.InfinityCategories
