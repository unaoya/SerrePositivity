module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeActionUnlift
public import SerrePositivity.InfinityCategories.Derived.FunctorHomConjugationPrecomp
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyInputExchange
/-!
概要：指定済みの実出力分解の比較の射を、同じ元の nerve 作用へ照合する。
方針：全関手射の上げ下げと指定逆を保つ共役式を使う。
規約：比較の値を再選択しない。使われ方：導来 kernel の準同型比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
lemma dgModuleResolvedInfinity_rawFactor_target_eq
    (F : DGFunctor R C (RightModule R E)) :
    (dgNerve.map F) ≫ (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule
      R E))) = (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)) ≫
      (dgNerve.map (dgModuleResolutionLiftedInputFunctor R C E F)) ≫
      ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule R E) E (DGFunctor.id
      (RightModule R E))).inv ≫ (dgNerve.map (dgModuleFunctorResolutionReplacement R
      (RightModule R E) E (DGFunctor.id (RightModule R E))))) := by
  have hL := dgModuleResolvedInfinity_eq_section_replacement R (RightModule R E) E (DGFunctor.id
    (RightModule R E))
  have hF := dgModuleResolutionLiftedInputFunctor_up_eq R C E F
  exact (congrArg (fun t => (dgNerve.map F) ≫ t) hL).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ ((dgModuleFunctorResolutionSourceNerveEquivalence R (RightModule
        R E) E (DGFunctor.id (RightModule R E))).inv ≫ (dgNerve.map
        (dgModuleFunctorResolutionReplacement R (RightModule R E) E (DGFunctor.id (RightModule R
        E)))))) hF.symm).trans (Category.assoc _ _ _)))
lemma dgModuleResolvedInfinity_rawFactor_hom_raw_heq (F : DGFunctor R C (RightModule R E)) :
    HEq (dgModuleResolvedInfinity_rawFactorIso R C E F).hom
      ((dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).hom :=
  functorIso_hom_heq_of_endpoint_heq (dgModuleResolvedInfinity_rawFactorIso R C E F)
    ((dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (dgNerve.map
    (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
    (dgModuleResolvedInfinity_eq_section_replacement R C E F)
    (dgModuleResolvedInfinity_rawFactor_target_eq R C E F)
    (dgModuleResolvedInfinity_rawFactorIso_raw_heq R C E F)
lemma dgModuleResolvedInfinity_rawFactor_inv_raw_heq (F : DGFunctor R C (RightModule R E)) :
    HEq (dgModuleResolvedInfinity_rawFactorIso R C E F).inv
      ((dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).inv :=
  functorIso_inv_heq_of_endpoint_heq (dgModuleResolvedInfinity_rawFactorIso R C E F)
    ((dgModuleOutputResolution_rawFactorPrecompIso R C E F).precomp (dgNerve.map
    (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)))
    (dgModuleResolvedInfinity_eq_section_replacement R C E F)
    (dgModuleResolvedInfinity_rawFactor_target_eq R C E F)
    (dgModuleResolvedInfinity_rawFactorIso_raw_heq R C E F)
end SerrePositivity.InfinityCategories
