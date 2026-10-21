module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawTransport
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationRawFactor
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSectionEquivalence
/-!
概要：入力切断上の指定 raw factor 比較の射を、元の augmentation の全単体像へ同定する。
方針：同じ円柱の前合成・後合成を一般補題で移す。
規約：生の augmentation の可逆性は不要。使われ方：元の合成子の通常後続経路の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R C (RightModule R E))
  (H : DGFunctor R (RightModule R E) (RightModule R K))
/-- 同じ入力切断に制限した raw factor 比較の射は、元の augmentation の通常後続像。 -/
lemma dgModuleAugmentationRawFactorIso_section_hom_heq
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    HEq ((dgModuleAugmentationRawFactorIso R C E K F H hq).precomp
      (dgModuleResolvedSourceSectionEquivalence R C E F).hom).hom
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (dgModuleResolvedAugmentationHomotopy R C E F)
          (dgNerve.map H ≫ dgModuleResolvedInfinity R (RightModule R K) K
            (DGFunctor.id (RightModule R K)))))) := by
  let S := (dgModuleResolvedSourceSectionEquivalence R C E F).hom
  let q := dgNerve.map H ≫ dgModuleResolvedInfinity R (RightModule R K) K
    (DGFunctor.id (RightModule R K))
  let A := functorHomotopyPostcomp (dgModuleAugmentationUnliftedHomotopy R C E F) q
  have hp := functorIso_precomp_hom_of_homotopy
    (dgModuleAugmentationRawFactorIso R C E K F H hq) A S
    (dgModuleAugmentationRawFactorIso_hom R C E K F H hq)
  have hh : (functorHomotopyPrecomp A S).h =
      (functorHomotopyPostcomp (dgModuleResolvedAugmentationHomotopy R C E F) q).h := by
    simp only [A, S, functorHomotopyPrecomp, functorHomotopyPostcomp,
      dgModuleResolvedAugmentationHomotopy, dgModuleResolvedSourceSectionEquivalence,
      Category.assoc]
  exact (heq_of_eq hp).trans (functorHomotopyHom_heq_of_raw_eq _ _ hh)
end SerrePositivity.InfinityCategories
