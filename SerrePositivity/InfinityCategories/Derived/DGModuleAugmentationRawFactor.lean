module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPostcompConjugate
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationResolvedIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorNaturality
/-!
概要：同じ実 augmentation の可逆な像を、元の raw factor 比較で通常出力作用へ移す。
方針：指定後続比較で共役し、その順方向射を元の全単体ホモトピーの像へ回収する。
規約：生の augmentation の可逆性は不要。使われ方：指定導来合成子の計算式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R C (RightModule R E))
  (H : DGFunctor R (RightModule R E) (RightModule R K))
/-- 同じ augmentation を通常後続作用と指定出力分解で写す、指定 raw factor による比較。 -/
def dgModuleAugmentationRawFactorIso
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    FunctorIso
      (dgNerve.map (dgModuleAugmentationSource R C E F) ≫ dgNerve.map H ≫
        dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)))
      (dgNerve.map (dgModuleAugmentationTarget R C E F) ≫ dgNerve.map H ≫
        dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))) :=
  functorIsoPostcompConjugate (dgModuleAugmentationResolvedIso R C E K F H hq)
    (dgModuleResolvedInfinity_rawFactorIso R (RightModule R E) K H)
/-- 指定 raw factor による比較は、元の全単体 augmentation の通常後続像を回収する。 -/
lemma dgModuleAugmentationRawFactorIso_hom
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    (dgModuleAugmentationRawFactorIso R C E K F H hq).hom =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (dgModuleAugmentationUnliftedHomotopy R C E F)
          (dgNerve.map H ≫ dgModuleResolvedInfinity R (RightModule R K) K
            (DGFunctor.id (RightModule R K))))) :=
  functorIsoPostcompConjugate_hom (dgModuleAugmentationUnliftedHomotopy R C E F)
    (dgModuleAugmentationResolvedIso R C E K F H hq)
    (dgModuleResolvedInfinity_rawFactorIso R (RightModule R E) K H) rfl
end SerrePositivity.InfinityCategories
