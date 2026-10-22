module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationResolvedIso
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyPostcompHom
/-!
概要：元の augmentation 比較の射は、後続作用間の任意の全関手射に自然である。
方針：同じ全単体ホモトピーの後合成の射を回収し、型付き交換則を使う。
規約：後続作用の平坦性・射の可逆性を要求しない。使われ方：元の κ の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R C (RightModule R E))
lemma dgModuleAugmentationResolvedIso_hom
    (H : DGFunctor R (RightModule R E) (RightModule R K))
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    (dgModuleAugmentationResolvedIso R C E K F H hq).hom =
    functorHomPostcomp (dgNerve.map (dgModuleAugmentationSource R C E F))
      (dgNerve.map (dgModuleAugmentationTarget R C E F))
      (dgModuleResolvedInfinity R (RightModule R E) K H)
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgModuleAugmentationUnliftedHomotopy R C E F))) :=
  functorIsoOfPointwiseInvertibleHomotopy_postcomp_hom _ _ _
lemma dgModuleAugmentationResolvedIso_hom_naturality
    (H0 H1 : DGFunctor R (RightModule R E) (RightModule R K))
    (hq0 : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H0.onClosed.map X.augmentation))
    (hq1 : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H1.onClosed.map X.augmentation))
    (d : FunctorHom (dgModuleResolvedInfinity R (RightModule R E) K H0)
      (dgModuleResolvedInfinity R (RightModule R E) K H1)) :
    (dgModuleAugmentationResolvedIso R C E K F H0 hq0).hom ≫
      functorHomPrecomp (dgModuleResolvedInfinity R (RightModule R E) K H0)
        (dgModuleResolvedInfinity R (RightModule R E) K H1)
        (dgNerve.map (dgModuleAugmentationTarget R C E F)) d =
    functorHomPrecomp (dgModuleResolvedInfinity R (RightModule R E) K H0)
        (dgModuleResolvedInfinity R (RightModule R E) K H1)
        (dgNerve.map (dgModuleAugmentationSource R C E F)) d ≫
      (dgModuleAugmentationResolvedIso R C E K F H1 hq1).hom := by
  rw [dgModuleAugmentationResolvedIso_hom, dgModuleAugmentationResolvedIso_hom]
  exact functorHom_whisker_exchange_typed _ d
end SerrePositivity.InfinityCategories
