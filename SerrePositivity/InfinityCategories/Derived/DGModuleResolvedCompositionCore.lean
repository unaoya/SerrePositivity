module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedComposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecompCompositionEq
/-!
概要：実分解圏上の指定三比較の経路を構成する。
方針：元の両射影と同じ augmentation 比較を保ち、入力切断前の経路を明示する。
規約：元の合成子の定義を変更しない。使われ方：raw factor と augmentation による計算。
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
/-- 入力切断を前合成する前の、元の指定三比較の全関手経路。 -/
def dgModuleResolvedCompositionCoreIso
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    FunctorIso
      (dgNerve.map (dgModuleFunctorResolutionReplacement R C E F) ≫
        dgModuleResolvedInfinity R (SemifreeDGModules R E) K
          ((dgFullSubcategoryInclusion R (RightModule R E)
            (dgModuleSemifreeProperty R E)).comp H))
      (dgNerve.map (dgModuleFunctorResolutionSource R C E F) ≫
        dgModuleResolvedInfinity R C K (F.comp H)) := by
  let T := DGModuleFunctorResolutionObject R C E F
  let I := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)
  let P := dgModuleFunctorResolutionSource R C E F
  let G := dgModuleFunctorResolutionReplacement R C E F
  have hc₀ : (dgModuleAugmentationSource R C E F).comp H = G.comp (I.comp H) := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [dgModuleAugmentationSource, EnrichedFunctor.comp_map,
      Category.assoc, eqToHom_refl, Category.comp_id]
  have hc₁ : (dgModuleAugmentationTarget R C E F).comp H = P.comp (F.comp H) := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [dgModuleAugmentationTarget, EnrichedFunctor.comp_map,
      Category.assoc, eqToHom_refl, Category.comp_id]
  have e := dgModuleAugmentationResolvedComparisonIso R C E K F H hq
  rw [hc₀, hc₁] at e
  have a : FunctorIso
      (dgNerve.map G ≫ dgModuleResolvedInfinity R (SemifreeDGModules R E) K (I.comp H))
      (dgNerve.map P ≫ dgModuleResolvedInfinity R C K (F.comp H)) :=
    (dgModuleResolvedInfinity_precompIso R T (SemifreeDGModules R E) K G
    (I.comp H)).symm ≪≫ e ≪≫
      dgModuleResolvedInfinity_precompIso R T C K P (F.comp H)
  exact a
end SerrePositivity.InfinityCategories
