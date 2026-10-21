module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationResolvedIso
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSectionEquivalence
/-!
概要：同じ全 augmentation ホモトピーで、二段の出力分解を一段の実合成へ比較する。
方針：元の指定切断・augmentation と、全単体上の関手比較を使う。
規約：元の入力 Hom の平坦性・出力の射影性を仮定しない。
使われ方：一般 kernel の導来合成とその模型移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R C (RightModule R E))
  (H : DGFunctor R (RightModule R E) (RightModule R K))
/-- augmentation の指定後続像が準同型なら、二段の実出力分解は通常合成の実出力分解と同型。 -/
def dgModuleResolvedInfinity_compositionIso
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    FunctorIso
      (dgModuleResolvedInfinity R C E F ≫
        dgModuleResolvedInfinity R (SemifreeDGModules R E) K
          ((dgFullSubcategoryInclusion R (RightModule R E)
            (dgModuleSemifreeProperty R E)).comp H))
      (dgModuleResolvedInfinity R C K (F.comp H)) := by
  let T := DGModuleFunctorResolutionObject R C E F
  let I := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)
  let P := dgModuleFunctorResolutionSource R C E F
  let G := dgModuleFunctorResolutionReplacement R C E F
  let S := (dgModuleResolvedSourceSectionEquivalence R C E F).hom
  have hs : dgModuleResolvedInfinity R C E F = S ≫ dgNerve.map G := by
    simpa only [S, dgModuleResolvedSourceSectionEquivalence, Category.assoc] using!
      dgModuleResolvedInfinity_eq_section_replacement R C E F
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
  have hsp : S ≫ dgNerve.map P = 𝟙 _ :=
    dgModuleResolvedSourceSection_comp_source R C E F
  have q := a.precomp S
  rw [hs]
  simpa only [Category.assoc, ← Category.assoc S (dgNerve.map P), hsp,
    Category.id_comp] using! q
end SerrePositivity.InfinityCategories
