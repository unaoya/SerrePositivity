module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationRawFactor
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationRawFactorSectionHom
/-!
概要：元の分解関手上の指定 augmentation 比較の射を、同じ全単体ホモトピーへ同定する。
方針：二射影の表示を元の augmentation へ戻し、指定同型の射の型輸送を保つ。
規約：同じ全関手射の一致を証明する。使われ方：元の合成子の通常後続像の照合。
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
/-- 元の型に揃えた指定同型の射は、同じ augmentation の通常後続像の全関手射である。 -/
lemma dgModuleResolvedAugmentationRawFactorIso_hom_heq
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    HEq (dgModuleResolvedAugmentationRawFactorIso R C E K F H hq).hom
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (dgModuleResolvedAugmentationHomotopy R C E F)
          (dgNerve.map H ≫ dgModuleResolvedInfinity R (RightModule R K) K
            (DGFunctor.id (RightModule R K)))))) := by
  let S := (dgModuleResolvedSourceSectionEquivalence R C E F).hom
  let G := dgNerve.map (dgModuleFunctorResolutionReplacement R C E F)
  let P := dgNerve.map (dgModuleFunctorResolutionSource R C E F)
  let I := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)
  let L := dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))
  let a := dgModuleResolvedAugmentationRawFactorIso R C E K F H hq
  let b := dgModuleAugmentationRawFactorCoreIso R C E K F H hq
  let d := dgModuleAugmentationRawFactorIso R C E K F H hq
  have hs : dgModuleResolvedInfinity R C E F = S ≫ G := by
    simpa only [S, G, dgModuleResolvedSourceSectionEquivalence, Category.assoc] using!
      dgModuleResolvedInfinity_eq_section_replacement R C E F
  have hsp : S ≫ P = 𝟙 _ := dgModuleResolvedSourceSection_comp_source R C E F
  have hf : dgModuleResolvedInfinity R C E F ≫ dgNerve.map (I.comp H) ≫ L =
      S ≫ G ≫ dgNerve.map (I.comp H) ≫ L := by rw [hs, Category.assoc]
  have hg : dgNerve.map (F.comp H) ≫ L = S ≫ P ≫ dgNerve.map (F.comp H) ≫ L := by
    rw [← Category.assoc S P, hsp, Category.id_comp]
  have h1 := functorIso_hom_heq a (b.precomp S) hf hg
    (dgModuleResolvedAugmentationRawFactorIso_heq R C E K F H hq)
  have hsrc : dgNerve.map (dgModuleAugmentationSource R C E F) ≫ dgNerve.map H ≫ L =
      G ≫ dgNerve.map (I.comp H) ≫ L := by
    simp only [G, I, dgModuleAugmentationSource, dgNerve.map_comp, Category.assoc]
  have htgt : dgNerve.map (dgModuleAugmentationTarget R C E F) ≫ dgNerve.map H ≫ L =
      P ≫ dgNerve.map (F.comp H) ≫ L := by
    simp only [P, dgModuleAugmentationTarget, dgNerve.map_comp, Category.assoc]
  have hb := F2.functorIso_precomp_heq_of_heq d b hsrc htgt
    (dgModuleAugmentationRawFactorCoreIso_heq R C E K F H hq) S
  have h2 := functorIso_hom_heq (b.precomp S) (d.precomp S)
    (congrArg (fun m => S ≫ m) hsrc.symm) (congrArg (fun m => S ≫ m) htgt.symm) hb
  exact h1.trans (h2.trans (dgModuleAugmentationRawFactorIso_section_hom_heq R C E K F H hq))
end SerrePositivity.InfinityCategories
