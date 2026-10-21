module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationRawFactor
/-!
概要：元の指定合成子の raw factor 計算を、元の分解関手の同じ型の等式で表す。
方針：二段前合成と入力切断・射影の厳密な単位関係で型輸送を揃える。
規約：元の合成子と指定比較の値を保つ。使われ方：K-flat 上の通常 tensor 経路との照合。
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
/-- 元の合成子へ raw factor を続けると、同じ分解関手上の raw factor と augmentation になる。 -/
lemma dgModuleResolvedInfinity_compositionIso_rawFactor
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    dgModuleResolvedInfinity_compositionIso R C E K F H hq ≪≫
        dgModuleResolvedInfinity_rawFactorIso R C K (F.comp H) =
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
        ((dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E)).comp H)).precomp
            (dgModuleResolvedInfinity R C E F) ≪≫
        dgModuleResolvedAugmentationRawFactorIso R C E K F H hq := by
  let S := (dgModuleResolvedSourceSectionEquivalence R C E F).hom
  let G := dgNerve.map (dgModuleFunctorResolutionReplacement R C E F)
  let P := dgNerve.map (dgModuleFunctorResolutionSource R C E F)
  let I := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)
  let L := dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))
  let b := dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K (I.comp H)
  let d := dgModuleAugmentationRawFactorCoreIso R C E K F H hq
  have hs : dgModuleResolvedInfinity R C E F = S ≫ G := by
    simpa only [S, G, dgModuleResolvedSourceSectionEquivalence, Category.assoc] using!
      dgModuleResolvedInfinity_eq_section_replacement R C E F
  have hsp : S ≫ P = 𝟙 _ := dgModuleResolvedSourceSection_comp_source R C E F
  have hb : HEq (b.precomp (dgModuleResolvedInfinity R C E F))
      ((b.precomp G).precomp S) :=
    (F2.functorIso_precomp_heq_of_map_eq b hs).trans
      (heq_of_eq (F2.functorIso_precomp_precomp b G S).symm)
  have hf : dgModuleResolvedInfinity R C E F ≫
      dgModuleResolvedInfinity R (SemifreeDGModules R E) K (I.comp H) =
      S ≫ G ≫ dgModuleResolvedInfinity R (SemifreeDGModules R E) K (I.comp H) := by
    rw [hs, Category.assoc]
  have hg : dgModuleResolvedInfinity R C E F ≫ dgNerve.map (I.comp H) ≫ L =
      S ≫ G ≫ dgNerve.map (I.comp H) ≫ L := by rw [hs, Category.assoc]
  have hh : dgNerve.map (F.comp H) ≫ L = S ≫ P ≫ dgNerve.map (F.comp H) ≫ L := by
    rw [← Category.assoc S P, hsp, Category.id_comp]
  have ht := functorIso_trans_heq (b.precomp (dgModuleResolvedInfinity R C E F))
    (dgModuleResolvedAugmentationRawFactorIso R C E K F H hq)
    ((b.precomp G).precomp S) (d.precomp S) hf hg hh hb
    (dgModuleResolvedAugmentationRawFactorIso_heq R C E K F H hq)
  have hw := F2.functorIso_precomp_trans (b.precomp G) d S
  have hc := dgModuleResolvedInfinity_compositionIso_rawFactor_heq R C E K F H hq
  exact eq_of_heq (hc.trans ((heq_of_eq hw).trans ht.symm))
end SerrePositivity.InfinityCategories
