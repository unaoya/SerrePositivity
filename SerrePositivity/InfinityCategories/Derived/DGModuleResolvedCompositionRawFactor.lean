module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedCompositionExtraction
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedCompositionCoreRawFactor
/-!
概要：元の指定合成子へ raw factor を続けた経路を計算する。
方針：入力切断前の計算式を同じ切断で制限し、射影との厳密な単位関係を使う。
規約：元の合成子と全関手変換の指定値を保つ。使われ方：K-flat 上の二経路の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet DifferentialGraded DGNerve
private lemma functorIso_precomp_identity {X Y : SSet.{u}} {f g : X ⟶ Y} (e : FunctorIso f g) :
    e.precomp (𝟙 X) = e := by
  rw [F2.functorIso_precomp_eq_mapIso]
  have h : SSet.mapHomotopyCategory ((pre (𝟙 X)).app Y) =
      𝟭 (SSet.HomotopyCategory ((ihom X).obj Y)) := by
    rw [pre_id, NatTrans.id_app]
    change (hoFunctor.map (𝟙 ((ihom X).obj Y))).toFunctor = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  exact eq_of_heq (F2.mapIso_heq_of_functor_eq h e)

variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R C (RightModule R E))
  (H : DGFunctor R (RightModule R E) (RightModule R K))
/-- 元の指定合成子の raw factor 計算は、同じ augmentation の通常後続像への経路に等しい。 -/
lemma dgModuleResolvedInfinity_compositionIso_rawFactor_heq
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    HEq (dgModuleResolvedInfinity_compositionIso R C E K F H hq ≪≫
        dgModuleResolvedInfinity_rawFactorIso R C K (F.comp H))
      (FunctorIso.precomp ((dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
        ((dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E)).comp H)).precomp
            (dgNerve.map (dgModuleFunctorResolutionReplacement R C E F)) ≪≫
        dgModuleAugmentationRawFactorCoreIso R C E K F H hq)
          (dgModuleResolvedSourceSectionEquivalence R C E F).hom) := by
  let S := (dgModuleResolvedSourceSectionEquivalence R C E F).hom
  let P := dgNerve.map (dgModuleFunctorResolutionSource R C E F)
  let G := dgNerve.map (dgModuleFunctorResolutionReplacement R C E F)
  let b := dgModuleResolvedInfinity_rawFactorIso R C K (F.comp H)
  let a := dgModuleResolvedCompositionCoreIso R C E K F H hq
  have hsp : S ≫ P = 𝟙 _ := dgModuleResolvedSourceSection_comp_source R C E F
  have hs : dgModuleResolvedInfinity R C E F = S ≫ G := by
    simpa only [S, G, dgModuleResolvedSourceSectionEquivalence, Category.assoc] using!
      dgModuleResolvedInfinity_eq_section_replacement R C E F
  have hd : HEq b ((b.precomp P).precomp S) := by
    have h1 := F2.functorIso_precomp_precomp b P S
    have h2 := F2.functorIso_precomp_heq_of_map_eq b hsp
    exact ((heq_of_eq h1).trans (h2.trans (heq_of_eq (functorIso_precomp_identity b)))).symm
  have hf : dgModuleResolvedInfinity R C E F ≫
      dgModuleResolvedInfinity R (SemifreeDGModules R E) K
        ((dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E)).comp H) =
      S ≫ G ≫ dgModuleResolvedInfinity R (SemifreeDGModules R E) K
        ((dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E)).comp H) := by rw [hs, Category.assoc]
  have hg : dgModuleResolvedInfinity R C K (F.comp H) =
      S ≫ P ≫ dgModuleResolvedInfinity R C K (F.comp H) := by
    rw [← Category.assoc, hsp, Category.id_comp]
  have hh : dgNerve.map (F.comp H) ≫
      dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)) =
      S ≫ P ≫ dgNerve.map (F.comp H) ≫
      dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)) := by
    rw [← Category.assoc S P, hsp, Category.id_comp]
  have ht := functorIso_trans_heq
    (dgModuleResolvedInfinity_compositionIso R C E K F H hq) b
    (a.precomp S) ((b.precomp P).precomp S) hf hg hh
    (dgModuleResolvedInfinity_compositionIso_core_heq R C E K F H hq) hd
  have hw := F2.functorIso_precomp_trans a (b.precomp P) S
  have hc := congrArg (fun i => FunctorIso.precomp i S)
    (dgModuleResolvedCompositionCoreIso_rawFactor R C E K F H hq)
  exact ht.trans ((heq_of_eq hw).symm.trans (heq_of_eq hc))
end SerrePositivity.InfinityCategories
