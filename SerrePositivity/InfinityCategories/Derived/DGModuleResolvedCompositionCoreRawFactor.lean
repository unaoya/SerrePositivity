module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationRawFactorCore
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactorTransport
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedCompositionCore
/-!
概要：入力切断前の指定三項経路を、通常後続像との比較で計算する。
方針：augmentation の raw factor 正方形を二射影の入力自然性で囲み、比較を相殺する。
規約：同じ指定経路と全関手変換を保つ。使われ方：元の合成子の経路照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
private lemma mp_heq {α β : Sort u} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
  cases h
  rfl
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R C (RightModule R E))
  (H : DGFunctor R (RightModule R E) (RightModule R K))
/-- 指定三項経路へ raw factor を続けた経路は、replacement 側の比較と通常後続像に等しい。 -/
lemma dgModuleResolvedCompositionCoreIso_rawFactor
    (hq : ∀ X : DGModuleFunctorResolutionObject R C E F,
      moduleQuasiIso R K (H.onClosed.map X.augmentation)) :
    dgModuleResolvedCompositionCoreIso R C E K F H hq ≪≫
        (dgModuleResolvedInfinity_rawFactorIso R C K (F.comp H)).precomp
          (dgNerve.map (dgModuleFunctorResolutionSource R C E F)) =
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
        ((dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E)).comp H)).precomp
            (dgNerve.map (dgModuleFunctorResolutionReplacement R C E F)) ≪≫
        dgModuleAugmentationRawFactorCoreIso R C E K F H hq := by
  dsimp -zeta only [dgModuleResolvedCompositionCoreIso]
  extract_lets T I P G hc0 hc1 e a
  let pG := dgModuleResolvedInfinity_precompIso R T (SemifreeDGModules R E) K G (I.comp H)
  let pP := dgModuleResolvedInfinity_precompIso R T C K P (F.comp H)
  let bG := (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
    (I.comp H)).precomp (dgNerve.map G)
  let bP := (dgModuleResolvedInfinity_rawFactorIso R C K (F.comp H)).precomp (dgNerve.map P)
  let A := dgModuleAugmentationSource R C E F
  let B := dgModuleAugmentationTarget R C E F
  let L := dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K))
  let nA := F2.functorIsoOfEq (dgModuleResolvedInfinity_rawFactorIso R T K (A.comp H)) rfl
    (congrArg (fun m => m ≫ L) (dgNerve.map_comp A H))
  let nB := F2.functorIsoOfEq (dgModuleResolvedInfinity_rawFactorIso R T K (B.comp H)) rfl
    (congrArg (fun m => m ≫ L) (dgNerve.map_comp B H))
  let d := dgModuleAugmentationRawFactorIso R C E K F H hq
  let d' := dgModuleAugmentationRawFactorCoreIso R C E K F H hq
  let e0 : FunctorIso (dgModuleResolvedInfinity R T K (G.comp (I.comp H)))
      (dgModuleResolvedInfinity R T K (P.comp (F.comp H))) :=
    Eq.mp (congrArg (fun Z : DGFunctor R T (RightModule R K) =>
      FunctorIso (dgModuleResolvedInfinity R T K (G.comp (I.comp H)))
        (dgModuleResolvedInfinity R T K Z)) hc1)
      (Eq.mp (congrArg (fun Z : DGFunctor R T (RightModule R K) =>
        FunctorIso (dgModuleResolvedInfinity R T K Z)
          (dgModuleResolvedInfinity R T K (B.comp H))) hc0) e)
  have he0 : HEq e0 e := by
    dsimp only [e0]
    exact (mp_heq _ _).trans (mp_heq _ e)
  have hnA : HEq nA (pG ≪≫ bG) := by
    have h1 := F2.functorIsoOfEq_heq
      (dgModuleResolvedInfinity_rawFactorIso R T K (A.comp H)) rfl
      (congrArg (fun m => m ≫ L) (dgNerve.map_comp A H))
    have h2 := dgModuleResolvedInfinity_rawFactorIso_heq_of_output_eq R T K hc0
    have h3 := dgModuleResolvedInfinity_rawFactorIso_precomp_heq R T
      (SemifreeDGModules R E) K G (I.comp H)
    exact h1.trans (h2.trans h3)
  have hnB : HEq nB (pP ≪≫ bP) := by
    have h1 := F2.functorIsoOfEq_heq
      (dgModuleResolvedInfinity_rawFactorIso R T K (B.comp H)) rfl
      (congrArg (fun m => m ≫ L) (dgNerve.map_comp B H))
    have h2 := dgModuleResolvedInfinity_rawFactorIso_heq_of_output_eq R T K hc1
    have h3 := dgModuleResolvedInfinity_rawFactorIso_precomp_heq R T C K P (F.comp H)
    exact h1.trans (h2.trans h3)
  have hsrc : dgNerve.map A ≫ dgNerve.map H ≫ L =
      dgNerve.map G ≫ dgNerve.map (I.comp H) ≫ L := by
    simp only [A, I, G, dgModuleAugmentationSource, dgNerve.map_comp, Category.assoc]
  have htgt : dgNerve.map B ≫ dgNerve.map H ≫ L =
      dgNerve.map P ≫ dgNerve.map (F.comp H) ≫ L := by
    simp only [B, P, dgModuleAugmentationTarget, dgNerve.map_comp, Category.assoc]
  have hl := functorIso_trans_heq e nB e0 (pP ≪≫ bP)
    (congrArg (dgModuleResolvedInfinity R T K) hc0)
    (congrArg (dgModuleResolvedInfinity R T K) hc1) htgt he0.symm hnB
  have hr := functorIso_trans_heq nA d (pG ≪≫ bG) d'
    (congrArg (dgModuleResolvedInfinity R T K) hc0) hsrc htgt hnA
    (dgModuleAugmentationRawFactorCoreIso_heq R C E K F H hq).symm
  have hOld : e ≪≫ nB = nA ≪≫ d :=
    dgModuleAugmentationResolvedComparisonIso_rawFactor R C E K F H hq
  have hsquare : e0 ≪≫ (pP ≪≫ bP) = (pG ≪≫ bG) ≪≫ d' :=
    eq_of_heq (hl.symm.trans ((heq_of_eq hOld).trans hr))
  change (pG.symm ≪≫ e0 ≪≫ pP) ≪≫ bP = bG ≪≫ d'
  simp only [Iso.trans_assoc] at hsquare ⊢
  rw [hsquare, Iso.symm_self_id_assoc]
end SerrePositivity.InfinityCategories
