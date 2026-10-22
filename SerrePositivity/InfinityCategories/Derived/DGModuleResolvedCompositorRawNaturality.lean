module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationHomNaturality
public import SerrePositivity.InfinityCategories.Derived.IsoRawFactorSquare
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPrecompNaturalitySquare
/-!
概要：同じ分解・augmentation・通常比較の raw 四角形から元の合成比較の自然性を得る。
方針：任意の dg 加群値関手について三段経路を接続し、指定 raw factor を相殺する。
規約：比較を選び直さず追加の平坦性を要求しない。使われ方：元の κ の右変数自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (A : Type (max (u + 1) v)) [DGCategory R A]
  (E K : Type v) [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
  (F : DGFunctor R A (RightModule R E))
  (H0 H1 : DGFunctor R (RightModule R E) (RightModule R K))
  (G0 G1 : DGFunctor R A (RightModule R K))
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E)
  (dgModuleSemifreeProperty R E)
local notation "L" => dgModuleResolvedInfinity R (RightModule R K) K
  (DGFunctor.id (RightModule R K))
local notation "U0" => dgModuleResolvedInfinity R (SemifreeDGModules R E) K (DGFunctor.comp I H0)
local notation "U1" => dgModuleResolvedInfinity R (SemifreeDGModules R E) K (DGFunctor.comp I H1)
local notation "V0" => dgModuleResolvedInfinity R A K G0
local notation "V1" => dgModuleResolvedInfinity R A K G1
local notation "J" => dgModuleResolvedInfinity R A E F
local notation "r0" => dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
  (DGFunctor.comp I H0)
local notation "r1" => dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
  (DGFunctor.comp I H1)
local notation "t0" => dgModuleResolvedInfinity_rawFactorIso R A K G0
local notation "t1" => dgModuleResolvedInfinity_rawFactorIso R A K G1
lemma dgModuleResolved_compositor_hom_naturality_of_raw
    (hq0 : ∀ X : DGModuleFunctorResolutionObject R A E F,
      moduleQuasiIso R K (H0.onClosed.map X.augmentation))
    (hq1 : ∀ X : DGModuleFunctorResolutionObject R A E F,
      moduleQuasiIso R K (H1.onClosed.map X.augmentation))
    (c0 : FunctorIso (dgNerve.map (F.comp H0)) (dgNerve.map G0))
    (c1 : FunctorIso (dgNerve.map (F.comp H1)) (dgNerve.map G1))
    (k0 : FunctorIso (J ≫ U0) V0) (k1 : FunctorIso (J ≫ U1) V1)
    (d : FunctorHom (dgNerve.map H0 ≫ L) (dgNerve.map H1 ≫ L))
    (a : FunctorHom U0 U1) (b : FunctorHom V0 V1)
    (e : FunctorHom (dgNerve.map G0 ≫ L) (dgNerve.map G1 ≫ L))
    (ha : (r0).hom ≫
        dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) I H0 H1 d =
      a ≫ (r1).hom)
    (ht : (t0).hom ≫ e = b ≫ (t1).hom)
    (hc : (c0.postcomp L).hom ≫ e =
      dgModuleRawOutputPrecompHom R E K A F H0 H1 d ≫ (c1.postcomp L).hom)
    (hk0 : k0.hom ≫ (t0).hom = ((r0).precomp J).hom ≫
      (dgModuleResolvedAugmentationRawFactorIso R A E K F H0 hq0).hom ≫
        (c0.postcomp L).hom)
    (hk1 : k1.hom ≫ (t1).hom = ((r1).precomp J).hom ≫
      (dgModuleResolvedAugmentationRawFactorIso R A E K F H1 hq1).hom ≫
        (c1.postcomp L).hom) :
    k0.hom ≫ b = functorHomPrecomp U0 U1 J a ≫ k1.hom := by
  have hA := functorHomPrecomp_iso_square_forward r0 r1 a
    (dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) I H0 H1 d) J ha
  have hB := dgModuleResolvedAugmentationRawFactorIso_hom_naturality
    R E K A F H0 H1 hq0 hq1 d
  exact iso_compositor_square_of_three_step_raw k0 k1 t0 t1
    ((r0).precomp J) ((r1).precomp J)
    (dgModuleResolvedAugmentationRawFactorIso R A E K F H0 hq0)
    (dgModuleResolvedAugmentationRawFactorIso R A E K F H1 hq1)
    (c0.postcomp L) (c1.postcomp L) (functorHomPrecomp U0 U1 J a)
    (functorHomPrecomp (dgNerve.map (DGFunctor.comp I H0) ≫ L)
      (dgNerve.map (DGFunctor.comp I H1) ≫ L) J
      (dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) I H0 H1 d))
    (dgModuleRawOutputPrecompHom R E K A F H0 H1 d) e b hk0 hk1 hA.symm hB hc ht
end
end SerrePositivity.InfinityCategories
