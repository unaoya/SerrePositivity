module
public import SerrePositivity.DifferentialGraded.Module.Ring
public import SerrePositivity.DifferentialGraded.Module.TensorAdjunction
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Module.RestrictionColimits
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComparison
public import SerrePositivity.DifferentialGraded.Tensor.ProjectiveKFlat
public import SerrePositivity.DifferentialGraded.Tensor.Ring

/-! # K-flat 係数からの自由加群を一対象環からの導来延長で計算する

置換は通常の dg 加群の射影置換だけを使う。dg 圏の分解は使わない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 一対象環 A から指定対象への dg 関手。 -/
def pointDGFunctor (b : D) : DGFunctor A PUnit.{1} D where
  obj _ := b
  map _ _ := eId (Complex A) b
  map_id _ := Category.id_comp _
  map_comp _ _ _ := by
    have h : (eId (Complex A) b ▷ homObject A D b b) ≫ eComp (Complex A) b b b =
        (λ_ (homObject A D b b)).hom := by
      apply (cancel_epi (λ_ (homObject A D b b)).inv).mp
      rw [e_id_comp, Iso.inv_hom_id]
    change (λ_ (𝟙_ (Complex A))).hom ≫ eId (Complex A) b =
      (eId (Complex A) b ⊗ₘ eId (Complex A) b) ≫ eComp (Complex A) b b b
    rw [tensorHom_def', Category.assoc, h, leftUnitor_naturality]

/-- 一対象環からの延長は、複体の同値を通じて自由加群関手になる。 -/
def pointExtensionFreeFunctorIso (b : D) :
    (ringModuleEquivalence A).inverse ⋙
      (dgModuleExtension A PUnit.{1} D (pointDGFunctor A D b)).onClosed ≅ freeAt b := by
  let adj := (ringModuleEquivalence A).symm.toAdjunction.comp
    (dgModuleExtensionRestrictionAdjunction A PUnit.{1} D (pointDGFunctor A D b))
  let e : (moduleRestriction A PUnit.{1} D (pointDGFunctor A D b).op ⋙
      (ringModuleEquivalence A).functor) ≅ moduleEvaluation A D b :=
    eqToIso (moduleRestriction_comp_evaluation A PUnit.{1} D
      (pointDGFunctor A D b).op PUnit.unit)
  exact Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) (freeEvaluationAdjunction A D b)

def pointExtensionRingIso (b : D) (M : ModuleCategory A PUnit.{1}) :
    (dgModuleExtension A PUnit.{1} D (pointDGFunctor A D b)).onClosed.obj M ≅
      (freeAt b).obj ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M) :=
  (dgModuleExtension A PUnit.{1} D (pointDGFunctor A D b)).onClosed.mapIso
      ((ringModuleEquivalence A).unitIso.app M) ≪≫
    (pointExtensionFreeFunctorIso A D b).app ((ringModuleEquivalence A).functor.obj M)

variable (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgExtension_relativeKFlat_quasiIso {M N : ModuleCategory A D}
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E ((dgModuleExtension A D E F).onClosed.map f) := by
  intro e
  rw [dgModuleExtension_map_eval]
  exact BalancedTensor.rightTensor_relativeKFlat_quasiIso A D
    ((functorGraph A D E F).leftAt e) hM hN f hf

/-- 相対 K-flat 加群の導来延長は underived 延長で計算できる。 -/
def relativeKFlatExtensionComputation (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj M) :=
  dgDerivedExtensionResolutionComputation A D E F (moduleCanonicalProjectiveResolution A D M) ≪≫
    moduleDerivedIso A E _ (dgExtension_relativeKFlat_quasiIso A D E F
      (moduleHomotopicallyProjective_relativeKFlat A D
        (moduleCanonicalProjectiveResolution A D M).projective) hM
      (moduleCanonicalProjectiveResolution A D M).π
      (moduleCanonicalProjectiveResolution A D M).quasiIso)

lemma coefficientRingModule_relativeKFlat (K : Complex A) (hK : complexKFlat A K) :
    moduleRelativeKFlat A PUnit.{1} (ringModule A K) := by
  intro N hN
  exact cochainAcyclic_of_iso (hK _ (hN PUnit.unit))
    (BalancedTensor.ringIso A (ringModule A K) N).symm

/-- K-flat 係数の underived 自由加群は、一対象環からの導来延長で得られる。 -/
def derivedFreeAtKFlatIso (b : D) (K : Complex A) (hK : complexKFlat A K) :
    (dgDerivedExtension A PUnit.{1} D (pointDGFunctor A D b)).obj
        ((moduleToDerived A PUnit.{1}).obj (ForgetEnrichment.of (Complex A) (ringModule A K))) ≅
      (moduleToDerived A D).obj ((freeAt b).obj K) :=
  relativeKFlatExtensionComputation A PUnit.{1} D (pointDGFunctor A D b)
      (ForgetEnrichment.of (Complex A) (ringModule A K))
      (coefficientRingModule_relativeKFlat A K hK) ≪≫
    (moduleToDerived A D).mapIso
      (pointExtensionRingIso A D b (ForgetEnrichment.of (Complex A) (ringModule A K)))

end SerrePositivity.DifferentialGraded.DGQuotient
