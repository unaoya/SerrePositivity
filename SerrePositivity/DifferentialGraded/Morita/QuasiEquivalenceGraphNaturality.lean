module
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph
public import SerrePositivity.DifferentialGraded.Morita.PerfectFunctoriality
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionNaturality

/-! # graph作用の自然な解像度モデルと主局所化による比較の復元

将来のU16a関手Kについて、通常graph作用による自然な計算同型を入力すると、
主導来関手の自然同型を復元する。対象ごとの同型だけを自然性の代用にしない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def quasiEquivalenceGraphResolutionModel
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    ModuleCategory A D ⥤ DerivedModuleCategory A E :=
  moduleResolutionHomotopyFunctor A D R ⋙
    (kernelTensor A D E (functorGraph A D E F)).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E

/-- 既存導来延長は、任意解像度族によるgraphモデルを自然に計算する。 -/
def quasiEquivalenceGraphDerivedModelIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleToDerived A D ⋙ dgDerivedExtension A D E F ≅
      quasiEquivalenceGraphResolutionModel A D E F R :=
  Functor.isoWhiskerLeft (moduleToDerived A D)
      (dgResolutionDerivedExtensionIso A D E F (moduleCanonicalProjectiveResolution A D) R) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDerivedResolutionFunctor_fac A D R) _

/-- 通常graphの射影解像度計算は、元の加群の射と選んだliftに自然。 -/
lemma quasiEquivalenceGraphResolutionModel_naturality
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (dgResolutionDerivedExtension A D E F R).map ((moduleToDerived A D).map f) ≫
        (dgResolutionDerivedExtensionComputation A D E F R N).hom =
      (dgResolutionDerivedExtensionComputation A D E F R M).hom ≫
        (moduleToDerived A E).map
          ((kernelTensor A D E (functorGraph A D E F)).onClosed.map ((R M).lift (R N) f)) :=
  dgResolutionDerivedExtensionComputation_naturality A D E F R f

/-- 自然なgraph計算同型を持つ指定関手Kを、既存導来延長へ比較する。 -/
def quasiEquivalenceGraphComparisonOfModel
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R) :
    K ≅ dgDerivedExtension A D E F :=
  (Localization.fullyFaithfulWhiskeringLeft (moduleToDerived A D) (moduleQuasiIso A D)
    (DerivedModuleCategory A E)).preimageIso
      (eK ≪≫ (quasiEquivalenceGraphDerivedModelIso A D E F R).symm)

lemma quasiEquivalenceGraphComparisonOfModel_precomp
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R) :
    Functor.whiskerLeft (moduleToDerived A D)
        (quasiEquivalenceGraphComparisonOfModel A D E F R K eK).hom =
      (eK ≪≫ (quasiEquivalenceGraphDerivedModelIso A D E F R).symm).hom :=
  (Localization.fullyFaithfulWhiskeringLeft (moduleToDerived A D) (moduleQuasiIso A D)
    (DerivedModuleCategory A E)).map_preimage _

lemma quasiEquivalenceGraphComparisonOfModel_unique
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R)
    (α : K ⟶ dgDerivedExtension A D E F)
    (hα : Functor.whiskerLeft (moduleToDerived A D) α =
      (eK ≪≫ (quasiEquivalenceGraphDerivedModelIso A D E F R).symm).hom) :
    α = (quasiEquivalenceGraphComparisonOfModel A D E F R K eK).hom := by
  apply (Localization.fullyFaithfulWhiskeringLeft (moduleToDerived A D)
    (moduleQuasiIso A D) (DerivedModuleCategory A E)).map_injective
  exact hα.trans (quasiEquivalenceGraphComparisonOfModel_precomp A D E F R K eK).symm

lemma quasiEquivalenceGraphComparisonOfModel_perfect
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R)
    {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E (K.obj X) :=
  (modulePerfect A E).prop_of_iso
    ((quasiEquivalenceGraphComparisonOfModel A D E F R K eK).app X).symm
    (dgDerivedExtension_perfect A D E F hX)

lemma quasiEquivalenceGraphComparisonOfModel_isEquivalence
    (hF : QuasiEquivalence F)
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R) :
    K.IsEquivalence := by
  let : (dgDerivedExtension A D E F).IsEquivalence :=
    (dgFunctorDerivedEquivalence A D E F hF).isEquivalence_functor
  exact Functor.isEquivalence_of_iso
    (quasiEquivalenceGraphComparisonOfModel A D E F R K eK).symm

def quasiEquivalenceGraphComparisonOnPerfect
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (K : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (eK : moduleToDerived A D ⋙ K ≅ quasiEquivalenceGraphResolutionModel A D E F R) :
    perfectFunctorRestriction A D E K
        (fun _ h => quasiEquivalenceGraphComparisonOfModel_perfect A D E F R K eK h) ≅
      perfectFunctorRestriction A D E (dgDerivedExtension A D E F)
        (fun _ h => dgDerivedExtension_perfect A D E F h) :=
  perfectFunctorIso A D E K (dgDerivedExtension A D E F)
    (fun _ h => quasiEquivalenceGraphComparisonOfModel_perfect A D E F R K eK h)
    (fun _ h => dgDerivedExtension_perfect A D E F h)
    (quasiEquivalenceGraphComparisonOfModel A D E F R K eK)

end SerrePositivity.DifferentialGraded.Morita
