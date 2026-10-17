module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLayerModule
public import SerrePositivity.DifferentialGraded.Module.ConeDesc
public import SerrePositivity.DifferentialGraded.Derived.ConeTriangles
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # 長さ filtration の層と加群 cone の導来比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex CochainComplex Opposite Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def lengthLayerModuleEvaluationShortComplex (S : Set D) (z : D) (n : ℕ) (x : D) :
    ShortComplex (Complex A) :=
  ShortComplex.mk ((moduleEvaluation A D x).map
    (lengthModuleTransition A D S z (Nat.le_succ n)))
    ((moduleEvaluation A D x).map (lengthLayerModuleProjection A D S z n))
    (moduleCompZero_eval A D _ _ (lengthModuleTransition_layerProjection A D S z n) (op x))

lemma lengthLayerModuleEvaluationShortExact (S : Set D) (z : D) (n : ℕ) (x : D) :
    (lengthLayerModuleEvaluationShortComplex A D S z n x).ShortExact := by
  have hc := (isColimitMapCoconeCoforkEquiv' (moduleEvaluation A D x)
    (lengthModuleTransition_layerProjection A D S z n))
      (isColimitOfPreserves (moduleEvaluation A D x) (lengthLayerModule_isColimit A D S z n))
  have hm : Mono ((moduleEvaluation A D x).map
      (lengthModuleTransition A D S z (Nat.le_succ n))) := by
    rw [lengthModuleTransition_eval]
    exact mono_of_mono_fac (lengthMap_inclusion A D S x z (Nat.le_succ n))
  exact
    { exact := (lengthLayerModuleEvaluationShortComplex A D S z n x).exact_of_g_is_cokernel hc
      mono_f := hm
      epi_g := epi_of_isColimit_cofork hc }

/-- 相隣る長さ部分加群の cone から固定長加群への実際の加群射。 -/
def lengthLayerConeDesc (S : Set D) (z : D) (n : ℕ) :
    moduleCone A D (lengthModuleTransition A D S z (Nat.le_succ n)) ⟶
      selectedPathModule A D S (fun w => w.length = n + 1) z :=
  moduleConeDesc A D _ _ (lengthModuleTransition_layerProjection A D S z n)

@[reassoc] lemma lengthLayerConeDesc_inr (S : Set D) (z : D) (n : ℕ) :
    moduleConeInr A D (lengthModuleTransition A D S z (Nat.le_succ n)) ≫
      lengthLayerConeDesc A D S z n = lengthLayerModuleProjection A D S z n :=
  moduleConeDesc_inr A D _ _ _

/-- objectwise 短完全性から cone と固定長加群は擬同型。K-flat 仮定は不要。 -/
lemma lengthLayerConeDesc_quasiIso (S : Set D) (z : D) (n : ℕ) :
    moduleQuasiIso A D (lengthLayerConeDesc A D S z n) := by
  intro x
  rw [lengthLayerConeDesc, moduleConeDesc_eval]
  change QuasiIso (mappingCone.descShortComplex
    (lengthLayerModuleEvaluationShortComplex A D S z n x))
  exact mappingCone.quasiIso_descShortComplex (lengthLayerModuleEvaluationShortExact A D S z n x)

/-- 導来圏では実際の加群 cone と固定長加群が同型になる。 -/
def lengthLayerDerivedConeIso (S : Set D) (z : D) (n : ℕ) :
    (moduleToDerived A D).obj
        (moduleCone A D (lengthModuleTransition A D S z (Nat.le_succ n))) ≅
      (moduleToDerived A D).obj (selectedPathModule A D S (fun w => w.length = n + 1) z) :=
  moduleDerivedIso A D _ (lengthLayerConeDesc_quasiIso A D S z n)

/-- 相隣る長さ部分加群と固定長 path 加群からなる導来三角形。 -/
def lengthLayerDerivedTriangle (S : Set D) (z : D) (n : ℕ) :
    Triangle (DerivedModuleCategory A D) :=
  Triangle.mk ((moduleToDerived A D).map (lengthModuleTransition A D S z (Nat.le_succ n)))
    ((moduleToDerived A D).map (lengthLayerModuleProjection A D S z n))
    ((lengthLayerDerivedConeIso A D S z n).inv ≫
      (moduleDerivedConeTriangle A D (lengthModuleTransition A D S z (Nat.le_succ n))).mor₃)

def lengthLayerDerivedTriangleIso (S : Set D) (z : D) (n : ℕ) :
    moduleDerivedConeTriangle A D (lengthModuleTransition A D S z (Nat.le_succ n)) ≅
      lengthLayerDerivedTriangle A D S z n := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (lengthLayerDerivedConeIso A D S z n) ?_ ?_ ?_
  · change (moduleToDerived A D).map (lengthModuleTransition A D S z (Nat.le_succ n)) ≫
        𝟙 _ = 𝟙 _ ≫ (moduleToDerived A D).map
          (lengthModuleTransition A D S z (Nat.le_succ n))
    rw [Category.comp_id, Category.id_comp]
  · change (moduleToDerived A D).map
        (moduleConeInr A D (lengthModuleTransition A D S z (Nat.le_succ n))) ≫
        (moduleToDerived A D).map (lengthLayerConeDesc A D S z n) =
      𝟙 _ ≫ (moduleToDerived A D).map (lengthLayerModuleProjection A D S z n)
    rw [← CategoryTheory.Functor.map_comp, lengthLayerConeDesc_inr, Category.id_comp]
  · change (moduleDerivedConeTriangle A D
        (lengthModuleTransition A D S z (Nat.le_succ n))).mor₃ ≫ (𝟙 _)⟦(1 : ℤ)⟧' =
      (lengthLayerDerivedConeIso A D S z n).hom ≫
        (lengthLayerDerivedConeIso A D S z n).inv ≫ _
    rw [CategoryTheory.Functor.map_id, Category.comp_id, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]

lemma lengthLayerDerivedTriangle_distinguished (S : Set D) (z : D) (n : ℕ) :
    lengthLayerDerivedTriangle A D S z n ∈ distTriang (DerivedModuleCategory A D) :=
  isomorphic_distinguished _ (moduleDerivedConeTriangle_distinguished A D
    (lengthModuleTransition A D S z (Nat.le_succ n))) _
      (lengthLayerDerivedTriangleIso A D S z n).symm

end SerrePositivity.DifferentialGraded.DGQuotient
