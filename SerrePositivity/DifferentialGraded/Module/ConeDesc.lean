module
public import SerrePositivity.DifferentialGraded.Module.Cone
public import SerrePositivity.DifferentialGraded.Complexes.ConeDesc
public import SerrePositivity.DifferentialGraded.Module.Zero

/-! # 合成が零となる加群射の全dg自然なcone延長 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompZero_eval {L M N : ModuleCategory A D} (a : L ⟶ M) (q : M ⟶ N)
    (h : a ≫ q = 0) (x : Dᵒᵖ) :
    closedTransApp A (moduleClosedHomEquiv A D L M a) x ≫
      closedTransApp A (moduleClosedHomEquiv A D M N q) x = 0 := by
  change (moduleEvaluation A D x.unop).map a ≫ (moduleEvaluation A D x.unop).map q = 0
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_zero]

def moduleConeDesc {L M N : ModuleCategory A D} (a : L ⟶ M) (q : M ⟶ N) (h : a ≫ q = 0) :
    moduleCone A D a ⟶ N :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) (moduleCone A D a))
    (N := ForgetEnrichment.to (Complex A) N)
    (fun x => complexConeDesc (closedTransApp A (moduleClosedHomEquiv A D L M a) x)
      (closedTransApp A (moduleClosedHomEquiv A D M N q) x) (moduleCompZero_eval A D a q h x)) (by
        intro x y
        apply HomologicalComplex.Hom.ext
        funext p
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        change (coneMapCochain
          (closedTransApp A (moduleClosedHomEquiv A D L M a) x)
          (closedTransApp A (moduleClosedHomEquiv A D L M a) y)
          (((ForgetEnrichment.to (Complex A) L).map x y).f p b)
          (((ForgetEnrichment.to (Complex A) M).map x y).f p b)).comp
          (Cochain.ofHom (complexConeDesc _ _ (moduleCompZero_eval A D a q h y))) (add_zero p) =
          (Cochain.ofHom (complexConeDesc _ _ (moduleCompZero_eval A D a q h x))).comp
            (((ForgetEnrichment.to (Complex A) N).map x y).f p b) (zero_add p)
        apply coneMapCochain_desc
        exact congrArg (fun k => k.f p b)
          (closedTransApp_naturality A (moduleClosedHomEquiv A D M N q) x y))

@[simp] lemma moduleConeDesc_eval {L M N : ModuleCategory A D} (a : L ⟶ M) (q : M ⟶ N)
    (h : a ≫ q = 0) (x : D) :
    (moduleEvaluation A D x).map (moduleConeDesc A D a q h) =
      complexConeDesc ((moduleEvaluation A D x).map a) ((moduleEvaluation A D x).map q)
        (moduleCompZero_eval A D a q h (op x)) := by
  unfold moduleConeDesc
  rw [moduleMorphismMk_eval]
  rfl

@[reassoc] lemma moduleConeDesc_inr {L M N : ModuleCategory A D} (a : L ⟶ M) (q : M ⟶ N)
    (h : a ≫ q = 0) : moduleConeInr A D a ≫ moduleConeDesc A D a q h = q := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeInr_eval, moduleConeDesc_eval, complexConeDesc_inr]

end SerrePositivity.DifferentialGraded
