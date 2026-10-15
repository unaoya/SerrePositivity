module
public import SerrePositivity.DifferentialGraded.Module.ConeElements
public import SerrePositivity.DifferentialGraded.Module.HomElementComposition
public import SerrePositivity.DifferentialGraded.Module.HomCycles

/-! # 全dg自然なホモトピーを用いるconeからの延長

通常順の斉次合成でconeの二つの射影を組み合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- coneからの閉零射の候補。hは次数−1、bは閉零射。 -/
def moduleConeDescElement {L M T : ModuleCategory A D} (a : L ⟶ M)
    (h : (moduleHom A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) T)).X (-1)) (b : M ⟶ T) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D a))
      (ForgetEnrichment.to (Complex A) T)).X 0 :=
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D a))
    (y := ForgetEnrichment.to (Complex A) L) (z := ForgetEnrichment.to (Complex A) T)
    h (moduleConeFstElement A D a) (by omega) +
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D a))
    (y := ForgetEnrichment.to (Complex A) M) (z := ForgetEnrichment.to (Complex A) T)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) b)).val
    (moduleConeSndElement A D a) (by omega)

lemma moduleConeDescElement_π {L M T : ModuleCategory A D} (a : L ⟶ M) (h) (b : M ⟶ T)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D a))
      (ForgetEnrichment.to (Complex A) T) x).f 0 (moduleConeDescElement A D a h b) =
      mappingCone.descCochain ((moduleEvaluation A D x).map a)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) L)
          (ForgetEnrichment.to (Complex A) T) x).f (-1) h)
        (Cochain.ofHom ((moduleEvaluation A D x).map b)) (by omega) := by
  rw [moduleConeDescElement, map_add, moduleHomCompose_π, moduleHomCompose_π,
    moduleConeFstElement_π, moduleConeSndElement_π, ← moduleEvaluation_cochain]
  rfl

lemma moduleConeDescElement_closed {L M T : ModuleCategory A D} (a : L ⟶ M) (h) (b : M ⟶ T)
    (hh : (moduleHom A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) T)).d (-1) 0 h =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D a))
      (ForgetEnrichment.to (Complex A) T)).d 0 1 (moduleConeDescElement A D a h b) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeDescElement_π, map_zero,
    mappingCone.δ_descCochain _ _ _ _ 1 (by omega)]
  have hc := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) L)
    (ForgetEnrichment.to (Complex A) T) x).f 0) hh
  rw [moduleHomElement_d_π, ← moduleEvaluation_cochain,
    CategoryTheory.Functor.map_comp, Cochain.ofHom_comp] at hc
  rw [hc]
  simp

/-- hの境界がa≫bなら、cone(a)→Tを構成できる。 -/
def moduleConeDescOfBoundary {L M T : ModuleCategory A D} (a : L ⟶ M) (h) (b : M ⟶ T)
    (hh : (moduleHom A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) T)).d (-1) 0 h =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val) :
    moduleCone A D a ⟶ T :=
  moduleMorphismOfCycle A D (moduleConeDescElement A D a h b)
    (moduleConeDescElement_closed A D a h b hh)


lemma moduleConeDescBoundary_condition_eval {L M T : ModuleCategory A D} (a : L ⟶ M)
    (h) (b : M ⟶ T)
    (hh : (moduleHom A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) T)).d (-1) 0 h =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (a ≫ b))).val) (x : D) :
    δ (-1) 0 ((moduleHomπ A D (ForgetEnrichment.to (Complex A) L)
      (ForgetEnrichment.to (Complex A) T) x).f (-1) h) =
        Cochain.ofHom ((moduleEvaluation A D x).map a ≫ (moduleEvaluation A D x).map b) := by
  have hc := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) L)
    (ForgetEnrichment.to (Complex A) T) x).f 0) hh
  rw [moduleHomElement_d_π, ← moduleEvaluation_cochain,
    CategoryTheory.Functor.map_comp] at hc
  exact hc

@[simp] lemma moduleConeDescOfBoundary_eval {L M T : ModuleCategory A D} (a : L ⟶ M)
    (h) (b : M ⟶ T) (hh) (x : D) :
    (moduleEvaluation A D x).map (moduleConeDescOfBoundary A D a h b hh) =
      mappingCone.desc ((moduleEvaluation A D x).map a)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) L)
          (ForgetEnrichment.to (Complex A) T) x).f (-1) h)
        ((moduleEvaluation A D x).map b)
        (moduleConeDescBoundary_condition_eval A D a h b hh x) := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain, mappingCone.ofHom_desc]
  change (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D a))
    (ForgetEnrichment.to (Complex A) T) x).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleMorphismOfCycle A D (moduleConeDescElement A D a h b) _))).val = _
  rw [moduleMorphismOfCycle_cycle, moduleConeDescElement_π]

@[reassoc] lemma moduleConeDescOfBoundary_inr {L M T : ModuleCategory A D} (a : L ⟶ M)
    (h) (b : M ⟶ T) (hh) :
    moduleConeInr A D a ≫ moduleConeDescOfBoundary A D a h b hh = b := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeInr_eval, moduleConeDescOfBoundary_eval]
  exact mappingCone.inr_desc _ _ _ _

end SerrePositivity.DifferentialGraded
