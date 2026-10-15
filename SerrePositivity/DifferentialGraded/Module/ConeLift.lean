module
public import SerrePositivity.DifferentialGraded.Module.HomCone
public import SerrePositivity.DifferentialGraded.Module.HomCycles
public import SerrePositivity.DifferentialGraded.Complexes.ConeElements

/-! # 全次数Homのcone比較から得られるconeへのlift -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeLiftElement {T M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ)
    (a : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).X (q + 1))
    (b : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N)).X q) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X q :=
  (moduleHomConeComparison A D T f).f q
    (complexConeElementMk A (eHomWhiskerLeft (Complex A) T f) q a b)

lemma moduleConeLiftElement_π {T M N : ModuleCategory A D} (f : M ⟶ N) (q : ℤ)
    (a) (b) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f q
        (moduleConeLiftElement A D (T := T) f q a b) =
      mappingCone.liftCochain ((moduleEvaluation A D x).map f)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) M) x).f (q + 1) a)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N) x).f q b) rfl := by
  rw [moduleConeLiftElement, moduleHomConeComparison_apply_π,
    complexConeElementMk_fst, complexConeElementMk_snd]

lemma moduleConeLift_cycle_eval {T M N : ModuleCategory A D} (f : M ⟶ N) (a) (b)
    (ha : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).d 1 2 a = 0)
    (hb : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N)).d 0 1 b +
        (show (moduleHom A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N)).X 1 from
          (eHomWhiskerLeft (Complex A) T f).f 1 a) = 0) (x : D) :
    δ 1 2 ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) x).f 1 a) = 0 ∧
    δ 0 1 ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) x).f 0 b) +
        (show Cochain ((ForgetEnrichment.to (Complex A) T).obj (Opposite.op x))
          ((ForgetEnrichment.to (Complex A) N).obj (Opposite.op x)) 1 from
          ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
            (ForgetEnrichment.to (Complex A) M) x).f 1 a).comp
            (Cochain.ofHom ((moduleEvaluation A D x).map f)) (add_zero 1)) = 0 := by
  constructor
  · have h := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M) x).f 2) ha
    rw [moduleHomElement_d_π, map_zero] at h
    exact h
  · have h := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N) x).f 1) hb
    rw [map_add, moduleHomElement_d_π, moduleHomWhiskerLeft_apply_π, map_zero] at h
    exact h

lemma moduleConeLiftElement_closed {T M N : ModuleCategory A D} (f : M ⟶ N) (a) (b)
    (ha : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).d 1 2 a = 0)
    (hb : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N)).d 0 1 b +
        (show (moduleHom A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N)).X 1 from
          (eHomWhiskerLeft (Complex A) T f).f 1 a) = 0) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d 0 1
        (moduleConeLiftElement A D (T := T) f 0 a b) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeLiftElement_π, map_zero]
  have hx := moduleConeLift_cycle_eval A D (T := T) f a b ha hb x
  exact Cocycle.δ_eq_zero
    (mappingCone.liftCocycle ((moduleEvaluation A D x).map f)
      (Cocycle.mk ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) M) x).f 1 a) 2 rfl hx.1)
      ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
        (ForgetEnrichment.to (Complex A) N) x).f 0 b) (zero_add 1) hx.2) 1

def moduleConeLiftOfCycle {T M N : ModuleCategory A D} (f : M ⟶ N) (a) (b)
    (ha : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) M)).d 1 2 a = 0)
    (hb : (moduleHom A D (ForgetEnrichment.to (Complex A) T)
      (ForgetEnrichment.to (Complex A) N)).d 0 1 b +
        (show (moduleHom A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N)).X 1 from
          (eHomWhiskerLeft (Complex A) T f).f 1 a) = 0) : T ⟶ moduleCone A D f :=
  moduleMorphismOfCycle A D (moduleConeLiftElement A D f 0 a b)
    (moduleConeLiftElement_closed A D f a b ha hb)

@[simp] lemma moduleConeLiftOfCycle_eval {T M N : ModuleCategory A D} (f : M ⟶ N)
    (a) (b) (ha) (hb) (x : D) :
    (moduleEvaluation A D x).map (moduleConeLiftOfCycle A D (T := T) f a b ha hb) =
      mappingCone.lift ((moduleEvaluation A D x).map f)
        (Cocycle.mk ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) M) x).f 1 a) 2 rfl
          (moduleConeLift_cycle_eval A D f a b ha hb x).1)
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (Complex A) N) x).f 0 b)
        (moduleConeLift_cycle_eval A D f a b ha hb x).2 := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain, mappingCone.ofHom_lift]
  change (moduleHomπ A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleMorphismOfCycle A D (moduleConeLiftElement A D f 0 a b) _))).val = _
  rw [moduleMorphismOfCycle_cycle, moduleConeLiftElement_π]
  rfl

end SerrePositivity.DifferentialGraded
