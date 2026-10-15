module
public import SerrePositivity.DifferentialGraded.Module.ConeShift
public import SerrePositivity.DifferentialGraded.Module.ShiftCompatibility

/-! # cone shift比較と符号付き可換square -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleShiftSignSquare (s : ℤ) {X Y : ModuleCategory A D} (f : X ⟶ Y) :
    (s.negOnePow • f) ≫ (s.negOnePow • 𝟙 Y) = 𝟙 X ≫ f := by
  simp only [Linear.comp_units_smul, Category.comp_id, Category.id_comp, smul_smul,
    Int.units_mul_self, one_smul]

def moduleShiftSignIso (s : ℤ) (X : ModuleCategory A D) : X ≅ X where
  hom := s.negOnePow • 𝟙 X
  inv := s.negOnePow • 𝟙 X
  hom_inv_id := (moduleShiftSignSquare A D s (𝟙 X)).trans (Category.id_comp _)
  inv_hom_id := (moduleShiftSignSquare A D s (𝟙 X)).trans (Category.id_comp _)

lemma moduleEvaluation_sign_map (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (s.negOnePow • f) =
      s.negOnePow • (moduleEvaluation A D x).map f :=
  (moduleEvaluation A D x).map_units_smul s.negOnePow f

lemma moduleConeShift_inr (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (s.negOnePow • moduleShiftMap A D s (moduleConeInr A D f)) ≫
      moduleConeShiftHom A D s f =
        (s.negOnePow • 𝟙 (moduleShiftObj A D s N)) ≫
          moduleConeInr A D (moduleShiftMap A D s f) := by
  apply moduleMorphism_ext
  intro x
  rw [(moduleEvaluation A D x).map_comp]
  conv_rhs => rw [(moduleEvaluation A D x).map_comp]
  rw [moduleEvaluation_sign_map A D s (moduleShiftMap A D s (moduleConeInr A D f)) x,
    moduleEvaluation_sign_map A D s (𝟙 (moduleShiftObj A D s N)) x,
    (moduleEvaluation A D x).map_id, moduleShiftMap_eval, moduleConeInr_eval,
    moduleConeShiftHom_eval, moduleConeInr_eval]
  exact complexConeShift_inr ((moduleEvaluation A D x).map f) s _
    (moduleShiftMap_eval A D s f x)

lemma moduleConeShift_connecting (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    s.negOnePow • (moduleShiftMap A D s (moduleConeConnecting A D f) ≫
      (shiftFunctorComm (ModuleCategory A D) 1 s).hom.app M) =
        moduleConeShiftHom A D s f ≫ moduleConeConnecting A D (moduleShiftMap A D s f) := by
  apply moduleMorphism_ext
  intro x
  let E := moduleEvaluation A D x
  have h₁ := (moduleShiftMap_eval A D s (moduleConeConnecting A D f) x).trans
    (congrArg (fun a => (CategoryTheory.shiftFunctor (Complex A) s).map a)
      (moduleConeConnecting_eval A D f x))
  let c := (shiftFunctorComm (Complex A) 1 s).hom.app (E.obj M)
  have h₂ := (E.map_comp (moduleShiftMap A D s (moduleConeConnecting A D f))
    ((shiftFunctorComm (ModuleCategory A D) 1 s).hom.app M)).trans
      ((congrArg (fun b => E.map (moduleShiftMap A D s (moduleConeConnecting A D f)) ≫ b)
        (moduleEvaluation_shiftComm A D M 1 s x)).trans
          (congrArg (fun a => a ≫ c) h₁))
  have hL := (moduleEvaluation_sign_map A D s
    (moduleShiftMap A D s (moduleConeConnecting A D f) ≫
      (shiftFunctorComm (ModuleCategory A D) 1 s).hom.app M) x).trans
        (congrArg (s.negOnePow • ·) h₂)
  have hR := (E.map_comp (moduleConeShiftHom A D s f)
    (moduleConeConnecting A D (moduleShiftMap A D s f))).trans
      (congrArg₂ (fun a b => a ≫ b) (moduleConeShiftHom_eval A D s f x)
        (moduleConeConnecting_eval A D (moduleShiftMap A D s f) x))
  exact hL.trans (((Linear.units_smul_comp _ _ _).symm.trans
    (complexConeShift_connecting (E.map f) s _
      (moduleShiftMap_eval A D s f x))).trans hR.symm)

end SerrePositivity.DifferentialGraded
