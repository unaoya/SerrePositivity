module
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import Mathlib.Data.ZMod.Basic

/-! # 反変Homと右Hom加群の検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Opposite CochainComplex HomComplex SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

-- Dのsmallnessを仮定せず、対象と全次数作用を構成できる。
example (N : LeftModule A D) (T : Complex A) : DGFunctor A Dᵒᵖ (Complex A) :=
  (homRightModule A D N T).toFunctor

example (T P Q : Complex A) (f : Homogeneous Q P (-1)) (g : Homogeneous P T 1) :
    (((homContravariantDG A T).map (op P) (op Q)).f (-1) f).v 1 0 (by omega) g =
      -(f.comp g (by omega)) := by
  simpa using homContravariantDG_map_element A T (op P) (op Q) (-1) 1 0 (by omega) f g

example (T : Complex (ZMod 2)) :
    DGFunctor (ZMod 2) (Complex (ZMod 2))ᵒᵖ (Complex (ZMod 2)) :=
  homContravariantDG (ZMod 2) T

example [Small.{u} D] (N : LeftModule A D) : Complex A ⥤ ModuleCategory A D :=
  homRightFunctor A D N

#print axioms DGFunctor.op
#print axioms DGFunctor.op_id
#print axioms DGFunctor.op_comp
#print axioms homContravariantDG
#print axioms homContravariantDG_obj
#print axioms homContravariantDG_map_element
#print axioms homRightModule
#print axioms homRightModule_obj
#print axioms homRightModule_action
#print axioms homRightModule_postcompose_naturality
#print axioms homRightModuleMap
#print axioms homRightModuleMap_eval
#print axioms homRightFunctor
