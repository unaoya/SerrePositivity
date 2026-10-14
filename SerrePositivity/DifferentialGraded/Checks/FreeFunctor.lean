module
public import SerrePositivity.DifferentialGraded.Module.Free
public import Mathlib.Data.ZMod.Basic

/-! # U6b の全次数自然な閉零射・自由加群関手の検証 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory MonoidalCategory Opposite
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
example (x : D) : Complex A ⥤ ModuleCategory A D := freeAt x
example (x y : D) {K L : Complex A} (g : K ⟶ L) :
    (moduleEvaluation A D y).map ((freeAt x).map g) = g ⊗ₘ 𝟙 (y ⟶[Complex A] x) :=
  tensorModuleMap_eval g (representable A x) y
example (x : D) (K : Complex A) :
    (freeAt x).map (𝟙 K) = 𝟙 ((freeAt x).obj K) := (freeAt x).map_id K
example (K : Complex (ZMod 2)) : ModuleCategory (ZMod 2) PUnit.{1} :=
  (freeAt (A := ZMod 2) PUnit.unit).obj K
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.tensorLeftHom_naturality
#print axioms SerrePositivity.DifferentialGraded.homPostcompose_closedMap
#print axioms SerrePositivity.DifferentialGraded.homPrecompose_closedMap
#print axioms SerrePositivity.DifferentialGraded.closedFamilyTrans
#print axioms SerrePositivity.DifferentialGraded.moduleMorphismMk_eval
#print axioms SerrePositivity.DifferentialGraded.freeAt
