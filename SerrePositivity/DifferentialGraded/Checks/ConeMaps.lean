module
public import SerrePositivity.DifferentialGraded.Module.ConeFunctor
public import SerrePositivity.DifferentialGraded.Module.Ring
public import Mathlib.Data.ZMod.Basic

/-! # U7b3b：cone の connecting map・可換 square・triangle 評価比較 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Pretriangulated CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
example {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A D f ⟶ M⟦(1 : ℤ)⟧ := moduleConeConnecting A D f
example {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).mapTriangle.obj (moduleConeTriangle A D f) ≅
      mappingCone.triangle ((moduleEvaluation A D x).map f) :=
  moduleConeTriangleEvaluationIso A D f x
example {M N M' N' : ModuleCategory A D} (f : M ⟶ N) (g : M' ⟶ N')
    (u : M ⟶ M') (v : N ⟶ N') (h : f ≫ v = u ≫ g) :
    moduleConeTriangle A D f ⟶ moduleConeTriangle A D g := moduleConeTriangleMap A D f g u v h
example {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleConeFunctor A D).obj (Arrow.mk f) = moduleCone A D f := rfl
example (f g k : Arrow (ModuleCategory A D)) (s : f ⟶ g) (t : g ⟶ k) :
    (moduleConeFunctor A D).map (s ≫ t) =
      (moduleConeFunctor A D).map s ≫ (moduleConeFunctor A D).map t :=
  (moduleConeFunctor A D).map_comp s t
example {K P Q R S : Complex A} (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S)
    (h : a ≫ homPostcompose P g = b ≫ homPrecompose f S) :
    coneHomMap f g a b h ≫ homPostcompose (mappingCone f) (mappingCone.triangle g).mor₃ =
      a ≫ shiftHom 1 P R ≫ homPrecompose (mappingCone.triangle f).mor₃ (R⟦(1 : ℤ)⟧) :=
  coneHomMap_connecting f g a b h
example {M N : ModuleCategory ℤ PUnit.{1}} (f : M ⟶ N) :
    (moduleEvaluation ℤ PUnit.{1} PUnit.unit).mapTriangle.obj (moduleConeTriangle ℤ PUnit.{1} f) ≅
      mappingCone.triangle ((moduleEvaluation ℤ PUnit.{1} PUnit.unit).map f) :=
  moduleConeTriangleEvaluationIso _ _ _ _
example : Arrow (ModuleCategory (ZMod 2) PUnit.{1}) ⥤ ModuleCategory (ZMod 2) PUnit.{1} :=
  moduleConeFunctor _ _
end SerrePositivity.DifferentialGraded.Checks
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_fst_v
#print axioms SerrePositivity.DifferentialGraded.coneHomMap_connecting
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_ofHom
#print axioms SerrePositivity.DifferentialGraded.moduleConeConnecting
#print axioms SerrePositivity.DifferentialGraded.moduleConeConnecting_eval
#print axioms SerrePositivity.DifferentialGraded.moduleConeTriangle
#print axioms SerrePositivity.DifferentialGraded.moduleConeTriangleEvaluationIso
#print axioms SerrePositivity.DifferentialGraded.coneFamilyMap_naturality
#print axioms SerrePositivity.DifferentialGraded.moduleSquare_eval
#print axioms SerrePositivity.DifferentialGraded.moduleConeMap
#print axioms SerrePositivity.DifferentialGraded.moduleConeMap_eval
#print axioms SerrePositivity.DifferentialGraded.moduleConeMap_id
#print axioms SerrePositivity.DifferentialGraded.moduleConeMap_comp
#print axioms SerrePositivity.DifferentialGraded.moduleConeMap_inr
#print axioms SerrePositivity.DifferentialGraded.moduleConeMap_connecting
#print axioms SerrePositivity.DifferentialGraded.moduleConeTriangleMap
#print axioms SerrePositivity.DifferentialGraded.moduleConeFunctor
