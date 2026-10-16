module
public import SerrePositivity.DifferentialGraded.Module.LeftClosedMaps

/-! # 左dg加群の閉零射の全Hom自然性をchain mapの式で読む -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma leftModuleMorphism_naturality {M N : LeftModuleCategory A D} (f : M ⟶ N) (x y : D) :
    (ForgetEnrichment.to (Complex A) M).map x y ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x)
        ((leftModuleEvaluation A D y).map f) =
    (ForgetEnrichment.to (Complex A) N).map x y ≫
      homPrecompose ((leftModuleEvaluation A D x).map f)
        ((ForgetEnrichment.to (Complex A) N).obj y) := by
  have h := closedTransApp_naturality A (leftModuleClosedHomEquiv A D M N f)
    (op (op x)) (op (op y))
  change (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) M).map x y) ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x)
        ((leftModuleEvaluation A D y).map f) =
    (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) N).map x y) ≫
      homPrecompose ((leftModuleEvaluation A D x).map f)
        ((ForgetEnrichment.to (Complex A) N).obj y) at h
  simpa only [Category.id_comp] using h

end SerrePositivity.DifferentialGraded
