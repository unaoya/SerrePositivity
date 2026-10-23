module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSourceSlideFaces
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackPathLift

/-!
概要：一定の底を持つ source の実経路から、元の class 模型内の実経路を構成する。
方針：動く始点の affine 二重経路を、元の両脚と共に実 path lift に渡す。
規約：全 source 経路と全 class 経路を保持。使われ方：直接分母の自然性模型比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
open DGAlgebra
variable {R : Type u} [CommRing R] {A W D : Mon (Complex R)} (N : Bimod A A)
  (f : D ⟶ SquareZero.algebra A N) (r : W ⟶ A) {l₀ l₁ : W ⟶ D}
  (h : DGAlgebra.Path.Witness R l₀ l₁)
  (hh : (h.postcomp f).hom ≫ DGAlgebra.Path.map R (SquareZero.projection A N) =
    r ≫ DGAlgebra.Path.diagonal R A)
  (p : SquareZero.RelativeWitness r N (l₀ ≫ f) (r ≫ SquareZero.zeroSection A N))

def sourceModelClassWitness : SquareZero.RelativeWitness r N (l₀ ≫ f) (l₁ ≫ f) where
  toWitness := h.postcomp f
  projection_eq := hh

def sourceModelInitialMap : W ⟶ HomotopyPullbackModel.algebra R f (SquareZero.zeroSection A N) :=
  HomotopyPullbackModel.lift R f (SquareZero.zeroSection A N) l₀ r p.toWitness

def sourceModelFinalMap : W ⟶ HomotopyPullbackModel.algebra R f (SquareZero.zeroSection A N) :=
  HomotopyPullbackModel.lift R f (SquareZero.zeroSection A N) l₁ r
    (((sourceModelClassWitness N f r h hh).reverse).comp p).toWitness

def sourceModelPath : W ⟶ DGAlgebra.Path.algebra R
    (HomotopyPullbackModel.algebra R f (SquareZero.zeroSection A N)) :=
  HomotopyPullbackModel.pathLift R f (SquareZero.zeroSection A N) h.hom
    (r ≫ DGAlgebra.Path.diagonal R A) ((sourceModelClassWitness N f r h hh).sourceSlideHom p)
    (SquareZero.RelativeWitness.sourceSlideHom_source_trace _ _)
    (by
      rw [SquareZero.RelativeWitness.sourceSlideHom_target_trace]
      simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality])

def sourceModelHomotopy : DGAlgebra.Path.Witness R (sourceModelInitialMap N f r p)
    (sourceModelFinalMap N f r h hh p) where
  hom := sourceModelPath N f r h hh p
  source_eq := by
    unfold sourceModelPath
    apply HomotopyPullbackModel.pathLift_source_eq
    · exact h.source_eq.trans (HomotopyPullbackModel.lift_left R _ _ _ _ _).symm
    · rw [Category.assoc, DGAlgebra.Path.diagonal_source, Category.comp_id]
      exact (HomotopyPullbackModel.lift_right R _ _ _ _ _).symm
    · exact (SquareZero.RelativeWitness.sourceSlideHom_source _ _).trans
        (HomotopyPullbackModel.lift_path R _ _ _ _ _).symm
  target_eq := by
    unfold sourceModelPath
    apply HomotopyPullbackModel.pathLift_target_eq
    · exact h.target_eq.trans (HomotopyPullbackModel.lift_left R _ _ _ _ _).symm
    · rw [Category.assoc, DGAlgebra.Path.diagonal_target, Category.comp_id]
      exact (HomotopyPullbackModel.lift_right R _ _ _ _ _).symm
    · exact (SquareZero.RelativeWitness.sourceSlideHom_target _ _).trans
        (HomotopyPullbackModel.lift_path R _ _ _ _ _).symm

lemma sourceModelHomotopy_left : (sourceModelHomotopy N f r h hh p).hom ≫
    DGAlgebra.Path.map R (HomotopyPullbackModel.left R f (SquareZero.zeroSection A N)) = h.hom := by
  unfold sourceModelHomotopy sourceModelPath
  exact HomotopyPullbackModel.pathLift_left R f (SquareZero.zeroSection A N) h.hom
    (r ≫ DGAlgebra.Path.diagonal R A) ((sourceModelClassWitness N f r h hh).sourceSlideHom p)
    (SquareZero.RelativeWitness.sourceSlideHom_source_trace _ _)
    (by
      rw [SquareZero.RelativeWitness.sourceSlideHom_target_trace]
      simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality])

lemma sourceModelHomotopy_right : (sourceModelHomotopy N f r h hh p).hom ≫
    DGAlgebra.Path.map R (HomotopyPullbackModel.right R f (SquareZero.zeroSection A N)) =
      r ≫ DGAlgebra.Path.diagonal R A := by
  unfold sourceModelHomotopy sourceModelPath
  exact HomotopyPullbackModel.pathLift_right R f (SquareZero.zeroSection A N) h.hom
    (r ≫ DGAlgebra.Path.diagonal R A) ((sourceModelClassWitness N f r h hh).sourceSlideHom p)
    (SquareZero.RelativeWitness.sourceSlideHom_source_trace _ _)
    (by
      rw [SquareZero.RelativeWitness.sourceSlideHom_target_trace]
      simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality])

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
