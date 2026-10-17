module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionDifferential

/-! # cell付加の最終Hom合成：CompositionComparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 微分を変えても最終合成の各次数の射は内部合成の射そのものである。 -/
lemma attachedComposition_f (x y z : D) (n : ℤ) :
    (C.attachedComposition A D I x y z).f n = (C.internalComposition A D I x y z).f n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  exact C.attachedComposition_ι A D I x y z i j n hij

/-- 最終合成は元のdg圏の豊穣合成と包含を通じて一致する。 -/
lemma attachedComposition_original (x y z : D) :
    (C.originalHomInclusion A D I x y ⊗ₘ C.originalHomInclusion A D I y z) ≫
      C.attachedComposition A D I x y z =
    eComp (Complex A) x y z ≫ C.originalHomInclusion A D I x z := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, attachedComposition_f,
    HomologicalComplex.comp_f, originalHomInclusion_f]
  have h := congrArg (fun f => f.f n) (C.internalComposition_original_original A D I x y z)
  simp only [HomologicalComplex.comp_f] at h
  exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
