module
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import SerrePositivity.DifferentialGraded.Functor.ComplexValued
public import SerrePositivity.DifferentialGraded.Complexes.ClosedMaps

/-! # 複体に値を持つdg関手の閉零・微分・通常順合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

def toComplexFunctor (F : DGFunctor A D (Complex A)) : ClosedCategory A D ⥤ Complex A :=
  F.onClosed ⋙ closedToComplex A

lemma map_closedElement (F : DGFunctor A D (Complex A))
    {M N : ClosedCategory A D} (f : M ⟶ N) :
    (F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      Cochain.ofHom ((F.toComplexFunctor A).map f) := by
  have h := mapFromUnit_cochain A
    (F.obj (ForgetEnrichment.to (Complex A) M)) (F.obj (ForgetEnrichment.to (Complex A) N))
    (ForgetEnrichment.homTo (Complex A) f ≫
      F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))
  rw [cycleFromUnit_postcomp] at h
  exact h.symm

lemma map_d_cochain (F : DGFunctor A D (Complex A)) {x y : D} {p q : ℤ}
    (z : GradedHom A x y p) :
    (F.map x y).f q ((x ⟶[Complex A] y).d p q z) =
      δ p q ((F.map x y).f p z) := by
  exact (congrArg (fun f => f z) ((F.map x y).comm p q)).symm

lemma map_compose_cochain (F : DGFunctor A D (Complex A)) {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    (F.map x z).f n (compose A g f hn) =
      ((F.map x y).f p f).comp ((F.map y z).f q g) hn := by
  unfold compose
  simp only [Units.smul_def, map_zsmul]
  rw [map_forward_cochain]
  simp only [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]

end SerrePositivity.DifferentialGraded.DGFunctor
