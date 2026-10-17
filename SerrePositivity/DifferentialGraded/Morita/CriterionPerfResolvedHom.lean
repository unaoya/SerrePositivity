module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfDGFunctorShift

/-! # dg 関手の全 Hom 射を、像の源の射影増強により比較する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A (RightModule A D) (RightModule A E))

def criterionPerfResolvedHomComparison (M N : RightModule A D)
    (R : ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj M))) :
    moduleHom A D M N ⟶
      moduleHom A E (ForgetEnrichment.to (Complex A) R.obj) (F.obj N) :=
  F.map M N ≫ eHomWhiskerRight (Complex A) R.π (ForgetEnrichment.of (Complex A) (F.obj N))

/-- 像の源の解像度を shift し、dg 関手の正規化 shift 同型で増強を戻す。 -/
def criterionPerfDGFunctorShiftResolution (M : RightModule A D)
    (R : ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj M))) (s : ℤ) :
    ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj (shiftModule s M))) where
  obj := R.obj⟦s⟧
  π := (moduleShiftFunctor A E s).map R.π ≫
    (normalizedDGModuleFunctorShiftIso A D E F s M).inv
  projective := moduleHomotopicallyProjective_shift A E R.projective s
  quasiIso := by
    intro e
    rw [CategoryTheory.Functor.map_comp]
    have h : QuasiIso ((moduleEvaluation A E e).map ((moduleShiftFunctor A E s).map R.π)) := by
      change QuasiIso ((moduleEvaluation A E e).map (moduleShiftMap A E s R.π))
      rw [moduleShiftMap_eval]
      exact (CochainComplex.quasiIso_shift_iff _ s).2 (R.quasiIso e)
    have := h
    infer_instance

/-- 射影増強後の全 Hom 比較の源 shift 可換図式。 -/
lemma criterionPerfResolvedHomComparison_sourceShift (M N : RightModule A D)
    (R : ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj M))) (s : ℤ) :
    criterionPerfResolvedHomComparison A D E F (shiftModule s M) N
        (criterionPerfDGFunctorShiftResolution A D E F M R s) ≫
      (moduleHomSourceShiftIso A E (ForgetEnrichment.to (Complex A) R.obj) (F.obj N) s).hom =
    (moduleHomSourceShiftIso A D M N s).hom ≫
      (CategoryTheory.shiftFunctor (Complex A) (-s)).map
        (criterionPerfResolvedHomComparison A D E F M N R) := by
  simp only [criterionPerfResolvedHomComparison, criterionPerfDGFunctorShiftResolution,
    eHomWhiskerRight_comp, Category.assoc]
  rw [criterionPerfHomSourceShiftIso_precompose]
  have h := congrArg (fun k => k ≫ (CategoryTheory.shiftFunctor (Complex A) (-s)).map
    (eHomWhiskerRight (Complex A) R.π (ForgetEnrichment.of (Complex A) (F.obj N))))
    (criterionPerfDGFunctorHom_sourceShift A D E F M N s)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h ⊢
  exact h

/-- shift した増強による比較の H⁰ は、元の比較の H^(-s) を検査する。 -/
lemma criterionPerfResolvedHomComparison_shift_zero_iff (M N : RightModule A D)
    (R : ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj M))) (s : ℤ) :
    QuasiIsoAt (criterionPerfResolvedHomComparison A D E F (shiftModule s M) N
      (criterionPerfDGFunctorShiftResolution A D E F M R s)) 0 ↔
    QuasiIsoAt (criterionPerfResolvedHomComparison A D E F M N R) (-s) := by
  let a := criterionPerfResolvedHomComparison A D E F M N R
  let b := criterionPerfResolvedHomComparison A D E F (shiftModule s M) N
    (criterionPerfDGFunctorShiftResolution A D E F M R s)
  let eT := (moduleHomSourceShiftIso A E (ForgetEnrichment.to (Complex A) R.obj) (F.obj N) s)
  let eS := moduleHomSourceShiftIso A D M N s
  calc
    QuasiIsoAt b 0 ↔ QuasiIsoAt (b ≫ eT.hom) 0 :=
      (quasiIsoAt_iff_comp_right b eT.hom 0).symm
    _ ↔ QuasiIsoAt (eS.hom ≫ (CategoryTheory.shiftFunctor (Complex A) (-s)).map a) 0 := by
      rw [criterionPerfResolvedHomComparison_sourceShift]
    _ ↔ QuasiIsoAt ((CategoryTheory.shiftFunctor (Complex A) (-s)).map a) 0 :=
      quasiIsoAt_iff_comp_left eS.hom _ 0
    _ ↔ QuasiIsoAt a (-s) := CochainComplex.quasiIsoAt_shift_iff a (-s) 0 (-s) (by omega)

/-- 全 Hom の擬同型条件を全ての源 shift の H⁰ 条件として検査できる。 -/
lemma criterionPerfResolvedHomComparison_quasiIso_iff_shifts (M N : RightModule A D)
    (R : ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj M))) :
    QuasiIso (criterionPerfResolvedHomComparison A D E F M N R) ↔
      ∀ s : ℤ, QuasiIsoAt (criterionPerfResolvedHomComparison A D E F (shiftModule s M) N
        (criterionPerfDGFunctorShiftResolution A D E F M R s)) 0 := by
  constructor
  · intro h s
    apply (criterionPerfResolvedHomComparison_shift_zero_iff A D E F M N R s).2
    exact h.quasiIsoAt (-s)
  · intro h
    rw [quasiIso_iff]
    intro i
    simpa only [neg_neg] using
      (criterionPerfResolvedHomComparison_shift_zero_iff A D E F M N R (-i)).1 (h (-i))

end SerrePositivity.DifferentialGraded.Morita
