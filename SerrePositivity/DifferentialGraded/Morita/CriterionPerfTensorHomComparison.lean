module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfResolvedAction

/-! # 列の全 Hom 比較と、表現可能入力の tensor の全 Hom 比較の同定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

private lemma homComparison_resolution_square
    {B : Type*} [Category* B] [EnrichedOrdinaryCategory (Complex A) B]
    {U U' V V' T : B} {H : Complex A}
    (f : H ⟶ (U ⟶[Complex A] U')) (g : H ⟶ (V ⟶[Complex A] V'))
    (e : U ≅ V) (e' : U' ≅ V')
    (h : f ≫ eHomWhiskerLeft (Complex A) U e'.hom =
      g ≫ eHomWhiskerRight (Complex A) e.hom V') (r : T ⟶ V) :
    f ≫ eHomWhiskerRight (Complex A) (r ≫ e.inv) U' ≫
        eHomWhiskerLeft (Complex A) T e'.hom =
      g ≫ eHomWhiskerRight (Complex A) r V' := by
  simp only [eHomWhiskerRight_comp, Category.assoc]
  rw [← eHom_whisker_exchange, ← eHom_whisker_exchange_assoc]
  rw [reassoc_of% h, ← eHomWhiskerRight_comp_assoc, e.inv_hom_id,
    eHomWhiskerRight_id, Category.id_comp]

def criterionPerfTensorRepresentableResolution (d : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    ModuleProjectiveResolution A E
      ((kernelTensor A D E P).onClosed.obj
        (ForgetEnrichment.of (Complex A) (representable A d))) where
  obj := R.obj
  π := R.π ≫ (BimoduleTensor.rightUnitIso A E D P d).inv
  projective := R.projective
  quasiIso := by
    intro e
    rw [CategoryTheory.Functor.map_comp]
    have := R.quasiIso e
    infer_instance

lemma criterionPerfTensorYonedaHom_naturality (d d' : D) :
    yonedaHom A D d d' ≫ (kernelTensor A D E P).map (representable A d) (representable A d') ≫
      eHomWhiskerLeft (Complex A)
        (ForgetEnrichment.of (Complex A) ((kernelTensor A D E P).obj (representable A d)))
        (BimoduleTensor.rightUnitIso A E D P d').hom =
    P.toFunctor.map d d' ≫ eHomWhiskerRight (Complex A)
      (BimoduleTensor.rightUnitIso A E D P d).hom (criterionPerfColumn A D E P d') := by
  have h := BimoduleTensor.rightUnitIso_naturality A E D P d d'
  have he : yonedaHom A D d d' ≫
      (kernelTensor A D E P).map (representable A d) (representable A d') =
      (BimoduleTensor.compose A E D D P (Bimodule.diagonal A D)).toFunctor.map d d' := by
    apply moduleHom_ext A E
    intro e
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => yonedaHom A D d d' ≫ k)
        (kernelTensor_map_π A D E P (representable A d) (representable A d') e)).trans
          (BimoduleTensor.compose_leftMap_π A E D D P (Bimodule.diagonal A D) d d' e).symm)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ eHomWhiskerLeft (Complex A)
      (ForgetEnrichment.of (Complex A) ((kernelTensor A D E P).obj (representable A d)))
      (BimoduleTensor.rightUnitIso A E D P d').hom) he).trans h)

lemma criterionPerfTensorHomComparison_square (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    yonedaHom A D d d' ≫
        criterionPerfResolvedHomComparison A D E (kernelTensor A D E P)
          (representable A d) (representable A d')
          (criterionPerfTensorRepresentableResolution A D E P d R) ≫
        eHomWhiskerLeft (Complex A) R.obj (BimoduleTensor.rightUnitIso A E D P d').hom =
      criterionPerfHomComparison A D E P d d' R := by
  have h := homComparison_resolution_square A
    (yonedaHom A D d d' ≫ (kernelTensor A D E P).map (representable A d) (representable A d'))
    (P.toFunctor.map d d') (BimoduleTensor.rightUnitIso A E D P d)
    (BimoduleTensor.rightUnitIso A E D P d')
    (by
      have h0 := criterionPerfTensorYonedaHom_naturality A D E P d d'
      simp only [Category.assoc] at h0 ⊢
      exact h0) R.π
  simp only [criterionPerfResolvedHomComparison, criterionPerfTensorRepresentableResolution,
    criterionPerfHomComparison, Category.assoc] at h ⊢
  exact h

lemma criterionPerfTensorHomComparison_quasiIso_iff (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    QuasiIso (criterionPerfHomComparison A D E P d d' R) ↔
      QuasiIso (criterionPerfResolvedHomComparison A D E (kernelTensor A D E P)
        (representable A d) (representable A d')
        (criterionPerfTensorRepresentableResolution A D E P d R)) := by
  have : QuasiIso (yonedaHom A D d d') := by
    change QuasiIso (dgYonedaIso A d (representable A d')).inv
    infer_instance
  let p := eHomWhiskerLeft (Complex A) R.obj (BimoduleTensor.rightUnitIso A E D P d').hom
  have : IsIso p := by
    change IsIso (((eHomFunctor (Complex A) (ModuleCategory A E)).obj (Opposite.op R.obj)).map
      (BimoduleTensor.rightUnitIso A E D P d').hom)
    infer_instance
  rw [← criterionPerfTensorHomComparison_square A D E P d d' R]
  exact (quasiIso_iff_comp_left (yonedaHom A D d d') (_ ≫ p)).trans
    (quasiIso_iff_comp_right _ p)

/-- 元の列の全 Hom 比較は、表現可能入力の全源 shift 上の主作用で検査できる。 -/
lemma criterionPerfHomComparison_quasiIso_iff_sourceShifts (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    QuasiIso (criterionPerfHomComparison A D E P d d' R) ↔
      ∀ s : ℤ, Function.Bijective
        ((kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
          (X := (moduleToDerived A D).obj
            ((ForgetEnrichment.of (Complex A) (representable A d))⟦s⟧))
          (Y := criterionPerfRepresentable A D d')) :=
  (criterionPerfTensorHomComparison_quasiIso_iff A D E P d d' R).trans
    (criterionPerfResolvedAction_quasiIso_iff_sourceShifts A D E P
      (representable_homotopicallyProjective A D d)
      (representable_homotopicallyProjective A D d')
      (criterionPerfTensorRepresentableResolution A D E P d R))

end SerrePositivity.DifferentialGraded.Morita
