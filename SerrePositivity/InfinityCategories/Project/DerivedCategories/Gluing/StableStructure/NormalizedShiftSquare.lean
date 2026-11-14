module
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! 正規化シフト同型で移送した augmentation の、全次数の厳密な射影正方形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (C : Type w) [DGCategory R C] [Small.{u} C]
  (F : DGFunctor R (RightModule R D) (RightModule R C))
  (U : RightModule R D) (V : RightModule R C) (n : ℤ)
  (a : ForgetEnrichment.of (Complex R) V ⟶ ForgetEnrichment.of (Complex R) (F.obj U))

/-- シフト元の標準斉次射影は、正規化して移送した同じ augmentation と可換。 -/
lemma dgGluingNormalizedShiftSquare :
    (eHomWhiskerRight (Complex R)
      (moduleShiftMap R C n a ≫ (normalizedDGModuleFunctorShiftIso R D C F n U).inv)
      (ForgetEnrichment.of (Complex R) (F.obj U))).f n
        ((F.map (shiftModule n U) U).f n (normalizedModuleShiftOut R D n U)) =
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (shiftModule n V)) a).f n
        (normalizedModuleShiftOut R C n V) := by
  apply moduleHomElement_ext R C
  intro c
  have hl := moduleHomWhiskerRight_apply_π R C
    (M := ForgetEnrichment.of (Complex R) (shiftModule n V))
    (N := ForgetEnrichment.of (Complex R) (F.obj (shiftModule n U)))
    (P := ForgetEnrichment.of (Complex R) (F.obj U))
    (moduleShiftMap R C n a ≫ (normalizedDGModuleFunctorShiftIso R D C F n U).inv)
    n ((F.map (shiftModule n U) U).f n (normalizedModuleShiftOut R D n U)) c
  have hr := moduleHomWhiskerLeft_apply_π R C
    (T := ForgetEnrichment.of (Complex R) (shiftModule n V))
    (M := ForgetEnrichment.of (Complex R) V)
    (N := ForgetEnrichment.of (Complex R) (F.obj U)) a n
    (normalizedModuleShiftOut R C n V) c
  refine hl.trans (Eq.trans ?_ hr.symm)
  apply Cochain.ext
  intro i j hij
  subst j
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v]
  change (((moduleEvaluation R C c).map
    (moduleShiftMap R C n a ≫ (normalizedDGModuleFunctorShiftIso R D C F n U).inv)).f i) ≫
    (((moduleHomπ R C (F.obj (shiftModule n U)) (F.obj U) c).f n
      ((F.map (shiftModule n U) U).f n (normalizedModuleShiftOut R D n U))).v
        i (i + n) rfl) =
    (((moduleHomπ R C (shiftModule n V) V c).f n (normalizedModuleShiftOut R C n V)).v
      i (i + n) rfl) ≫ ((moduleEvaluation R C c).map a).f (i + n)
  rw [normalizedModuleShiftOut_v, Category.id_comp]
  rw [← normalizedDGModuleFunctorShiftIso_hom_eval_f,
    CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f, Category.assoc]
  have h := congrArg (fun f => ((moduleEvaluation R C c).map f).f i)
    (normalizedDGModuleFunctorShiftIso R D C F n U).inv_hom_id
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    HomologicalComplex.comp_f, HomologicalComplex.id_f] at h
  rw [h]
  erw [Category.comp_id, moduleShiftMap_eval]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
