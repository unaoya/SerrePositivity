module
public import SerrePositivity.DifferentialGraded.Endomorphism.ShiftAdditionElements

/-! # 正規化shift比較と加法shiftの整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma normalizedDGModuleFunctorShiftIso_add_square (s t : ℤ) (M : RightModule A D) :
    F.onClosed.map (moduleShiftAddIsoObj A D s t M).hom ≫
        (normalizedDGModuleFunctorShiftIso A D B F t (shiftModule s M)).hom ≫
        (moduleShiftFunctor A B t).map (normalizedDGModuleFunctorShiftIso A D B F s M).hom =
      (normalizedDGModuleFunctorShiftIso A D B F (s + t) M).hom ≫
        (moduleShiftAddIsoObj A B s t (F.obj M)).hom := by
  apply moduleMorphism_ext
  intro b
  apply HomologicalComplex.hom_ext
  intro i
  let G := F.comp (moduleEvaluationDG A B b)
  have h := congrArg (fun z => (G.map (shiftModule (s + t) M) M).f (s + t) z)
    (normalizedModuleShiftOut_add A D s t M)
  rw [G.map_forward_cochain A, G.map_compose_cochain A] at h
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  have hc : (G.map (shiftModule (s + t) M) (shiftModule t (shiftModule s M))).f 0
      (endomorphismClosedElement A D (moduleShiftAddIsoObj A D s t M).hom) =
      Cochain.ofHom ((G.toComplexFunctor A).map (moduleShiftAddIsoObj A D s t M).hom) :=
    G.map_closedElement A (moduleShiftAddIsoObj A D s t M).hom
  rw [hc] at h
  have hv := Cochain.congr_v h i ((i + t) + s) (by omega)
  rw [Cochain.zero_cochain_comp_v,
    Cochain.comp_v _ _ _ i (i + t) ((i + t) + s) rfl rfl,
    Cochain.ofHom_v] at hv
  rw [← Cochain.v_comp_XIsoOfEq_hom _ i (i + (s + t)) ((i + t) + s) rfl (by omega)] at hv
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    normalizedDGModuleFunctorShiftIso_hom_eval_f,
    normalizedDGModuleFunctorShiftIso_hom_eval_f,
    moduleShiftAddIsoObj_hom_eval, shiftFunctorAdd_hom_app_f]
  change _ ≫ (_ ≫ (((moduleEvaluation A B b).map
    (moduleShiftMap A B t (normalizedDGModuleFunctorShiftIso A D B F s M).hom)).f i)) = _
  rw [moduleShiftMap_eval]
  change _ ≫ (_ ≫ ((moduleEvaluation A B b).map
    (normalizedDGModuleFunctorShiftIso A D B F s M).hom).f (i + t)) = _
  rw [normalizedDGModuleFunctorShiftIso_hom_eval_f]
  exact hv

lemma shiftComparison_eq_isoAdd_of_square {C E : Type*} [Category* C] [Category* E]
    [HasShift C ℤ] [HasShift E ℤ] (H : C ⥤ E) (s t : ℤ)
    (es : CategoryTheory.shiftFunctor C s ⋙ H ≅ H ⋙ CategoryTheory.shiftFunctor E s)
    (et : CategoryTheory.shiftFunctor C t ⋙ H ≅ H ⋙ CategoryTheory.shiftFunctor E t)
    (est : CategoryTheory.shiftFunctor C (s + t) ⋙ H ≅ H ⋙ CategoryTheory.shiftFunctor E (s + t))
    (h : ∀ X, H.map ((shiftFunctorAdd C s t).hom.app X) ≫
      et.hom.app ((CategoryTheory.shiftFunctor C s).obj X) ≫
      (CategoryTheory.shiftFunctor E t).map (es.hom.app X) =
        est.hom.app X ≫ (shiftFunctorAdd E s t).hom.app (H.obj X)) :
    est = CategoryTheory.Functor.CommShift.isoAdd es et := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  rw [CategoryTheory.Functor.CommShift.isoAdd_hom_app]
  rw [← cancel_mono ((shiftFunctorAdd E s t).hom.app (H.obj X))]
  simp only [Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.comp_obj, Category.comp_id]
  exact (h X).symm

/-- 登録済みshiftの型へ、関手の等式を明示的に用いて移す。 -/
def normalizedDGModuleFunctorCommShiftIso (s : ℤ) :
    CategoryTheory.shiftFunctor (ModuleCategory A D) s ⋙ F.onClosed ≅
      F.onClosed ⋙ CategoryTheory.shiftFunctor (ModuleCategory A B) s := by
  rw [moduleShiftFunctor_eq, moduleShiftFunctor_eq]
  exact normalizedDGModuleFunctorShiftNatIso A D B F s

lemma normalizedDGModuleFunctorCommShiftIso_zero :
    normalizedDGModuleFunctorCommShiftIso A D B F 0 =
      CategoryTheory.Functor.CommShift.isoZero F.onClosed ℤ := by
  exact normalizedDGModuleFunctorShiftNatIso_zero A D B F

lemma normalizedDGModuleFunctorShiftNatIso_add (s t : ℤ) :
    normalizedDGModuleFunctorCommShiftIso A D B F (s + t) =
      CategoryTheory.Functor.CommShift.isoAdd
        (C := ModuleCategory A D) (D := ModuleCategory A B) (A := ℤ)
        (F := F.onClosed) (a := s) (b := t)
        (normalizedDGModuleFunctorCommShiftIso A D B F s)
        (normalizedDGModuleFunctorCommShiftIso A D B F t) := by
  apply shiftComparison_eq_isoAdd_of_square
    (C := ModuleCategory A D) (E := ModuleCategory A B) F.onClosed s t
    (normalizedDGModuleFunctorCommShiftIso A D B F s)
    (normalizedDGModuleFunctorCommShiftIso A D B F t)
    (normalizedDGModuleFunctorCommShiftIso A D B F (s + t))
  intro M
  simp only [moduleShiftAdd_eq, moduleShiftFunctor_eq,
    normalizedDGModuleFunctorCommShiftIso]
  exact normalizedDGModuleFunctorShiftIso_add_square A D B F s t
    (ForgetEnrichment.to (Complex A) M)

/-- 加群値dg関手の閉零関手は、正規化比較で整数shiftと整合的に可換する。 -/
@[instance_reducible]
def dgModuleFunctorCommShift : F.onClosed.CommShift ℤ where
  commShiftIso := normalizedDGModuleFunctorCommShiftIso A D B F
  commShiftIso_zero := normalizedDGModuleFunctorCommShiftIso_zero A D B F
  commShiftIso_add := normalizedDGModuleFunctorShiftNatIso_add A D B F

end SerrePositivity.DifferentialGraded
