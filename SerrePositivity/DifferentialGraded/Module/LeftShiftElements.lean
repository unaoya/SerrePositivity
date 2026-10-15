module
public import SerrePositivity.DifferentialGraded.Module.HomElements
public import SerrePositivity.DifferentialGraded.Module.Shift
public import SerrePositivity.DifferentialGraded.Module.Postcomposition

/-! # 主Hom endの始域だけをshiftする斉次要素

成分はMathlibのleftShiftそのもの。次数はqからq+sへ移り、微分に(-1)^sを伴う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomLeftShift_naturality (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (z : (moduleHom A D M N).X q)
    (x y : Dᵒᵖ) (p : ℤ) (a : GradedHom A x y p) :
    (((shiftModule s M).map x y).f p a).comp
      (((moduleHomπ A D M N y.unop).f q z).leftShift s q' hqq') (by omega : p + q' = q' + p) =
      (q' * p).negOnePow •
        ((((moduleHomπ A D M N x.unop).f q z).leftShift s q' hqq').comp
          ((N.map x y).f p a) rfl) := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ _ i (i + q') j rfl (by omega),
    shiftModule_map_v,
    Cochain.leftShift_v _ s q' hqq' (i + p) j (by omega) (i + p + s) (by omega),
    Cochain.leftShift_v _ s q' hqq' i (i + q') rfl (i + s) (by omega)]
  simp only [shiftFunctor_obj_X, Opposite.op_unop,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.id_comp,
    Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  have hz := Cochain.congr_v (moduleHomElement_naturality A D q z x y p a)
    (i + s) j (by omega)
  rw [Cochain.comp_v _ _ _ (i + s) (i + p + s) j (by omega) (by omega),
    Cochain.units_smul_v, Cochain.comp_v _ _ _ (i + s) (i + q') j (by omega) (by omega)] at hz
  rw [hz]
  simp only [smul_smul]
  congr 1
  simp only [← Int.negOnePow_add]
  congr 1
  rw [← hqq']
  ring

/-- 自然な次数qの要素を、始域shift後の次数q'へ移す。 -/
def moduleHomLeftShiftElement (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (z : (moduleHom A D M N).X q) :
    (moduleHom A D (shiftModule s M) N).X q' :=
  moduleHomElementMk A D q'
    (fun x => ((moduleHomπ A D M N x.unop).f q z).leftShift s q' hqq')
    (moduleHomLeftShift_naturality A D s hqq' z)

lemma moduleHomLeftShiftElement_π (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (z : (moduleHom A D M N).X q) (x : D) :
    (moduleHomπ A D (shiftModule s M) N x).f q' (moduleHomLeftShiftElement A D s hqq' z) =
      ((moduleHomπ A D M N x).f q z).leftShift s q' hqq' :=
  moduleHomElementMk_π A D q' _ _ x

lemma moduleHomLeftShiftElement_d (s : ℤ) {M N : RightModule A D} {q q' r r' : ℤ}
    (hqq' : q + s = q') (hrr' : r + s = r') (z : (moduleHom A D M N).X q) :
    (moduleHom A D (shiftModule s M) N).d q' r' (moduleHomLeftShiftElement A D s hqq' z) =
      s.negOnePow • moduleHomLeftShiftElement A D s hrr' ((moduleHom A D M N).d q r z) := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleHomLeftShiftElement_π]
  simp only [Units.smul_def, map_zsmul]
  rw [moduleHomLeftShiftElement_π, moduleHomElement_d_π, Cochain.δ_leftShift]
  rfl

lemma moduleHomLeftShiftElement_add (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (z w : (moduleHom A D M N).X q) :
    moduleHomLeftShiftElement A D s hqq' (z + w) =
      moduleHomLeftShiftElement A D s hqq' z + moduleHomLeftShiftElement A D s hqq' w := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomLeftShiftElement_π, map_add, Cochain.leftShift_add, map_add,
    moduleHomLeftShiftElement_π, moduleHomLeftShiftElement_π]

lemma moduleHomLeftShiftElement_smul (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (a : A) (z : (moduleHom A D M N).X q) :
    moduleHomLeftShiftElement A D s hqq' (a • z) =
      a • moduleHomLeftShiftElement A D s hqq' z := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomLeftShiftElement_π, map_smul, Cochain.leftShift_smul, map_smul,
    moduleHomLeftShiftElement_π]

lemma moduleHomLeftShiftElement_injective (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') : Function.Injective
      (moduleHomLeftShiftElement A D s (M := M) (N := N) hqq') := by
  intro z w h
  apply moduleHomElement_ext A D
  intro x
  have hx := congrArg ((moduleHomπ A D (shiftModule s M) N x).f q') h
  rw [moduleHomLeftShiftElement_π, moduleHomLeftShiftElement_π] at hx
  exact (Cochain.leftShiftLinearEquiv A (M.obj (op x)) (N.obj (op x)) q s q' hqq').injective hx


lemma moduleHomLeftShiftElement_zero (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') :
    moduleHomLeftShiftElement A D s (M := M) (N := N) hqq' 0 = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomLeftShiftElement_π, map_zero, Cochain.leftShift_zero, map_zero]

lemma moduleHomLeftShiftElement_neg (s : ℤ) {M N : RightModule A D} {q q' : ℤ}
    (hqq' : q + s = q') (z : (moduleHom A D M N).X q) :
    moduleHomLeftShiftElement A D s hqq' (-z) = -moduleHomLeftShiftElement A D s hqq' z := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomLeftShiftElement_π, map_neg, Cochain.leftShift_neg, map_neg,
    moduleHomLeftShiftElement_π]

lemma moduleHomLeftShiftElement_postcompose (s : ℤ) {M N P : ModuleCategory A D} {q q' : ℤ}
    (hqq' : q + s = q') (z : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).X q) (f : N ⟶ P) :
    moduleHomLeftShiftElement A D s hqq' ((eHomWhiskerLeft (Complex A) M f).f q z) =
      (eHomWhiskerLeft (Complex A) (moduleShiftObj A D s M) f).f q'
        (moduleHomLeftShiftElement A D s hqq' z) := by
  apply moduleHomElement_ext A D
    (M := shiftModule s (ForgetEnrichment.to (Complex A) M))
    (N := ForgetEnrichment.to (Complex A) P)
  intro x
  have h₁ := moduleHomWhiskerLeft_apply_π A D (T := M) f q z x
  have h₂ := moduleHomWhiskerLeft_apply_π A D (T := moduleShiftObj A D s M)
    f q' (moduleHomLeftShiftElement A D s hqq' z) x
  rw [moduleHomLeftShiftElement_π]
  have h₃ := congrArg (fun c => c.leftShift s q' hqq') h₁
  exact h₃.trans ((Cochain.leftShift_comp_zero_cochain _ s q' hqq' _).trans
    ((congrArg (fun c => c.comp (Cochain.ofHom ((moduleEvaluation A D x).map f)) (add_zero q'))
      (moduleHomLeftShiftElement_π A D s hqq' z x).symm).trans h₂.symm))

end SerrePositivity.DifferentialGraded
