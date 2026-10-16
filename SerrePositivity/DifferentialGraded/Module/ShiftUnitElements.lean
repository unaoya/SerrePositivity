module
public import SerrePositivity.DifferentialGraded.Complexes.HomogeneousTransport
public import SerrePositivity.DifferentialGraded.Module.LeftShiftElements
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Module.Composition

/-! # 加群shiftの互いに逆な斉次単位要素 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Mathlib leftShiftの単位上の定数符号を保持した次数sの射影。 -/
def moduleShiftOutElement (s : ℤ) (M : RightModule A D) :
    (moduleHom A D (shiftModule s M) M).X s :=
  moduleHomLeftShiftElement A D s (zero_add s) (unitElement A M).val

lemma moduleShiftOutElement_π (s : ℤ) (M : RightModule A D) (x : D) :
    (moduleHomπ A D (shiftModule s M) M x).f s (moduleShiftOutElement A D s M) =
      (Cochain.ofHom (𝟙 (M.obj (op x)))).leftShift s s (zero_add s) := by
  rw [moduleShiftOutElement, moduleHomLeftShiftElement_π, yoneda_moduleUnit_π]

lemma moduleShiftOutElement_d (s : ℤ) (M : RightModule A D) :
    (moduleHom A D (shiftModule s M) M).d s (s + 1) (moduleShiftOutElement A D s M) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleShiftOutElement_π, map_zero,
    Cochain.δ_leftShift _ s s (s + 1) (zero_add s) 1 (by omega)]
  simp only [δ_ofHom, Cochain.leftShift_zero, smul_zero]

omit [Small.{u} D] in
lemma moduleShiftIn_naturality (s : ℤ) (M : RightModule A D)
    (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p) :
    ((M.map x y).f p f).comp
        ((Cochain.ofHom (𝟙 (M.obj y))).rightShift s (-s) (neg_add_cancel s)) (by omega) =
      ((-s) * p).negOnePow •
        (((Cochain.ofHom (𝟙 (M.obj x))).rightShift s (-s) (neg_add_cancel s)).comp
          (((shiftModule s M).map x y).f p f) rfl) := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_v _ _ _ i (i + p) j rfl (by omega), Cochain.units_smul_v,
    Cochain.comp_v _ _ _ i (i - s) j (by omega) (by omega), shiftModule_map_v,
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) (i + p) j (by omega) (i + p) (add_zero _),
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) i (i - s) (by omega) i (add_zero _)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f,
    CochainComplex.shiftFunctorObjXIso, Category.id_comp,
    Linear.comp_units_smul, smul_smul, ← Int.negOnePow_add]
  have h : (-s) * p + s * p = 0 := by ring
  rw [h, Int.negOnePow_zero, one_smul]
  rw [Cochain.v_comp_XIsoOfEq_inv, homogeneous_XIsoOfEq_inv_comp]

/-- 次数−sの包含。射影の定数符号を掛け、通常順の両合成を単位にする。 -/
def moduleShiftInElement (s : ℤ) (M : RightModule A D) :
    (moduleHom A D M (shiftModule s M)).X (-s) :=
  (s * s + s * (s - 1) / 2).negOnePow •
    moduleHomElementMk A D (-s)
      (fun x => (Cochain.ofHom (𝟙 (M.obj x))).rightShift s (-s) (neg_add_cancel s))
      (moduleShiftIn_naturality A D s M)

lemma moduleShiftInElement_π (s : ℤ) (M : RightModule A D) (x : D) :
    (moduleHomπ A D M (shiftModule s M) x).f (-s) (moduleShiftInElement A D s M) =
      (s * s + s * (s - 1) / 2).negOnePow •
        (Cochain.ofHom (𝟙 (M.obj (op x)))).rightShift s (-s) (neg_add_cancel s) := by
  simp only [moduleShiftInElement, Units.smul_def, map_zsmul, moduleHomElementMk_π]

end SerrePositivity.DifferentialGraded
