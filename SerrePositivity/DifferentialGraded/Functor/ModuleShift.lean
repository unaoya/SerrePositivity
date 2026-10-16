module
public import SerrePositivity.DifferentialGraded.Module.ShiftUnitRelations
public import SerrePositivity.DifferentialGraded.Functor.ClosedComplex
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryHom

/-! # 複体値dg関手の加群shift比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A (RightModule A D) (Complex A))

def moduleShiftImageOut (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (shiftModule s M)) (F.obj M) s :=
  (F.map (shiftModule s M) M).f s (moduleShiftOutElement A D s M)

def moduleShiftImageIn (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj M) (F.obj (shiftModule s M)) (-s) :=
  (F.map M (shiftModule s M)).f (-s) (moduleShiftInElement A D s M)

lemma moduleShiftImageOut_d (s : ℤ) (M : RightModule A D) :
    δ s (s + 1) (moduleShiftImageOut A D F s M) = 0 := by
  have h := F.map_d_cochain A (moduleShiftOutElement A D s M) (q := s + 1)
  have hz : (F.map (shiftModule s M) M).f (s + 1)
      ((moduleHom A D (shiftModule s M) M).d s (s + 1)
        (moduleShiftOutElement A D s M)) = 0 := by
    rw [moduleShiftOutElement_d, map_zero]
  exact h.symm.trans hz

lemma moduleShiftImageOutIn (s : ℤ) (M : RightModule A D) :
    (moduleShiftImageOut A D F s M).comp (moduleShiftImageIn A D F s M)
        (add_neg_cancel s) = Cochain.ofHom (𝟙 (F.obj (shiftModule s M))) := by
  have h := congrArg (fun z => (F.map (shiftModule s M) (shiftModule s M)).f 0 z)
    (moduleShiftOutIn A D s M)
  rw [map_compose_cochain, map_unitElement, Bimodule.complex_unitElement] at h
  exact h

lemma moduleShiftImageInOut (s : ℤ) (M : RightModule A D) :
    (moduleShiftImageIn A D F s M).comp (moduleShiftImageOut A D F s M)
        (neg_add_cancel s) = Cochain.ofHom (𝟙 (F.obj M)) := by
  have h := congrArg (fun z => (F.map M M).f 0 z) (moduleShiftInOut A D s M)
  rw [map_compose_cochain, map_unitElement, Bimodule.complex_unitElement] at h
  exact h

/-- 全次数Hom写像によって得る、F(M[s])からF(M)[s]への実際のchain map。 -/
def moduleShiftImageComparison (s : ℤ) (M : RightModule A D) :
    F.obj (shiftModule s M) ⟶ (F.obj M)⟦s⟧ :=
  Cocycle.equivHomShift.symm
    (Cocycle.mk (moduleShiftImageOut A D F s M) (s + 1) rfl (moduleShiftImageOut_d A D F s M))

lemma moduleShiftImageComparison_f (s : ℤ) (M : RightModule A D) (i : ℤ) :
    (moduleShiftImageComparison A D F s M).f i =
      (moduleShiftImageOut A D F s M).v i (i + s) rfl := by
  simp only [moduleShiftImageComparison, Cocycle.equivHomShift_symm_apply,
    Cocycle.homOf_f, Cocycle.rightShift_coe, Cocycle.mk_coe]
  rw [Cochain.rightShift_v _ s 0 (zero_add s) i i (add_zero i) (i + s) rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]

/-- 比較射の各次数の逆は、次数−sの包含の像で与えられる。 -/
lemma moduleShiftImageComparison_bijective (s : ℤ) (M : RightModule A D) (i : ℤ) :
    Function.Bijective ((moduleShiftImageComparison A D F s M).f i) := by
  let ψ : (F.obj M).X (i + s) → (F.obj (shiftModule s M)).X i :=
    (moduleShiftImageIn A D F s M).v (i + s) i (by omega)
  have hl : Function.LeftInverse ψ ((moduleShiftImageComparison A D F s M).f i) := by
    intro z
    have h := Cochain.congr_v (moduleShiftImageOutIn A D F s M) i i (add_zero i)
    rw [Cochain.comp_v _ _ _ i (i + s) i rfl (by omega), Cochain.ofHom_v, id_f] at h
    have hz := congrArg (fun f => f z) h
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hz
    rw [moduleShiftImageComparison_f]
    exact hz
  have hr : Function.RightInverse ψ ((moduleShiftImageComparison A D F s M).f i) := by
    intro z
    have h := Cochain.congr_v (moduleShiftImageInOut A D F s M) (i + s) (i + s)
      (add_zero (i + s))
    rw [Cochain.comp_v _ _ _ (i + s) i (i + s) (by omega) rfl, Cochain.ofHom_v, id_f] at h
    have hz := congrArg (fun f => f z) h
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hz
    rw [moduleShiftImageComparison_f]
    exact hz
  exact ⟨hl.injective, hr.surjective⟩

instance moduleShiftImageComparison_isIso (s : ℤ) (M : RightModule A D) :
    IsIso (moduleShiftImageComparison A D F s M) := by
  have (i : ℤ) : IsIso ((moduleShiftImageComparison A D F s M).f i) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (moduleShiftImageComparison_bijective A D F s M i)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 任意複体値dg関手の、整数shiftに対する具体的比較同型。 -/
def moduleShiftImageIso (s : ℤ) (M : RightModule A D) :
    F.obj (shiftModule s M) ≅ (F.obj M)⟦s⟧ :=
  asIso (moduleShiftImageComparison A D F s M)

end SerrePositivity.DifferentialGraded.DGFunctor
