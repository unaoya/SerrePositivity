module
public import SerrePositivity.DifferentialGraded.Complexes.Shift

/-! # 互いに逆な斉次cochainによるshiftの表示 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {K L : Complex A} {s : ℤ}
variable (α : Cochain K L s) (hα : δ s (s + 1) α = 0)

/-- 閉じた次数sのcochainが定めるK→L[s]。 -/
def complexShiftComparison : K ⟶ L⟦s⟧ :=
  Cocycle.equivHomShift.symm (Cocycle.mk α (s + 1) rfl hα)

lemma complexShiftComparison_f (i : ℤ) :
    (complexShiftComparison A α hα).f i = α.v i (i + s) rfl := by
  simp only [complexShiftComparison, Cocycle.equivHomShift_symm_apply,
    Cocycle.homOf_f, Cocycle.rightShift_coe, Cocycle.mk_coe]
  rw [Cochain.rightShift_v _ s 0 (zero_add s) i i (add_zero i) (i + s) rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]

lemma complexShiftComparison_bijective (β : Cochain L K (-s))
    (hαβ : α.comp β (add_neg_cancel s) = Cochain.ofHom (𝟙 K))
    (hβα : β.comp α (neg_add_cancel s) = Cochain.ofHom (𝟙 L)) (i : ℤ) :
    Function.Bijective ((complexShiftComparison A α hα).f i) := by
  let ψ : L.X (i + s) → K.X i := β.v (i + s) i (by omega)
  have hl : Function.LeftInverse ψ ((complexShiftComparison A α hα).f i) := by
    intro z
    have h := Cochain.congr_v hαβ i i (add_zero i)
    rw [Cochain.comp_v _ _ _ i (i + s) i rfl (by omega), Cochain.ofHom_v, id_f] at h
    have hz := congrArg (fun f => f z) h
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hz
    rw [complexShiftComparison_f]
    exact hz
  have hr : Function.RightInverse ψ ((complexShiftComparison A α hα).f i) := by
    intro z
    have h := Cochain.congr_v hβα (i + s) (i + s) (add_zero (i + s))
    rw [Cochain.comp_v _ _ _ (i + s) i (i + s) (by omega) rfl, Cochain.ofHom_v, id_f] at h
    have hz := congrArg (fun f => f z) h
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hz
    rw [complexShiftComparison_f]
    exact hz
  exact ⟨hl.injective, hr.surjective⟩

lemma complexShiftComparison_isIso (β : Cochain L K (-s))
    (hαβ : α.comp β (add_neg_cancel s) = Cochain.ofHom (𝟙 K))
    (hβα : β.comp α (neg_add_cancel s) = Cochain.ofHom (𝟙 L)) :
    IsIso (complexShiftComparison A α hα) := by
  have (i : ℤ) : IsIso ((complexShiftComparison A α hα).f i) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (complexShiftComparison_bijective A α hα β hαβ hβα i)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 次数sと−sの逆なcochainから得られる実際のshift同型。 -/
def complexShiftIso (β : Cochain L K (-s))
    (hαβ : α.comp β (add_neg_cancel s) = Cochain.ofHom (𝟙 K))
    (hβα : β.comp α (neg_add_cancel s) = Cochain.ofHom (𝟙 L)) : K ≅ L⟦s⟧ := by
  have := complexShiftComparison_isIso A α hα β hαβ hβα
  exact asIso (complexShiftComparison A α hα)

/-- 逆cochainの次数を任意のtで指定する版。 -/
def complexShiftIsoOfSumZero {t : ℤ} (β : Cochain L K t) (hst : s + t = 0)
    (hαβ : α.comp β hst = Cochain.ofHom (𝟙 K))
    (hβα : β.comp α (by omega : t + s = 0) = Cochain.ofHom (𝟙 L)) : K ≅ L⟦s⟧ := by
  have ht : t = -s := by omega
  subst t
  exact complexShiftIso A α hα β hαβ hβα

end SerrePositivity.DifferentialGraded
