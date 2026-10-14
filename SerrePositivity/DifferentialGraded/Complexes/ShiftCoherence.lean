module
public import SerrePositivity.DifferentialGraded.Complexes.Shift

/-! # 零・加法 shift 比較の全次数自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- cochain の始域次数の輸送は XIsoOfEq の前合成。 -/
lemma homogeneous_XIsoOfEq_hom_comp {P Q : Complex A} {p i i' j : ℤ}
    (f : Homogeneous P Q p) (hi : i = i') (hij : i' + p = j) :
    (P.XIsoOfEq hi).hom ≫ f.v i' j hij = f.v i j (by omega) := by
  subst i'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]

/-- Mathlib の零 shift 比較は全次数 Hom に対して自然。 -/
lemma shiftHom_zero_naturality (P Q : Complex A) :
    shiftHom 0 P Q ≫ homPostcompose (P⟦(0 : ℤ)⟧)
      ((shiftFunctorZero (Complex A) ℤ).hom.app Q) =
    homPrecompose ((shiftFunctorZero (Complex A) ℤ).hom.app P) Q := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro i j hij
  change (((shiftHom 0 P Q).f p f).comp
    (Cochain.ofHom ((shiftFunctorZero (Complex A) ℤ).hom.app Q)) (add_zero p)).v i j hij =
    ((Cochain.ofHom ((shiftFunctorZero (Complex A) ℤ).hom.app P)).comp f
      (zero_add p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, shiftHom_v]
  simp only [zero_mul, Int.negOnePow_zero, one_smul,
    CochainComplex.shiftFunctorZero_hom_app_f]
  rw [Cochain.v_comp_XIsoOfEq_hom, homogeneous_XIsoOfEq_hom_comp]

/-- Mathlib の加法 shift 比較は全次数 Hom に対して自然。 -/
lemma shiftHom_add_naturality (s t : ℤ) (P Q : Complex A) :
    shiftHom (s + t) P Q ≫ homPostcompose (P⟦s + t⟧)
      ((shiftFunctorAdd (Complex A) s t).hom.app Q) =
    shiftHom s P Q ≫ shiftHom t (P⟦s⟧) (Q⟦s⟧) ≫
      homPrecompose ((shiftFunctorAdd (Complex A) s t).hom.app P) ((Q⟦s⟧)⟦t⟧) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro i j hij
  change (((shiftHom (s + t) P Q).f p f).comp
    (Cochain.ofHom ((shiftFunctorAdd (Complex A) s t).hom.app Q)) (add_zero p)).v i j hij =
    ((Cochain.ofHom ((shiftFunctorAdd (Complex A) s t).hom.app P)).comp
      ((shiftHom t (P⟦s⟧) (Q⟦s⟧)).f p ((shiftHom s P Q).f p f))
      (zero_add p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, shiftHom_v, shiftHom_v, shiftHom_v]
  simp only [CochainComplex.shiftFunctorAdd_hom_app_f,
    Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  rw [Cochain.v_comp_XIsoOfEq_hom, homogeneous_XIsoOfEq_hom_comp]
  rw [← Int.negOnePow_add]
  congr 1
  congr 1
  ring
end SerrePositivity.DifferentialGraded
