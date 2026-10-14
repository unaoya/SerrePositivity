module
public import SerrePositivity.DifferentialGraded.Complexes.ClosedMaps
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # 零複体を始域・終域に持つ全次数 Hom -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open scoped ZeroObject
variable {A : Type u} [CommRing A] {P Q : Complex A}

/-- 閉零複体から通常複体への比較は加法を保存する。 -/
instance closedToComplexAdditive : (closedToComplex A).Additive where
  map_add := by
    intro X Y f g
    apply Cochain.ofHom_injective
    rw [Cochain.ofHom_add]
    simp only [closedToComplex, complexClosedHomEquiv_cochain]
    rfl

/-- 零複体を始域に持つ斉次 cochain は全次数で零。 -/
lemma homogeneous_eq_zero_of_isZero_src (hP : IsZero P) {n : ℤ}
    (f : Homogeneous P Q n) : f = 0 := by
  apply Cochain.ext
  intro i j hij
  exact ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) i).map_isZero hP).eq_of_src _ _

/-- 零複体を終域に持つ斉次 cochain は全次数で零。 -/
lemma homogeneous_eq_zero_of_isZero_tgt (hQ : IsZero Q) {n : ℤ}
    (f : Homogeneous P Q n) : f = 0 := by
  apply Cochain.ext
  intro i j hij
  exact ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) j).map_isZero hQ).eq_of_tgt _ _

/-- 零複体からの線形 Hom 複体は零対象。 -/
lemma homComplex_isZero_src (hP : IsZero P) : IsZero (homComplex A P Q) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact homogeneous_eq_zero_of_isZero_src hP f

/-- 零複体への線形 Hom 複体は零対象。 -/
lemma homComplex_isZero_tgt (hQ : IsZero Q) : IsZero (homComplex A P Q) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact homogeneous_eq_zero_of_isZero_tgt hQ f
end SerrePositivity.DifferentialGraded
