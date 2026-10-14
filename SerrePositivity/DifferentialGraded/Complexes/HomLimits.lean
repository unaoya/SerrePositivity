module
public import SerrePositivity.DifferentialGraded.Complexes.ClosedMaps
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # 全次数 Hom の極限射影による判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {J : Type w} [Category.{w'} J]

/-- 指定された複体極限への全次数 Hom は射影後の成分で判定できる。 -/
lemma homComplex_limit_ext (F : J ⥤ Complex A) [HasLimit F] {P K : Complex A}
    {f g : K ⟶ homComplex A P (limit F)}
    (h : ∀ j, f ≫ homPostcompose P (limit.π F j) =
      g ≫ homPostcompose P (limit.π F j)) : f = g := by
  apply (tensorRightHomEquiv P K (limit F)).symm.injective
  change uncurryRight f = uncurryRight g
  apply limit.hom_ext
  intro j
  apply (tensorRightHomEquiv P K (F.obj j)).injective
  change curryRight (uncurryRight f ≫ limit.π F j) =
    curryRight (uncurryRight g ≫ limit.π F j)
  rw [curryRight_naturality_target, curryRight_naturality_target,
    curryRight_uncurryRight, curryRight_uncurryRight]
  exact h j

/-- Hom の単位を前合成・後合成で移す二通りは一致する。 -/
lemma identity_hom_naturality {P Q : Complex A} (f : P ⟶ Q) :
    identity P ≫ homPostcompose P f = identity Q ≫ homPrecompose f Q := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (identity P ≫ homPostcompose P f)).val =
    (cycleFromUnit _ (identity Q ≫ homPrecompose f Q)).val
  rw [cycleFromUnit_postcomp, cycleFromUnit_postcomp]
  simp only [identity, cycleFromUnit_unitFromCycle]
  change (Cochain.ofHom (𝟙 P)).comp (Cochain.ofHom f) (add_zero 0) =
    (Cochain.ofHom f).comp (Cochain.ofHom (𝟙 Q)) (zero_add 0)
  rw [Cochain.id_comp, Cochain.comp_id]
end SerrePositivity.DifferentialGraded
