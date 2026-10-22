module
public import SerrePositivity.InfinityCategories.Derived.Gluing.Composition

/-! 元の比較 cochain と代表加群表示の比較 cochain の一致、および閉単位の比較成分。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : DGGluingObject R C D M)
lemma dgGluingHomRepresentableIso_primitive :
    (Cochain.ofHom (dgGluingHomRepresentableIso R C D M X Y).hom).comp
      (dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y)) (zero_add (-1)) =
    (dgGluingHomPrimitive R C D M X Y).comp
      (Cochain.ofHom (dgYonedaIso R X.left (M.rightAt Y.right)).inv) (add_zero (-1)) := by
  simp only [dgGluingHomRepresentableIso, complexMappingCoconeMapIso,
    dgFunctorCommaPrimitive, dgGluingHomPrimitive, Iso.symm_hom]
  exact complexMappingCoconeMap_snd _ _ _ _ _

lemma dgGluingHomRepresentableIso_primitive_v (p q : ℤ) (hpq : p + -1 = q) :
    (dgGluingHomRepresentableIso R C D M X Y).hom.f p ≫
      (dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y)).v p q hpq =
    (dgGluingHomPrimitive R C D M X Y).v p q hpq ≫
      (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f q := by
  have h := Cochain.congr_v (dgGluingHomRepresentableIso_primitive R C D M X Y) p q hpq
  simpa only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using h

lemma dgGluingHomComparison_yoneda (K : Complex R) (f : K ⟶ dgGluingHomComplex R C D M X Y) :
    (dgFunctorCommaHomComparison R D (RightModule R C) M.toFunctor
      (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y) K
      (f ≫ (dgGluingHomRepresentableIso R C D M X Y).hom)).comp
      (Cochain.ofHom (dgYonedaIso R X.left (M.rightAt Y.right)).hom) (add_zero (-1)) =
      dgGluingHomComparison R C D M X Y K f := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgFunctorCommaHomComparison, dgGluingHomComparison,
    Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    HomologicalComplex.comp_f]
  have hv := dgGluingHomRepresentableIso_primitive_v R C D M X Y p q hpq
  have he := congrArg (fun t ↦ f.f p ≫ t ≫
    (dgYonedaIso R X.left (M.rightAt Y.right)).hom.f q) hv
  simpa only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f, Category.comp_id] using! he

lemma dgGluingIdentity_comparison :
    dgGluingHomComparison R C D M X X _ (dgGluingIdentity R C D M X) = 0 := by
  have h := dgGluingHomComparison_yoneda R C D M X X _ (dgGluingIdentity R C D M X)
  have hi := (dgGluingToComma R C D M).map_id X
  change dgGluingIdentity R C D M X ≫ (dgGluingHomRepresentableIso R C D M X X).hom =
    dgFunctorCommaIdentity R D (RightModule R C) M.toFunctor
      (dgGluingCommaObject R C D M X) at hi
  rw [hi, dgFunctorCommaIdentity_comparison, Cochain.zero_comp] at h
  exact h.symm

end SerrePositivity.InfinityCategories
