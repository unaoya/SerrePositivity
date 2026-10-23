module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommonComplexUniverseIso

/-! 共通宇宙の canonical 変更は、逆向き標準宇宙変更の逆射と同じ実写像。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] (K : Complex R)

lemma dgGluingCommonComplexUniverse_hom_eq_inv :
    (dgGluingCommonComplexPinchedUniverseIso.{u, v, w, max u v w} K).hom =
      (dgGluingComplexPinchedUniverseIso.{u, w, v} K).inv := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories
