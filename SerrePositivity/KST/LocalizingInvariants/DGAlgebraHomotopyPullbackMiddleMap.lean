module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMapQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.CochainMappingCoconeMapSurjective
public import SerrePositivity.KST.LocalizingInvariants.CochainBiprodMapComposition

/-!
概要：両端を恒等で保つ cospan 比較は、中央の次数全射性と準同型性を保つ。
方針：元の二脚の差の cocone 表示で、両端の恒等と中央の射を使う。
規約：次数全射性に準同型性は要求しない。使われ方：経路の境界・底比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)

def middleMap : algebra R (𝟙 C) (𝟙 C) ⟶ algebra R p p :=
  map R (𝟙 C) (𝟙 C) p p (𝟙 C) p (𝟙 C) (by simp) (by simp)

def middleCoconeMap : CochainComplex.mappingCocone (difference R (𝟙 C) (𝟙 C)) ⟶
    CochainComplex.mappingCocone (difference R p p) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap _ _ (sumMap R (𝟙 C) (𝟙 C)) p.hom
    (difference_comm R (𝟙 C) (𝟙 C) p p (𝟙 C) p (𝟙 C) (by simp) (by simp))

lemma middleMap_cocone : (middleMap R p).hom ≫ (complexIso R p p).hom =
    (complexIso R (𝟙 C) (𝟙 C)).hom ≫ middleCoconeMap R p :=
  map_toMappingCocone R _ _ _ _ _ _ _ _ _

lemma middleMap_asCocone : (middleMap R p).hom =
    (complexIso R (𝟙 C) (𝟙 C)).hom ≫ middleCoconeMap R p ≫ (complexIso R p p).inv := by
  apply (cancel_mono (complexIso R p p).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact middleMap_cocone R p

lemma middleMap_surjective (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (n : ℤ) :
    Function.Surjective ((middleMap R p).hom.f n) := by
  have ha : Function.Surjective ((sumMap R (𝟙 C) (𝟙 C)).f n) := by
    change Function.Surjective ((biprod.map (𝟙 C.X) (𝟙 C.X)).f n)
    rw [cochainBiprodMap_id, HomologicalComplex.id_f]
    exact Function.surjective_id
  have hm : Function.Surjective ((middleCoconeMap R p).f n) :=
    cochainMappingCoconeMap_surjective _ _ _ _ _ n ha (hs (n - 1))
  rw [middleMap_asCocone, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  have h₁ : Function.Surjective (((complexIso R (𝟙 C) (𝟙 C)).hom).f n) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have h₂ : Function.Surjective (((complexIso R p p).inv).f n) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  exact h₂.comp (hm.comp h₁)

lemma middleMap_quasiIso (hq : QuasiIso p.hom) : QuasiIso (middleMap R p).hom :=
  map_quasiIso R _ _ _ _ _ _ _ _ _ (quasiIso_of_isIso _) hq (quasiIso_of_isIso _)

lemma middleMap_left : middleMap R p ≫ left R p p = left R (𝟙 C) (𝟙 C) :=
  (map_left R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma middleMap_right : middleMap R p ≫ right R p p = right R (𝟙 C) (𝟙 C) :=
  (map_right R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma middleMap_path : middleMap R p ≫ path R p p =
    path R (𝟙 C) (𝟙 C) ≫ Path.map R p := map_path R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
