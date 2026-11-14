module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.EnrichedParameterizedClosed
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.EnrichedCochainUnit
/-!
概要：実閉射との豊穣合成を、同じ前後合成へ厳密に回収する。
方針：単位子の自然性と指定した閉射の豊穣 Hom を使う。
規約：全パラメータと全 cochain 次数を保持。使われ方：分解変更の厳密自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
lemma enrichedCochain_postcompose {R : Type u} [CommRing R]
    (C : Type v) [Category C] [EnrichedOrdinaryCategory (Complex R) C]
    (X Y Z : C) {K P : Complex R}
    (i : 𝟙_ (Complex R) ⟶ K) (a : K ⟶ (Y ⟶[Complex R] Z))
    (g : Y ⟶ Z) (hi : i ≫ a = eHomEquiv (Complex R) g)
    (p : ℤ) (h : Cochain P (X ⟶[Complex R] Y) p) :
    (Cochain.ofHom ((ρ_ P).inv ≫ P ◁ i)).comp
      (((tensorRightHom K P (X ⟶[Complex R] Y)).f p h).comp
        (Cochain.ofHom ((𝟙 _ ⊗ₘ a) ≫ eComp (Complex R) X Y Z)) (add_zero p))
      (zero_add p) = h.comp (Cochain.ofHom (eHomWhiskerLeft (Complex R) X g))
        (add_zero p) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexRightUnitInsertion_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_postcompose (Complex R) C X Y Z i a (𝟙 _) g hi
  rw [Category.assoc, he, Category.id_comp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
