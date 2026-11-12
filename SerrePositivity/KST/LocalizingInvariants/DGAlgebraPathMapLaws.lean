module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMap

/-!
概要：経路代数の射の恒等・合成則と、対角の厳密な自然性。
方針：両端と同じ比較 cochain による実 Hom の一意性から証明する。
規約：対象ごとの同型で関手則を代用しない。使われ方：相対経路の実図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R]

abbrev primitive (B : Mon (Complex R)) : Cochain (algebra R B).X B.X (-1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R _ _ (identityFunctor R B) (identityPoint R B) (identityPoint R B)

lemma chain_ext (B : Mon (Complex R)) {K : Complex R} (f g : K ⟶ (algebra R B).X)
    (hs : f ≫ (source R B).hom = g ≫ (source R B).hom)
    (ht : f ≫ (target R B).hom = g ≫ (target R B).hom)
    (hp : (Cochain.ofHom f).comp (primitive R B) (zero_add (-1)) =
      (Cochain.ofHom g).comp (primitive R B) (zero_add (-1))) : f = g :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R _ _ (identityFunctor R B) (identityPoint R B) (identityPoint R B)
    K f g hs ht hp

lemma mapHom_primitive {A B : Mon (Complex R)} (f : A ⟶ B) :
    (Cochain.ofHom (mapHom R f)).comp (primitive R B) (zero_add (-1)) =
      (primitive R A).comp (Cochain.ofHom f.hom) (add_zero (-1)) := mapHom_comparison R f

lemma diagonalHom_primitive (B : Mon (Complex R)) :
    (Cochain.ofHom (diagonalHom R B)).comp (primitive R B) (zero_add (-1)) = 0 :=
  diagonalHom_comparison R B

lemma map_id (B : Mon (Complex R)) : map R (𝟙 B) = 𝟙 (algebra R B) := by
  apply Mon.Hom.ext
  apply chain_ext R B
  · change mapHom R (𝟙 B) ≫ (source R B).hom = 𝟙 _ ≫ (source R B).hom
    rw [mapHom_source]
    simp
  · change mapHom R (𝟙 B) ≫ (target R B).hom = 𝟙 _ ≫ (target R B).hom
    rw [mapHom_target]
    simp
  · change (Cochain.ofHom (mapHom R (𝟙 B))).comp (primitive R B) _ =
      (Cochain.ofHom (𝟙 (algebra R B).X)).comp (primitive R B) _
    rw [mapHom_primitive]
    change (primitive R B).comp (Cochain.ofHom (𝟙 B.X)) _ = _
    rw [Cochain.comp_id, Cochain.id_comp]

lemma map_comp {A B C : Mon (Complex R)} (f : A ⟶ B) (g : B ⟶ C) :
    map R (f ≫ g) = map R f ≫ map R g := by
  apply Mon.Hom.ext
  apply chain_ext R C
  · change mapHom R (f ≫ g) ≫ (source R C).hom =
      (mapHom R f ≫ mapHom R g) ≫ (source R C).hom
    rw [mapHom_source, Category.assoc, mapHom_source, ← Category.assoc, mapHom_source]
    rfl
  · change mapHom R (f ≫ g) ≫ (target R C).hom =
      (mapHom R f ≫ mapHom R g) ≫ (target R C).hom
    rw [mapHom_target, Category.assoc, mapHom_target, ← Category.assoc, mapHom_target]
    rfl
  · change (Cochain.ofHom (mapHom R (f ≫ g))).comp (primitive R C) _ =
      (Cochain.ofHom (mapHom R f ≫ mapHom R g)).comp (primitive R C) _
    rw [mapHom_primitive, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      mapHom_primitive, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      mapHom_primitive, Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
    rfl

lemma diagonal_naturality {A B : Mon (Complex R)} (f : A ⟶ B) :
    diagonal R A ≫ map R f = f ≫ diagonal R B := by
  apply Mon.Hom.ext
  apply chain_ext R B
  · change (diagonalHom R A ≫ mapHom R f) ≫ (source R B).hom =
      (f.hom ≫ diagonalHom R B) ≫ (source R B).hom
    rw [Category.assoc, mapHom_source, ← Category.assoc, diagonalHom_source,
      Category.id_comp, Category.assoc, diagonalHom_source, Category.comp_id]
  · change (diagonalHom R A ≫ mapHom R f) ≫ (target R B).hom =
      (f.hom ≫ diagonalHom R B) ≫ (target R B).hom
    rw [Category.assoc, mapHom_target, ← Category.assoc, diagonalHom_target,
      Category.id_comp, Category.assoc, diagonalHom_target, Category.comp_id]
  · change (Cochain.ofHom (diagonalHom R A ≫ mapHom R f)).comp (primitive R B) _ =
      (Cochain.ofHom (f.hom ≫ diagonalHom R B)).comp (primitive R B) _
    rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, mapHom_primitive,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, diagonalHom_primitive, Cochain.zero_comp,
      Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      diagonalHom_primitive, Cochain.comp_zero]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
