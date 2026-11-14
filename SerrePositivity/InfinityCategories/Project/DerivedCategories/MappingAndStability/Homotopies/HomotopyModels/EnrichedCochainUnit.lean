module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.ComplexTensorCochainUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.EnrichedParameterizedUnit
/-!
概要：任意次数の豊穣 Hom 値 cochain と、指定実単位との合成を回収する。
方針：単位挿入の全 cochain 自然性と、実豊穣単位律を使う。
規約：全パラメータ複体を保持。使われ方：出力分解の単位律の比較成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable {R : Type u} [CommRing R] (C : Type v) [DGCategory R C]
/-- 指定実単位と、全次数の Hom 値 cochain の左合成。 -/
lemma enrichedCochain_leftUnit (X Y : C) {K P : Complex R}
    (i : 𝟙_ (Complex R) ⟶ K) (a : K ⟶ (X ⟶[Complex R] X))
    (hi : i ≫ a = eId (Complex R) X) (p : ℤ) (h : Cochain P (X ⟶[Complex R] Y) p) :
    (Cochain.ofHom ((λ_ P).inv ≫ i ▷ P)).comp
      (((tensorLeftHom K P (X ⟶[Complex R] Y)).f p h).comp
        (Cochain.ofHom ((a ⊗ₘ 𝟙 _) ≫ eComp (Complex R) X X Y)) (add_zero p))
      (zero_add p) = h := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexLeftUnitInsertion_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_leftUnit (Complex R) C X Y i a (𝟙 _) hi
  rw [Category.assoc, he, Cochain.comp_id]
/-- 指定実単位と、全次数の Hom 値 cochain の右合成。 -/
lemma enrichedCochain_rightUnit (X Y : C) {K P : Complex R}
    (i : 𝟙_ (Complex R) ⟶ K) (a : K ⟶ (Y ⟶[Complex R] Y))
    (hi : i ≫ a = eId (Complex R) Y) (p : ℤ) (h : Cochain P (X ⟶[Complex R] Y) p) :
    (Cochain.ofHom ((ρ_ P).inv ≫ P ◁ i)).comp
      (((tensorRightHom K P (X ⟶[Complex R] Y)).f p h).comp
        (Cochain.ofHom ((𝟙 _ ⊗ₘ a) ≫ eComp (Complex R) X Y Y)) (add_zero p))
      (zero_add p) = h := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexRightUnitInsertion_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_rightUnit (Complex R) C X Y i a (𝟙 _) hi
  rw [Category.assoc, he, Cochain.comp_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
