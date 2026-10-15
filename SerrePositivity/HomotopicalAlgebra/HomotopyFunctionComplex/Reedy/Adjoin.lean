module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Induced
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Subcategory

/-! # Adjoining one object to the lower-degree Reedy category

`none` is the new object and `some x` an existing lower-degree object.
The indexing is injective, and inverse maps cannot leave this object set.
No injectivity assumption on the degree function is required.
-/

@[expose] public section
universe v u t
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)

abbrev adjoinObj : Option (Lower r (r.deg j)) → J
  | none => j
  | some x => x.obj

abbrev Adjoin := InducedCategory J (adjoinObj r j)

lemma adjoinObj_injective : Function.Injective (adjoinObj r j) := by
  rintro (_ | x) (_ | y) h
  · rfl
  · exact (y.property.ne (congrArg r.deg h).symm).elim
  · exact (x.property.ne (congrArg r.deg h)).elim
  · exact congrArg some (ObjectProperty.FullSubcategory.ext h)

lemma adjoinObj_degree_le (x : Adjoin r j) : r.deg (adjoinObj r j x) ≤ r.deg j := by
  cases x with
  | none => exact le_rfl
  | some x => exact x.property.le

lemma adjoinObj_inverse_closed (x : Adjoin r j) {y : J}
    (f : adjoinObj r j x ⟶ y) (hf : inverse f) : ∃ z, adjoinObj r j z = y := by
  by_cases hy : r.deg y < r.deg j
  · exact ⟨some ⟨y, hy⟩, rfl⟩
  · have hi : MorphismProperty.identities J f := by
      by_contra hi
      exact hy (lt_of_lt_of_le (r.lt₁ f hf hi) (adjoinObj_degree_le r j x))
    exact ⟨x, identities_endpoints f hi⟩

abbrev adjoinReedy : ReedyStructure
    (inducedInverse (inverse := inverse) (adjoinObj r j))
    (inducedDirect (direct := direct) (adjoinObj r j)) α :=
  inducedReedy (adjoinObj r j) r (adjoinObj_injective r j) (adjoinObj_inverse_closed r j)

abbrev adjoinLower : Lower r (r.deg j) ⥤ Adjoin r j where
  obj x := some x
  map f := InducedCategory.homMk f.hom

abbrev adjoinInclusion : Adjoin r j ⥤ J := inducedFunctor (adjoinObj r j)

lemma not_identities_into_top (x : Lower r (r.deg j)) (f : x.obj ⟶ j) :
    ¬MorphismProperty.identities J f := by
  intro hf
  exact x.property.ne (congrArg r.deg (identities_endpoints f hf))

lemma not_identities_from_top (x : Lower r (r.deg j)) (f : j ⟶ x.obj) :
    ¬MorphismProperty.identities J f := by
  intro hf
  exact x.property.ne (congrArg r.deg (identities_endpoints f hf)).symm

lemma not_inverse_into_top (x : Lower r (r.deg j)) (f : x.obj ⟶ j) : ¬inverse f := by
  intro hf
  exact (r.le₁ f hf).not_gt x.property

lemma not_direct_from_top (x : Lower r (r.deg j)) (f : j ⟶ x.obj) : ¬direct f := by
  intro hf
  exact (r.le₂ f hf).not_gt x.property

include r in
lemma inverse_top_endomorphism (f : j ⟶ j) (hf : inverse f) : f = 𝟙 j := by
  exact identities_eqToHom f (r.identities_of_prop₁_of_eq hf rfl)

include r in
lemma direct_top_endomorphism (f : j ⟶ j) (hf : direct f) : f = 𝟙 j := by
  exact identities_eqToHom f (r.identities_of_prop₂_of_eq hf rfl)

end SerrePositivity.Reedy
