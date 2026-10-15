module

public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction

/-! # Comparing model structures on one category with fixed cofibrations

An identity left Quillen functor between such models preserves every weak
equivalence, including maps with noncofibrant endpoints. Two identity left
Quillen functors in opposite directions therefore identify all three classes.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] (m n : ModelCategory C)

lemma weakEquivalences_le_of_identity_leftQuillen
    (hc : m.categoryWithCofibrations.cofibrations = n.categoryWithCofibrations.cofibrations)
    (h : @IsLeftQuillen C _ C _ m.categoryWithCofibrations m.categoryWithWeakEquivalences
      n.categoryWithCofibrations n.categoryWithWeakEquivalences (𝟭 C)) :
    m.categoryWithWeakEquivalences.weakEquivalences ≤
      n.categoryWithWeakEquivalences.weakEquivalences := by
  have : m.categoryWithWeakEquivalences.weakEquivalences.HasTwoOutOfThreeProperty := m.cm2
  have : n.categoryWithWeakEquivalences.weakEquivalences.HasTwoOutOfThreeProperty := n.cm2
  have hm : m.categoryWithCofibrations.cofibrations.rlp =
      m.categoryWithFibrations.fibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences := by
    let := m
    exact cofibrations_rlp C
  have hn : n.categoryWithCofibrations.cofibrations.rlp =
      n.categoryWithFibrations.fibrations ⊓ n.categoryWithWeakEquivalences.weakEquivalences := by
    let := n
    exact cofibrations_rlp C
  have ht := hm.symm.trans ((congrArg MorphismProperty.rlp hc).trans hn)
  intro X Y f hf
  let d : MorphismProperty.MapFactorizationData
      (m.categoryWithCofibrations.cofibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences)
      m.categoryWithFibrations.fibrations f := by
    let := m
    exact MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C) f
  have hp : m.categoryWithWeakEquivalences.weakEquivalences d.p :=
    m.categoryWithWeakEquivalences.weakEquivalences.of_precomp _ _ d.hi.2 (d.fac.symm ▸ hf)
  have hpn := ht.le d.p ⟨d.hp, hp⟩
  exact d.fac ▸ n.categoryWithWeakEquivalences.weakEquivalences.comp_mem _ _
    (h.map_trivialCofibrations d.i d.hi).2 hpn.2

lemma classes_eq_of_identity_leftQuillen_both
    (h : @IsLeftQuillen C _ C _ m.categoryWithCofibrations m.categoryWithWeakEquivalences
      n.categoryWithCofibrations n.categoryWithWeakEquivalences (𝟭 C))
    (h' : @IsLeftQuillen C _ C _ n.categoryWithCofibrations n.categoryWithWeakEquivalences
      m.categoryWithCofibrations m.categoryWithWeakEquivalences (𝟭 C)) :
    m.categoryWithCofibrations.cofibrations = n.categoryWithCofibrations.cofibrations ∧
      m.categoryWithWeakEquivalences.weakEquivalences =
        n.categoryWithWeakEquivalences.weakEquivalences ∧
      m.categoryWithFibrations.fibrations = n.categoryWithFibrations.fibrations := by
  have hc : m.categoryWithCofibrations.cofibrations = n.categoryWithCofibrations.cofibrations :=
    le_antisymm (fun _ _ f hf => h.map_cofibrations f hf)
      (fun _ _ f hf => h'.map_cofibrations f hf)
  have hw := le_antisymm (weakEquivalences_le_of_identity_leftQuillen m n hc h)
    (weakEquivalences_le_of_identity_leftQuillen n m hc.symm h')
  have hm : m.categoryWithFibrations.fibrations =
      (m.categoryWithCofibrations.cofibrations ⊓
        m.categoryWithWeakEquivalences.weakEquivalences).rlp := by
    let := m
    exact (trivialCofibrations_rlp C).symm
  have hn : n.categoryWithFibrations.fibrations =
      (n.categoryWithCofibrations.cofibrations ⊓
        n.categoryWithWeakEquivalences.weakEquivalences).rlp := by
    let := n
    exact (trivialCofibrations_rlp C).symm
  have he := congrArg MorphismProperty.rlp (congrArg₂ (· ⊓ ·) hc hw)
  exact ⟨hc, hw, hm.trans (he.trans hn.symm)⟩

end SerrePositivity.Quillen
