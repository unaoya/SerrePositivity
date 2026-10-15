module

public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedCones
public import SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor

/-! # Comparing a contractible weight tensor with constant diagrams

The actual comparison is pointwise a tensor of the weight augmentation,
followed by the right unitor. Monomorphism cofibrations imply that every
simplicial set is cofibrant, so the comparison is a weak equivalence for
every input space, rather than only selected replacements.
-/

@[expose] public section
noncomputable section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.Quillen
namespace SerrePositivity.DiagramModel.WeightComparison
variable (K : Type w) [SmallCategory K]
def tensorUnitIso :
    WeightedCones.tensorDiagram K ((Functor.const K).obj (𝟙_ SSet.{w})) ≅ Functor.const K :=
  NatIso.ofComponents (fun X =>
    NatIso.ofComponents (fun _ => ρ_ X) (by
      intro i j f
      simp [WeightedCones.tensorDiagram, SerrePositivity.PointwiseAdjunction.pointwise])) (by
    intro X Y f
    ext k
    simp [WeightedCones.tensorDiagram, SerrePositivity.PointwiseAdjunction.pointwise])

def tensorComparison {W : K ⥤ SSet.{w}} (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{w})) :
    WeightedCones.tensorDiagram K W ⟶ Functor.const K :=
  (SerrePositivity.PointwiseAdjunction.pointwise K (curriedTensor SSet.{w})).flip.map q ≫
    (tensorUnitIso K).hom

lemma tensorComparison_app {W : K ⥤ SSet.{w}} (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{w}))
    (X : SSet.{w}) (k : K) :
    ((tensorComparison K q).app X).app k = (X ◁ q.app k) ≫ (ρ_ X).hom := rfl

variable [ModelCategory SSet.{w}]
  [IsQuillenBifunctor (curriedTensor SSet.{w})]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)

omit [IsQuillenBifunctor (curriedTensor SSet.{w})] in
include hcof in
lemma all_cofibrant (X : SSet.{w}) : IsCofibrant X := by
  constructor
  rw [hcof]
  infer_instance

include hcof in
lemma tensorComparison_weakEquivalence {W : K ⥤ SSet.{w}}
    (q : W ⟶ (Functor.const K).obj (𝟙_ SSet.{w}))
    (hq : ∀ k, weakEquivalences SSet.{w} (q.app k)) (X : SSet.{w}) (k : K) :
    weakEquivalences SSet.{w} (((tensorComparison K q).app X).app k) := by
  have := all_cofibrant hcof X
  have := all_cofibrant hcof (W.obj k)
  have : IsCofibrant (((Functor.const K).obj (𝟙_ SSet.{w})).obj k) :=
    all_cofibrant hcof _
  have : WeakEquivalence (q.app k) := ⟨hq k⟩
  have := tensorLeft_isLeftQuillen X
  have ht := map_weakEquivalence_of_cofibrant (tensorLeft X) (q.app k)
  change weakEquivalences SSet.{w} ((tensorLeft X).map (q.app k) ≫ (ρ_ X).hom)
  have : WeakEquivalence ((tensorLeft X).map (q.app k)) := ht
  exact (weakEquivalences SSet.{w}).comp_mem _ _ (mem_weakEquivalences _)
    (mem_weakEquivalences _)

end SerrePositivity.DiagramModel.WeightComparison
