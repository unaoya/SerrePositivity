module

public import SerrePositivity.HomotopicalAlgebra.Diagram.DerivedConstantAdjunction

/-! # Homotopy limits of small simplicial diagrams

The actual space is a fibrant-replaced weighted cone space. Its descended
functor is right adjoint to the descended constant diagram functor.
The weight, replacements, derived-functor existence and comparison are
constructed here; none is a new input or a literature axiom.
-/

@[expose] public section
universe w vH uH vD uD
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen

namespace SerrePositivity.DiagramModel.HomotopyLimit
variable (K : Type w) [SmallCategory K] [ModelCategory SSet.{w}]
  {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
  (L : SSet.{w} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{w})]
  (Q : (K ⥤ SSet.{w}) ⥤ D)
  [Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{w}))]

lemma constant_inverts : (weakEquivalences SSet.{w}).IsInvertedBy
    ((Functor.const K : SSet.{w} ⥤ _) ⋙ Q) := by
  intro X Y f hf
  exact Localization.inverts Q (Projective.objectwise K (weakEquivalences SSet.{w})) _
    (fun _ => hf)

def localizedConstant : H ⥤ D :=
  Localization.lift ((Functor.const K : SSet.{w} ⥤ _) ⋙ Q) (constant_inverts K Q) L

def constantComparison : (Functor.const K : SSet.{w} ⥤ _) ⋙ Q ≅
    L ⋙ localizedConstant K L Q :=
  (Localization.fac ((Functor.const K : SSet.{w} ⥤ _) ⋙ Q) (constant_inverts K Q) L).symm

variable (I J : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

abbrev functor : (K ⥤ SSet.{w}) ⥤ SSet.{w} := HomotopyCones.functor K I J

variable [IsQuillenBifunctor (curriedTensor SSet.{w})]

lemma map_weakEquivalence {F G : K ⥤ SSet.{w}} (f : F ⟶ G)
    (hf : ∀ k, weakEquivalences SSet.{w} (f.app k)) :
    weakEquivalences SSet.{w} ((functor K I J).map f) :=
  HomotopyCones.map_weakEquivalence K I J f hf

/-- The actual functor computes a right adjoint to the descended constant
functor, for arbitrary ordinary localizations in independent universes. -/
lemma exists_localizedAdjunction
    (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _) :
    ∃ RF : D ⥤ H, Nonempty (localizedConstant K L Q ⊣ RF) ∧
      Nonempty (functor K I J ⋙ L ≅ Q ⋙ RF) :=
  HomotopyCones.exists_rightAdjoint_constant K I J hcof L Q
    (localizedConstant K L Q) (constantComparison K L Q)

end SerrePositivity.DiagramModel.HomotopyLimit
