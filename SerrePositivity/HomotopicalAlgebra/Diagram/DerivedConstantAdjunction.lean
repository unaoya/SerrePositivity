module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyCones
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightComparison
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedAdjunction

/-! # A homotopy limit right adjoint on localized simplicial diagrams

The projective cofibrant weight resolves the constant unit diagram.
Its tensor is weakly equivalent to the actual constant functor on every
space. Hence its derived left adjoint agrees with the descended constant
functor. The derived right weighted cone functor is therefore right adjoint
to that constant functor. This proves an ordinary localized universal
property without asserting that ordinary limit is projective right Quillen.
-/

@[expose] public section
universe w vH uH vD uD
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen

namespace SerrePositivity.DiagramModel.HomotopyCones
variable (K : Type w) [SmallCategory K] [ModelCategory SSet.{w}]
  (I J : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [IsQuillenBifunctor (curriedTensor SSet.{w})]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)

local instance : IsLocallyPresentable.{w} SSet.{w} :=
  WeightedCones.simplicialSet_isLocallyPresentable

variable {H : Type uH} [Category.{vH} H] {D : Type uD} [Category.{vD} D]
  (L : SSet.{w} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{w})]
  (Q : (K ⥤ SSet.{w}) ⥤ D)
  [Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{w}))]
  (LF : H ⥤ D)
  (α : L ⋙ LF ⟶ WeightedCones.tensorDiagram K (weight K I J) ⋙ Q)
  [LF.IsLeftDerivedFunctor α (weakEquivalences SSet.{w})]
  (constant : H ⥤ D) (e : (Functor.const K : SSet.{w} ⥤ _) ⋙ Q ≅ L ⋙ constant)

include hcof

/-- Descent of the actual tensor-to-constant weak equivalence. -/
def derivedTensorConstantIso : LF ≅ constant := by
  let := Projective.modelCategory K I J
  have := WeightedCones.tensorDiagram_isLeftQuillen K I J _ (weight_isCofibrant K I J)
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{w})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{w})))
  have : ∀ X, IsIso (α.app X) := by
    intro X
    have := WeightComparison.all_cofibrant hcof X
    exact Quillen.leftComparison_isIso L Q α X
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let c := WeightComparison.tensorComparison K (weightComparison K I J)
  let b : WeightedCones.tensorDiagram K (weight K I J) ⋙ Q ⟶
      (Functor.const K : SSet.{w} ⥤ _) ⋙ Q := Functor.whiskerRight c Q
  have : ∀ X, IsIso (b.app X) := by
    intro X
    change IsIso (Q.map (c.app X))
    exact Localization.inverts Q (weakEquivalences (K ⥤ SSet.{w})) _
      (WeightComparison.tensorComparison_weakEquivalence K hcof
        (weightComparison K I J) (weightComparison_objectwiseWeakEquivalence K I J) X)
  have : IsIso b := NatIso.isIso_of_isIso_app b
  let ea := asIso α
  let eb := asIso b
  exact (Localization.fullyFaithfulWhiskeringLeft L (weakEquivalences SSet.{w}) D).preimageIso
    (ea ≪≫ eb ≪≫ e)

/-- The right derived weighted cone functor is right adjoint to the actual
constant functor descended to the two ordinary localizations. -/
def derivedConstantAdjunction (RF : D ⥤ H)
    (β : WeightedCones.coneSpace K (weight K I J) ⋙ L ⟶ Q ⋙ RF)
    [RF.IsRightDerivedFunctor β (Projective.objectwise K (weakEquivalences SSet.{w}))] :
    constant ⊣ RF := by
  let := Projective.modelCategory K I J
  have := WeightedCones.tensorDiagram_isLeftQuillen K I J _ (weight_isCofibrant K I J)
  have := coneSpace_isRightQuillen K I J
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{w})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{w})))
  have : RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ SSet.{w})) :=
    inferInstanceAs (RF.IsRightDerivedFunctor β
      (Projective.objectwise K (weakEquivalences SSet.{w})))
  let adj := Quillen.derivedAdjunction L Q (WeightedCones.adjunction K (weight K I J)) α β
  exact adj.ofNatIsoLeft (derivedTensorConstantIso K I J hcof L Q LF α constant e)

include e in
/-- Existence and computation use the proved derived-functor existence;
no derived tensor or cone functor is an additional input. -/
lemma exists_rightAdjoint_constant :
    ∃ RF : D ⥤ H, Nonempty (constant ⊣ RF) ∧
      Nonempty (functor K I J ⋙ L ≅ Q ⋙ RF) := by
  let := Projective.modelCategory K I J
  have := WeightedCones.tensorDiagram_isLeftQuillen K I J _ (weight_isCofibrant K I J)
  have := coneSpace_isRightQuillen K I J
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{w})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{w})))
  let T := WeightedCones.tensorDiagram K (weight K I J) ⋙ Q
  let R := WeightedCones.coneSpace K (weight K I J) ⋙ L
  let LF := T.totalLeftDerived L (weakEquivalences SSet.{w})
  let α := T.totalLeftDerivedCounit L (weakEquivalences SSet.{w})
  let RF := R.totalRightDerived Q (weakEquivalences (K ⥤ SSet.{w}))
  let β := R.totalRightDerivedUnit Q (weakEquivalences (K ⥤ SSet.{w}))
  have : RF.IsRightDerivedFunctor β
      (Projective.objectwise K (weakEquivalences SSet.{w})) :=
    inferInstanceAs (RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ SSet.{w})))
  exact ⟨RF, ⟨derivedConstantAdjunction K I J hcof L Q LF α constant e RF β⟩,
    ⟨computesDerivedIso K I J Q L RF β⟩⟩

end SerrePositivity.DiagramModel.HomotopyCones
