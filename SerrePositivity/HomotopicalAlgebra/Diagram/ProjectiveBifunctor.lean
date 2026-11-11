module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveQuillen
public import SerrePositivity.HomotopicalAlgebra.Monoidal.QuillenBifunctor
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-! # Pointwise Quillen bifunctors for the projective diagram model

Only fibrations and weak equivalences are evaluated pointwise. The
pushout-product condition follows from the lifted cotensor adjunction.
No objectwise characterization of projective cofibrations is assumed.
-/

@[expose] public section
universe w v u vV uV
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.PointwiseAdjunction

namespace SerrePositivity.DiagramModel.Projective
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  {V : Type uV} [Category.{vV} V] [ModelCategory V]

lemma pointwise_hasQuillenPullbackHom (G : Vᵒᵖ ⥤ C ⥤ C) [HasQuillenPullbackHom G] :
    let := modelCategory K I J
    HasQuillenPullbackHom (pointwise K G) := by
  let := modelCategory K I J
  constructor
  · intro A B X Y i p sq hi hp
    apply (fibration_iff sq.π).mpr
    intro k
    have hp' : Fibration (p.app k) := ⟨(fibration_iff p).mp hp k⟩
    have h := HasQuillenPullbackHom.fibration i (p.app k)
      (evaluatePullbackObjObj K G i p sq k) hi hp'
    exact (fibration_iff _).mp h
  · intro A B X Y i p sq hi hp hw
    apply (weakEquivalence_iff sq.π).mpr
    intro k
    have hp' : Fibration (p.app k) := ⟨(fibration_iff p).mp hp k⟩
    have hw' : WeakEquivalence i ∨ WeakEquivalence (p.app k) := by
      rcases hw with hw | hw
      · exact Or.inl hw
      · exact Or.inr ⟨(weakEquivalence_iff p).mp hw k⟩
    have h := HasQuillenPullbackHom.weakEquivalence i (p.app k)
      (evaluatePullbackObjObj K G i p sq k) hi hp' hw'
    exact (weakEquivalence_iff _).mp h

lemma pointwise_isQuillenBifunctor (F : V ⥤ C ⥤ C) (G : Vᵒᵖ ⥤ C ⥤ C)
    (adj : F ⊣₂ G) [IsQuillenBifunctor F] :
    let := modelCategory K I J
    IsQuillenBifunctor (pointwise K F) := by
  let := modelCategory K I J
  have : HasQuillenPullbackHom G := (isQuillenBifunctor_iff_pullbackHom adj).mp inferInstance
  have := pointwise_hasQuillenPullbackHom K I J G
  exact (isQuillenBifunctor_iff_pullbackHom (PointwiseAdjunction.adjunction K adj)).mpr
    inferInstance

end SerrePositivity.DiagramModel.Projective
