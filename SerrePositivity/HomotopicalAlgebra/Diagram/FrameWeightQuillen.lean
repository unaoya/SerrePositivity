module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightRealization
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedCones
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedFunctor

/-! # Projective weight realization and weighted mapping Quillen adjunctions

Pointwise cosimplicial frames give a right Quillen functor into the
projective model of simplicial diagrams. Its actual left adjoint realizes
weight diagrams. A projectively cofibrant weight can be tensored with a
space, giving a second actual Quillen adjunction into the original model.
Only weak equivalences between projectively cofibrant weights are claimed
preserved; objectwise cofibrancy does not substitute for that hypothesis.
-/

@[expose] public section
universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex SerrePositivity.Quillen

namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  [ModelCategory SSet.{w}]
  (I J : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

local instance : IsLocallyPresentable.{w} SSet.{w} :=
  WeightedCones.simplicialSet_isLocallyPresentable

include hcof hfib hA hconst

omit [HasColimitsOfSize.{w, w} C] in
lemma hom_isRightQuillen :
    let := Projective.modelCategory Kᵒᵖ I J
    IsRightQuillen (hom K A) := by
  let := Projective.modelCategory Kᵒᵖ I J
  constructor
  · intro X Y p hp k
    have := cosimplicialHom_isRightQuillen hcof hfib (A.obj k.unop) (hA k.unop) (hconst k.unop)
    exact IsRightQuillen.map_fibrations (R := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (A.obj k.unop)) p hp
  · intro X Y p hp
    have hk (k : Kᵒᵖ) : trivialFibrations SSet.{w}
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (A.obj k.unop)).map p) := by
      have := cosimplicialHom_isRightQuillen hcof hfib (A.obj k.unop) (hA k.unop) (hconst k.unop)
      exact IsRightQuillen.map_trivialFibrations (R := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (A.obj k.unop)) p hp
    exact ⟨fun k => (hk k).1, fun k => (hk k).2⟩

lemma isLeftQuillen :
    let := Projective.modelCategory Kᵒᵖ I J
    IsLeftQuillen (functor K A) := by
  let := Projective.modelCategory Kᵒᵖ I J
  have := hom_isRightQuillen K I J hcof hfib A hA hconst
  exact (isLeftQuillen_iff_isRightQuillen (adjunction K A)).mpr inferInstance

lemma map_weakEquivalence_of_cofibrant {W W' : Kᵒᵖ ⥤ SSet.{w}} (f : W ⟶ W')
    (hW : let := Projective.modelCategory Kᵒᵖ I J; IsCofibrant W)
    (hW' : let := Projective.modelCategory Kᵒᵖ I J; IsCofibrant W')
    (hf : ∀ k, weakEquivalences SSet.{w} (f.app k)) :
    weakEquivalences C ((functor K A).map f) := by
  let := Projective.modelCategory Kᵒᵖ I J
  have := isLeftQuillen K I J hcof hfib A hA hconst
  have := hW
  have := hW'
  have : WeakEquivalence f := ⟨hf⟩
  exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant (functor K A) f)

omit hcof hfib hA hconst in
abbrev weightedFunctor (W : Kᵒᵖ ⥤ SSet.{w}) : SSet.{w} ⥤ C :=
  WeightedCones.tensorDiagram Kᵒᵖ W ⋙ functor K A

omit hcof hfib hA hconst in
abbrev weightedHom (W : Kᵒᵖ ⥤ SSet.{w}) : C ⥤ SSet.{w} :=
  hom K A ⋙ WeightedCones.coneSpace Kᵒᵖ W

omit hcof hfib hA hconst in
def weightedAdjunction (W : Kᵒᵖ ⥤ SSet.{w}) : weightedFunctor K A W ⊣ weightedHom K A W :=
  (WeightedCones.adjunction Kᵒᵖ W).comp (adjunction K A)

lemma weighted_isLeftQuillen (W : Kᵒᵖ ⥤ SSet.{w})
    (hW : let := Projective.modelCategory Kᵒᵖ I J; IsCofibrant W) :
    IsLeftQuillen (weightedFunctor K A W) := by
  let := Projective.modelCategory Kᵒᵖ I J
  have : IsQuillenBifunctor (curriedTensor SSet.{w}) :=
    SimplicialModel.simplicial_isQuillenBifunctor hcof hfib
  have := WeightedCones.tensorDiagram_isLeftQuillen Kᵒᵖ I J W hW
  have := isLeftQuillen K I J hcof hfib A hA hconst
  exact Quillen.isLeftQuillen_comp _ _

lemma weighted_isRightQuillen (W : Kᵒᵖ ⥤ SSet.{w})
    (hW : let := Projective.modelCategory Kᵒᵖ I J; IsCofibrant W) :
    IsRightQuillen (weightedHom K A W) := by
  have := weighted_isLeftQuillen K I J hcof hfib A hA hconst W hW
  exact (isLeftQuillen_iff_isRightQuillen (weightedAdjunction K A W)).mp inferInstance

end SerrePositivity.DiagramModel.FrameWeightRealization
