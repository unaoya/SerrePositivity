module

public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedCones
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyColimit
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenResolutionHom
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedFunctor

/-! # Actual homotopy coherent cone spaces

A projective cofibrant replacement of the constant unit diagram supplies
the weight. The right adjoint of tensor with that weight is applied to an
actual fibrant replacement of the input diagram. The resulting functor is
homotopical and computes the right derived weighted cone functor.

The comparison of this construction with the right adjoint of the derived
constant functor is a separate theorem; no ordinary-limit Quillen condition
is assumed for the projective model.
-/

@[expose] public section
universe w vH uH vD uD
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen

namespace SerrePositivity.DiagramModel.HomotopyCones
variable (K : Type w) [SmallCategory K] [ModelCategory SSet.{w}]
  (I J : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : IsLocallyPresentable.{w} SSet.{w} :=
  WeightedCones.simplicialSet_isLocallyPresentable

/-- A specified projective cofibrant replacement of the constant unit diagram. -/
def weight : K ⥤ SSet.{w} :=
  (HomotopyColimit.replacement K I J).obj ((Functor.const K).obj (𝟙_ SSet.{w}))

def weightComparison : weight K I J ⟶ (Functor.const K).obj (𝟙_ SSet.{w}) :=
  (HomotopyColimit.replacementComparison K I J).app _

lemma weight_isCofibrant :
    let := Projective.modelCategory K I J; IsCofibrant (weight K I J) :=
  HomotopyColimit.replacement_isCofibrant K I J _

lemma weightComparison_objectwiseWeakEquivalence (k : K) :
    weakEquivalences SSet.{w} ((weightComparison K I J).app k) :=
  HomotopyColimit.replacementComparison_objectwiseWeakEquivalence K I J _ k

def fibrantFactorization :
    let := Projective.modelCategory K I J
    MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations (K ⥤ SSet.{w})) (fibrations (K ⥤ SSet.{w})) := by
  let := Projective.modelCategory K I J
  have : (trivialCofibrations (K ⥤ SSet.{w})).HasFunctorialFactorization
      (fibrations (K ⥤ SSet.{w})) := (Projective.functorialFactorizations K I J).2
  exact MorphismProperty.functorialFactorizationData _ _

def replacement : (K ⥤ SSet.{w}) ⥤ (K ⥤ SSet.{w}) := by
  let := Projective.modelCategory K I J
  exact HomotopyFunctionComplex.fibrantTarget (fibrantFactorization K I J)

def replacementComparison : 𝟭 (K ⥤ SSet.{w}) ⟶ replacement K I J := by
  let := Projective.modelCategory K I J
  exact HomotopyFunctionComplex.fibrantTargetComparison (fibrantFactorization K I J)

lemma replacement_isFibrant (F : K ⥤ SSet.{w}) :
    let := Projective.modelCategory K I J; IsFibrant ((replacement K I J).obj F) := by
  let := Projective.modelCategory K I J
  exact HomotopyFunctionComplex.fibrantTarget_isFibrant (fibrantFactorization K I J) F

lemma replacementComparison_weakEquivalence (F : K ⥤ SSet.{w}) :
    let := Projective.modelCategory K I J
    weakEquivalences (K ⥤ SSet.{w}) ((replacementComparison K I J).app F) := by
  let := Projective.modelCategory K I J
  exact HomotopyFunctionComplex.fibrantTargetComparison_weakEquivalence
    (fibrantFactorization K I J) F

lemma replacement_map_weakEquivalence {F G : K ⥤ SSet.{w}} (f : F ⟶ G)
    (hf : ∀ k, weakEquivalences SSet.{w} (f.app k)) :
    let := Projective.modelCategory K I J
    weakEquivalences (K ⥤ SSet.{w}) ((replacement K I J).map f) := by
  let := Projective.modelCategory K I J
  exact HomotopyFunctionComplex.fibrantTarget_map_weakEquivalence
    (fibrantFactorization K I J) f hf

abbrev functor : (K ⥤ SSet.{w}) ⥤ SSet.{w} :=
  replacement K I J ⋙ WeightedCones.coneSpace K (weight K I J)

abbrev comparison : WeightedCones.coneSpace K (weight K I J) ⟶ functor K I J :=
  Functor.whiskerRight (replacementComparison K I J) _

variable [IsQuillenBifunctor (curriedTensor SSet.{w})]

lemma coneSpace_isRightQuillen :
    let := Projective.modelCategory K I J
    IsRightQuillen (WeightedCones.coneSpace K (weight K I J)) :=
  WeightedCones.coneSpace_isRightQuillen K I J _ (weight_isCofibrant K I J)

lemma comparison_weakEquivalence_of_fibrant (F : K ⥤ SSet.{w})
    (hF : let := Projective.modelCategory K I J; IsFibrant F) :
    weakEquivalences SSet.{w} ((comparison K I J).app F) := by
  let := Projective.modelCategory K I J
  have := coneSpace_isRightQuillen K I J
  have : IsFibrant ((𝟭 (K ⥤ SSet.{w})).obj F) := hF
  have := replacement_isFibrant K I J F
  have : WeakEquivalence ((replacementComparison K I J).app F) :=
    ⟨replacementComparison_weakEquivalence K I J F⟩
  exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_fibrant
    (WeightedCones.coneSpace K (weight K I J)) ((replacementComparison K I J).app F))

lemma isFibrant (F : K ⥤ SSet.{w}) : IsFibrant ((functor K I J).obj F) := by
  let := Projective.modelCategory K I J
  let R := WeightedCones.coneSpace K (weight K I J)
  have : R.IsRightAdjoint := (WeightedCones.adjunction K (weight K I J)).isRightAdjoint
  have : IsRightQuillen R := coneSpace_isRightQuillen K I J
  have := replacement_isFibrant K I J F
  have := Quillen.map_fibration R (terminal.from ((replacement K I J).obj F))
  exact (isFibrant_iff_of_isTerminal (R.map (terminal.from ((replacement K I J).obj F)))
    (terminalIsTerminal.isTerminalObj R (⊤_ (K ⥤ SSet.{w})))).mpr inferInstance

lemma map_weakEquivalence {F G : K ⥤ SSet.{w}} (f : F ⟶ G)
    (hf : ∀ k, weakEquivalences SSet.{w} (f.app k)) :
    weakEquivalences SSet.{w} ((functor K I J).map f) := by
  let := Projective.modelCategory K I J
  have := coneSpace_isRightQuillen K I J
  have := replacement_isFibrant K I J F
  have := replacement_isFibrant K I J G
  have : WeakEquivalence ((replacement K I J).map f) :=
    ⟨replacement_map_weakEquivalence K I J f hf⟩
  have := Quillen.map_weakEquivalence_of_fibrant
    (WeightedCones.coneSpace K (weight K I J)) ((replacement K I J).map f)
  exact (weakEquivalence_iff _).mp this

lemma hasPointwiseRightDerived {H : Type uH} [Category.{vH} H]
    (L : SSet.{w} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{w})] :
    let := Projective.modelCategory K I J
    (WeightedCones.coneSpace K (weight K I J) ⋙ L).HasPointwiseRightDerivedFunctor
      (weakEquivalences (K ⥤ SSet.{w})) := by
  let := Projective.modelCategory K I J
  have := coneSpace_isRightQuillen K I J
  infer_instance

/-- Comparison with every actual total right derived weighted cone functor. -/
def computesDerivedIso {D : Type uD} [Category.{vD} D] {H : Type uH} [Category.{vH} H]
    (Q : (K ⥤ SSet.{w}) ⥤ D)
    [Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{w}))]
    (L : SSet.{w} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{w})] (RF : D ⥤ H)
    (β : WeightedCones.coneSpace K (weight K I J) ⋙ L ⟶ Q ⋙ RF)
    [RF.IsRightDerivedFunctor β (Projective.objectwise K (weakEquivalences SSet.{w}))] :
    functor K I J ⋙ L ≅ Q ⋙ RF := by
  let := Projective.modelCategory K I J
  have := coneSpace_isRightQuillen K I J
  have : Q.IsLocalization (weakEquivalences (K ⥤ SSet.{w})) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences SSet.{w})))
  have : RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ SSet.{w})) :=
    inferInstanceAs (RF.IsRightDerivedFunctor β
      (Projective.objectwise K (weakEquivalences SSet.{w})))
  let a : functor K I J ⋙ L ⟶ replacement K I J ⋙ Q ⋙ RF :=
    Functor.whiskerLeft (replacement K I J) β
  let b : Q ⋙ RF ⟶ replacement K I J ⋙ Q ⋙ RF :=
    Functor.whiskerRight (replacementComparison K I J) (Q ⋙ RF)
  have : ∀ F, IsIso (a.app F) := by
    intro F
    have := replacement_isFibrant K I J F
    exact Quillen.rightComparison_isIso L Q β ((replacement K I J).obj F)
  have : ∀ F, IsIso (b.app F) := by
    intro F
    have : IsIso (Q.map ((replacementComparison K I J).app F)) :=
      Localization.inverts Q (weakEquivalences (K ⥤ SSet.{w})) _
        (replacementComparison_weakEquivalence K I J F)
    change IsIso (RF.map (Q.map ((replacementComparison K I J).app F)))
    infer_instance
  have : IsIso a := NatIso.isIso_of_isIso_app a
  have : IsIso b := NatIso.isIso_of_isIso_app b
  let ea := asIso a
  let eb := asIso b
  exact ea ≪≫ eb.symm

end SerrePositivity.DiagramModel.HomotopyCones
