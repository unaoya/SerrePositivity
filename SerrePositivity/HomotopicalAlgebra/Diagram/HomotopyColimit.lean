module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveQuillen
public import SerrePositivity.HomotopicalAlgebra.Generated.Replacement

/-! # Actual homotopy colimits from the projective diagram model

The specified projective cofibrant replacement is followed by actual
colimit. The result is homotopical and computes every ordinary total left
derived colimit by a natural isomorphism after localization.
-/

@[expose] public section
universe w v u vD uD vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.HomotopyColimit
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

def cofibrantFactorization :
    let := Projective.modelCategory K I J
    MorphismProperty.FunctorialFactorizationData
      (cofibrations (K ⥤ C)) (trivialFibrations (K ⥤ C)) := by
  let := Projective.modelCategory K I J
  have : (cofibrations (K ⥤ C)).HasFunctorialFactorization (trivialFibrations (K ⥤ C)) :=
    (Projective.functorialFactorizations K I J).1
  exact MorphismProperty.functorialFactorizationData _ _

def replacement : (K ⥤ C) ⥤ (K ⥤ C) := by
  let := Projective.modelCategory K I J
  exact ModelReplacement.initialArrows (K ⥤ C) ⋙ (cofibrantFactorization K I J).Z

def replacementComparison : replacement K I J ⟶ 𝟭 (K ⥤ C) := by
  let := Projective.modelCategory K I J
  exact
    { app F := (cofibrantFactorization K I J).p.app (Arrow.mk (initial.to F))
      naturality {_ _} f := (cofibrantFactorization K I J).p.naturality
        ((ModelReplacement.initialArrows (K ⥤ C)).map f) }

lemma replacement_isCofibrant (F : K ⥤ C) :
    let := Projective.modelCategory K I J
    IsCofibrant ((replacement K I J).obj F) := by
  let := Projective.modelCategory K I J
  let d := cofibrantFactorization K I J
  exact (isCofibrant_iff_of_isInitial (d.i.app (Arrow.mk (initial.to F))) initialIsInitial).mpr
    ⟨d.hi _⟩

lemma replacementComparison_trivialFibration (F : K ⥤ C) :
    let := Projective.modelCategory K I J
    trivialFibrations (K ⥤ C) ((replacementComparison K I J).app F) := by
  let := Projective.modelCategory K I J
  exact (cofibrantFactorization K I J).hp (Arrow.mk (initial.to F))

lemma replacementComparison_objectwiseWeakEquivalence (F : K ⥤ C) (k : K) :
    weakEquivalences C (((replacementComparison K I J).app F).app k) :=
  (replacementComparison_trivialFibration K I J F).2 k

lemma replacement_map_objectwiseWeakEquivalence {F G : K ⥤ C} (f : F ⟶ G)
    (hf : ∀ k, weakEquivalences C (f.app k)) (k : K) :
    weakEquivalences C (((replacement K I J).map f).app k) := by
  have h := congr_app ((replacementComparison K I J).naturality f) k
  change ((replacement K I J).map f).app k ≫ ((replacementComparison K I J).app G).app k =
    ((replacementComparison K I J).app F).app k ≫ f.app k at h
  have hc := (weakEquivalences C).comp_mem _ _
    (replacementComparison_objectwiseWeakEquivalence K I J F k) (hf k)
  exact (weakEquivalences C).of_postcomp _ _
    (replacementComparison_objectwiseWeakEquivalence K I J G k) (h.symm ▸ hc)

abbrev functor : (K ⥤ C) ⥤ C := replacement K I J ⋙ colim

abbrev comparison : functor K I J ⟶ (colim : (K ⥤ C) ⥤ C) :=
  Functor.whiskerRight (replacementComparison K I J) colim

lemma comparison_weakEquivalence_of_cofibrant (F : K ⥤ C)
    (hF : let := Projective.modelCategory K I J; IsCofibrant F) :
    weakEquivalences C ((comparison K I J).app F) := by
  let := Projective.modelCategory K I J
  have : IsCofibrant ((𝟭 (K ⥤ C)).obj F) := hF
  have := Projective.colimit_isLeftQuillen K I J
  have := replacement_isCofibrant K I J F
  have : WeakEquivalence ((replacementComparison K I J).app F) :=
    ⟨(replacementComparison_trivialFibration K I J F).2⟩
  have := Quillen.map_weakEquivalence_of_cofibrant (colim : (K ⥤ C) ⥤ C)
    ((replacementComparison K I J).app F)
  exact mem_weakEquivalences ((colim : (K ⥤ C) ⥤ C).map ((replacementComparison K I J).app F))

lemma map_weakEquivalence {F G : K ⥤ C} (f : F ⟶ G)
    (hf : ∀ k, weakEquivalences C (f.app k)) :
    weakEquivalences C ((functor K I J).map f) := by
  let := Projective.modelCategory K I J
  have := Projective.colimit_isLeftQuillen K I J
  have := replacement_isCofibrant K I J F
  have := replacement_isCofibrant K I J G
  have : WeakEquivalence ((replacement K I J).map f) :=
    ⟨replacement_map_objectwiseWeakEquivalence K I J f hf⟩
  have := Quillen.map_weakEquivalence_of_cofibrant (colim : (K ⥤ C) ⥤ C)
    ((replacement K I J).map f)
  exact mem_weakEquivalences ((colim : (K ⥤ C) ⥤ C).map ((replacement K I J).map f))

def computesDerivedIso {D : Type uD} [Category.{vD} D] {H : Type uH} [Category.{vH} H]
    (Q : (K ⥤ C) ⥤ D) [Q.IsLocalization (Projective.objectwise K (weakEquivalences C))]
    (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)] (LF : D ⥤ H)
    (α : Q ⋙ LF ⟶ (colim : (K ⥤ C) ⥤ C) ⋙ L)
    [LF.IsLeftDerivedFunctor α (Projective.objectwise K (weakEquivalences C))] :
    Q ⋙ LF ≅ functor K I J ⋙ L := by
  let := Projective.modelCategory K I J
  have := Projective.colimit_isLeftQuillen K I J
  have : Q.IsLocalization (weakEquivalences (K ⥤ C)) :=
    inferInstanceAs (Q.IsLocalization (Projective.objectwise K (weakEquivalences C)))
  have : LF.IsLeftDerivedFunctor α (weakEquivalences (K ⥤ C)) :=
    inferInstanceAs (LF.IsLeftDerivedFunctor α (Projective.objectwise K (weakEquivalences C)))
  let a : replacement K I J ⋙ Q ⋙ LF ⟶ Q ⋙ LF :=
    Functor.whiskerRight (replacementComparison K I J) (Q ⋙ LF)
  let b : replacement K I J ⋙ Q ⋙ LF ⟶ functor K I J ⋙ L :=
    Functor.whiskerLeft (replacement K I J) α
  have : ∀ F, IsIso (a.app F) := by
    intro F
    have : IsIso (Q.map ((replacementComparison K I J).app F)) :=
      Localization.inverts Q (weakEquivalences (K ⥤ C)) _
        (replacementComparison_trivialFibration K I J F).2
    change IsIso (LF.map (Q.map ((replacementComparison K I J).app F)))
    infer_instance
  have : ∀ F, IsIso (b.app F) := by
    intro F
    have := replacement_isCofibrant K I J F
    exact Quillen.leftComparison_isIso Q L α ((replacement K I J).obj F)
  have : IsIso a := NatIso.isIso_of_isIso_app a
  have : IsIso b := NatIso.isIso_of_isIso_app b
  let ea := asIso a
  let eb := asIso b
  exact ea.symm ≪≫ eb

end SerrePositivity.DiagramModel.HomotopyColimit
