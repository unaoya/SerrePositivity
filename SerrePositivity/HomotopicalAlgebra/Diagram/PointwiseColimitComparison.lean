module

public import SerrePositivity.HomotopicalAlgebra.Diagram.PostcompositionQuillen
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyColimit
public import SerrePositivity.HomotopicalAlgebra.Smith.Completeness

/-! # Homotopical colimit comparison detected after transposed evaluation

The cofibrancy hypotheses concern the K diagrams obtained at each l.
No objectwise characterization of projective cofibrations on the double
diagram category is asserted.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.PointwiseColimitComparison
variable (K L : Type w) [SmallCategory K] [SmallCategory L]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
local instance : HasLimitsOfSize.{w, w} C := Smith.locallyPresentable_hasLimits (C := C)
local instance : IsLocallyPresentable.{w} (L ⥤ C) :=
  Smith.AccessibleLimits.functorCategory_isLocallyPresentable L

lemma colimit_map_weakEquivalence {F G : K ⥤ L ⥤ C} (a : F ⟶ G)
    (hF : ∀ l, let := Projective.modelCategory K I J
      IsCofibrant (F ⋙ (evaluation L C).obj l))
    (hG : ∀ l, let := Projective.modelCategory K I J
      IsCofibrant (G ⋙ (evaluation L C).obj l))
    (ha : ∀ k l, weakEquivalences C ((a.app k).app l)) (l : L) :
    weakEquivalences C (((colim : (K ⥤ L ⥤ C) ⥤ _).map a).app l) := by
  let := Projective.modelCategory K I J
  let E := (evaluation L C).obj l
  let e := preservesColimitNatIso (J := K) E
  have := hF l
  have := hG l
  have : WeakEquivalence (Functor.whiskerRight a E) := ⟨fun k => ha k l⟩
  have := Projective.colimit_isLeftQuillen K I J
  have hm : weakEquivalences C (colim.map (Functor.whiskerRight a E)) :=
    (weakEquivalence_iff _).mp
      (Quillen.map_weakEquivalence_of_cofibrant (colim : (K ⥤ C) ⥤ C)
        (Functor.whiskerRight a E))
  have hn : ((colim : (K ⥤ L ⥤ C) ⥤ _).map a).app l ≫ (e.app G).hom =
      (e.app F).hom ≫ colim.map (Functor.whiskerRight a E) := e.hom.naturality a
  exact (weakEquivalences C).of_postcomp _ _ ((weakEquivalences C).of_isIso (e.app G).hom)
    (hn.symm ▸ (weakEquivalences C).comp_mem _ _
      ((weakEquivalences C).of_isIso (e.app F).hom) hm)

lemma homotopyColimit_comparison_weakEquivalence (F : K ⥤ L ⥤ C)
    (hF : ∀ l, let := Projective.modelCategory K I J
      IsCofibrant (F ⋙ (evaluation L C).obj l)) :
    let := Projective.modelCategory L I J
    let := Projective.modelCategory_generated L I J
    weakEquivalences (L ⥤ C)
      ((HomotopyColimit.comparison K
        (Projective.generators L I) (Projective.generators L J)).app F) := by
  have := Smith.AccessibleLimits.functorCategory_isLocallyPresentable (C := C) L
  let := Projective.modelCategory L I J
  have := Projective.modelCategory_generated L I J
  let Q := HomotopyColimit.replacement K (Projective.generators L I) (Projective.generators L J)
  let q := HomotopyColimit.replacementComparison K
    (Projective.generators L I) (Projective.generators L J)
  change ∀ l, weakEquivalences C ((colim.map (q.app F)).app l)
  intro l
  apply colimit_map_weakEquivalence K L I J (q.app F) _ hF _ l
  · intro l
    have := Projective.evaluation_isLeftQuillen L I J l
    exact Projective.postcompose_isCofibrant K
      (Projective.generators L I) (Projective.generators L J) I J
      (evaluationAdjunctionLeft C l) (Q.obj F)
      (HomotopyColimit.replacement_isCofibrant K
        (Projective.generators L I) (Projective.generators L J) F)
  · intro k l
    exact HomotopyColimit.replacementComparison_objectwiseWeakEquivalence K
      (Projective.generators L I) (Projective.generators L J) F k l

end SerrePositivity.DiagramModel.PointwiseColimitComparison
