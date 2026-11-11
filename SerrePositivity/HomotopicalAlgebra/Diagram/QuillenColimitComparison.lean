module

public import SerrePositivity.HomotopicalAlgebra.Diagram.PostcompositionQuillen
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyColimit
public import SerrePositivity.HomotopicalAlgebra.Smith.Completeness

/-! # Left Quillen functors and noncofibrant diagram colimit comparisons

The target diagram after postcomposition is projectively cofibrant; the
original target diagram only needs cofibrant values. This suffices for the
left Quillen functor to send the actual homotopy-colimit comparison to a
weak equivalence, even when the original comparison is not known to be one.
-/

@[expose] public section
universe w v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.QuillenColimitComparison
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  {D : Type u'} [Category.{v'} D] [ModelCategory D] [IsLocallyPresentable.{w} D]
  (I' J' : MorphismProperty D) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I' J']
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [Quillen.IsLeftQuillen L]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
local instance : HasColimitsOfSize.{w, w} D := Smith.locallyPresentable_hasColimits (C := D)

include adj in
lemma map_colimit_map_weakEquivalence {F G : K ⥤ C} (a : F ⟶ G)
    (hF : let := Projective.modelCategory K I J; IsCofibrant F)
    (hG : ∀ k, IsCofibrant (G.obj k))
    (hGL : let := Projective.modelCategory K I' J'; IsCofibrant (G ⋙ L))
    (ha : ∀ k, weakEquivalences C (a.app k)) :
    weakEquivalences D (L.map (colim.map a)) := by
  have := adj.isLeftAdjoint
  have hFL := Projective.postcompose_isCofibrant K I J I' J' adj F hF
  let := Projective.modelCategory K I' J'
  have := hFL
  have := hGL
  have : WeakEquivalence (Functor.whiskerRight a L) := by
    constructor
    intro k
    have := Projective.isCofibrant_obj K I J F hF k
    have := hG k
    have : WeakEquivalence (a.app k) := ⟨ha k⟩
    exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant L (a.app k))
  have := Projective.colimit_isLeftQuillen K I' J'
  have hm : weakEquivalences D (colim.map (Functor.whiskerRight a L)) :=
    (weakEquivalence_iff _).mp
      (Quillen.map_weakEquivalence_of_cofibrant (colim : (K ⥤ D) ⥤ D)
        (Functor.whiskerRight a L))
  let e := preservesColimitNatIso (J := K) L
  have hn : L.map (colim.map a) ≫ (e.app G).hom =
      (e.app F).hom ≫ colim.map (Functor.whiskerRight a L) := e.hom.naturality a
  exact (weakEquivalences D).of_postcomp _ _ ((weakEquivalences D).of_isIso (e.app G).hom)
    (hn.symm ▸ (weakEquivalences D).comp_mem _ _
      ((weakEquivalences D).of_isIso (e.app F).hom) hm)

include adj in
lemma map_homotopyColimit_comparison_weakEquivalence (F : K ⥤ C)
    (hF : ∀ k, IsCofibrant (F.obj k))
    (hFL : let := Projective.modelCategory K I' J'; IsCofibrant (F ⋙ L)) :
    weakEquivalences D (L.map ((HomotopyColimit.comparison K I J).app F)) := by
  exact map_colimit_map_weakEquivalence K I J I' J' adj
    ((HomotopyColimit.replacementComparison K I J).app F)
    (HomotopyColimit.replacement_isCofibrant K I J F) hF hFL
    (HomotopyColimit.replacementComparison_objectwiseWeakEquivalence K I J F)

end SerrePositivity.DiagramModel.QuillenColimitComparison
