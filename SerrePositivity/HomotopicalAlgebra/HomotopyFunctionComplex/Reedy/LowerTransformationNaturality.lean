module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LowerTransformation

/-! # Composition laws for the two lower-degree extension maps -/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) {C : Type u'} [Category.{v'} C]
  {E F G H : J ⥤ C}

lemma latchingExtension_restrict [HasColimitsOfShape (LatchingIndex r j) C] (τ : F ⟶ G) :
    latchingExtension r j (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ) =
      (latchingComparison r j).app F ≫ τ.app j := by
  change latchingExtension r j _ = colimit.desc _ (latchingCocone r F j) ≫ τ.app j
  apply colimit.hom_ext (F := latchingSource r j ⋙ F)
  intro f
  rw [ι_latchingExtension, colimit.ι_desc_assoc]
  exact (τ.naturality f.obj.hom).symm

lemma matchingExtension_restrict [HasLimitsOfShape (MatchingIndex r j) C] (τ : F ⟶ G) :
    matchingExtension r j (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ) =
      τ.app j ≫ (matchingComparison r j).app G := by
  change matchingExtension r j _ = τ.app j ≫ limit.lift _ (matchingCone r G j)
  apply limit.hom_ext (F := matchingTarget r j ⋙ G)
  intro g
  rw [matchingExtension_π, Category.assoc, limit.lift_π]
  exact τ.naturality g.obj.hom

lemma latchingExtension_precomp [HasColimitsOfShape (LatchingIndex r j) C]
    (τ : E ⟶ F) (ℓ : lowerInclusion r (r.deg j) ⋙ F ⟶ lowerInclusion r (r.deg j) ⋙ G) :
    (latchingEvaluation r j).map τ ≫ latchingExtension r j ℓ =
      latchingExtension r j (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ ≫ ℓ) := by
  change colim.map (Functor.whiskerLeft (latchingSource r j) τ) ≫ latchingExtension r j ℓ = _
  apply colimit.hom_ext (F := latchingSource r j ⋙ E)
  intro f
  rw [colimit.ι_map_assoc, ι_latchingExtension, ι_latchingExtension]
  exact (Category.assoc _ _ _).symm

lemma latchingExtension_postcomp [HasColimitsOfShape (LatchingIndex r j) C]
    (ℓ : lowerInclusion r (r.deg j) ⋙ F ⟶ lowerInclusion r (r.deg j) ⋙ G) (τ : G ⟶ H) :
    latchingExtension r j ℓ ≫ τ.app j =
      latchingExtension r j (ℓ ≫ Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ) := by
  apply colimit.hom_ext (F := latchingSource r j ⋙ F)
  intro f
  rw [ι_latchingExtension_assoc, ι_latchingExtension, τ.naturality f.obj.hom]
  exact (Category.assoc _ _ _).symm

lemma matchingExtension_precomp [HasLimitsOfShape (MatchingIndex r j) C]
    (τ : E ⟶ F) (ℓ : lowerInclusion r (r.deg j) ⋙ F ⟶ lowerInclusion r (r.deg j) ⋙ G) :
    τ.app j ≫ matchingExtension r j ℓ =
      matchingExtension r j (Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ ≫ ℓ) := by
  apply limit.hom_ext (F := matchingTarget r j ⋙ G)
  intro g
  rw [Category.assoc, matchingExtension_π, matchingExtension_π, ← Category.assoc,
    ← τ.naturality g.obj.hom, Category.assoc]
  rfl

lemma matchingExtension_postcomp [HasLimitsOfShape (MatchingIndex r j) C]
    (ℓ : lowerInclusion r (r.deg j) ⋙ F ⟶ lowerInclusion r (r.deg j) ⋙ G) (τ : G ⟶ H) :
    matchingExtension r j ℓ ≫ (matchingEvaluation r j).map τ =
      matchingExtension r j (ℓ ≫ Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ) := by
  change matchingExtension r j ℓ ≫ lim.map (Functor.whiskerLeft (matchingTarget r j) τ) = _
  apply limit.hom_ext (F := matchingTarget r j ⋙ H)
  intro g
  rw [Category.assoc, limit.map_π, ← Category.assoc]
  change (matchingExtension r j ℓ ≫ limit.π (matchingTarget r j ⋙ G) g) ≫ τ.app g.obj.right =
    matchingExtension r j (ℓ ≫ Functor.whiskerLeft (lowerInclusion r (r.deg j)) τ) ≫
      limit.π (matchingTarget r j ⋙ H) g
  rw [matchingExtension_π, matchingExtension_π]
  exact Category.assoc _ _ _

end SerrePositivity.Reedy
