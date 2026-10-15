module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Boundary

/-! # The two extensions of a lower-degree natural transformation

A transformation defined strictly below deg j induces L_j F ⟶ G_j and
F_j ⟶ M_j G. Their compatibility is forced by naturality on composites
of incoming direct and outgoing inverse maps, whose endpoints are lower.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J) {C : Type u'} [Category.{v'} C]
  {F G : J ⥤ C} (ℓ : lowerInclusion r (r.deg j) ⋙ F ⟶ lowerInclusion r (r.deg j) ⋙ G)

abbrev latchingExtensionCocone : Cocone (latchingSource r j ⋙ F) where
  pt := G.obj j
  ι :=
    { app f := ℓ.app ((latchingSourceLower r j).obj f) ≫ G.map f.obj.hom
      naturality f f' φ := by
        have h := ℓ.naturality ((latchingSourceLower r j).map φ)
        change F.map φ.hom.left ≫ ℓ.app ((latchingSourceLower r j).obj f') =
          ℓ.app ((latchingSourceLower r j).obj f) ≫ G.map φ.hom.left at h
        change F.map φ.hom.left ≫ (ℓ.app ((latchingSourceLower r j).obj f') ≫ G.map f'.obj.hom) =
          (ℓ.app ((latchingSourceLower r j).obj f) ≫ G.map f.obj.hom) ≫ 𝟙 _
        rw [← Category.assoc, h, Category.assoc, ← G.map_comp, Over.w, Category.comp_id] }

abbrev matchingExtensionCone : Cone (matchingTarget r j ⋙ G) where
  pt := F.obj j
  π :=
    { app g := F.map g.obj.hom ≫ ℓ.app ((matchingTargetLower r j).obj g)
      naturality g g' ψ := by
        have h := ℓ.naturality ((matchingTargetLower r j).map ψ)
        change F.map ψ.hom.right ≫ ℓ.app ((matchingTargetLower r j).obj g') =
          ℓ.app ((matchingTargetLower r j).obj g) ≫ G.map ψ.hom.right at h
        change 𝟙 _ ≫ (F.map g'.obj.hom ≫ ℓ.app ((matchingTargetLower r j).obj g')) =
          (F.map g.obj.hom ≫ ℓ.app ((matchingTargetLower r j).obj g)) ≫ G.map ψ.hom.right
        rw [Category.id_comp, Category.assoc, ← h, ← Category.assoc, ← F.map_comp, Under.w] }

abbrev latchingExtension [HasColimitsOfShape (LatchingIndex r j) C] :
    (latchingEvaluation r j).obj F ⟶ G.obj j :=
  colimit.desc _ (latchingExtensionCocone r j ℓ)

abbrev matchingExtension [HasLimitsOfShape (MatchingIndex r j) C] :
    F.obj j ⟶ (matchingEvaluation r j).obj G :=
  limit.lift _ (matchingExtensionCone r j ℓ)

@[reassoc (attr := simp)]
lemma ι_latchingExtension [HasColimitsOfShape (LatchingIndex r j) C]
    (f : LatchingIndex r j) :
    colimit.ι (latchingSource r j ⋙ F) f ≫ latchingExtension r j ℓ =
      ℓ.app ((latchingSourceLower r j).obj f) ≫ G.map f.obj.hom := colimit.ι_desc _ _

@[reassoc (attr := simp)]
lemma matchingExtension_π [HasLimitsOfShape (MatchingIndex r j) C]
    (g : MatchingIndex r j) :
    matchingExtension r j ℓ ≫ limit.π (matchingTarget r j ⋙ G) g =
      F.map g.obj.hom ≫ ℓ.app ((matchingTargetLower r j).obj g) := limit.lift_π _ _

lemma latching_matching_extension [HasColimitsOfShape (LatchingIndex r j) C]
    [HasLimitsOfShape (MatchingIndex r j) C] :
    latchingExtension r j ℓ ≫ (matchingComparison r j).app G =
      (latchingComparison r j).app F ≫ matchingExtension r j ℓ := by
  apply colimit.hom_ext
  intro f
  apply limit.hom_ext
  intro g
  change (colimit.ι (latchingSource r j ⋙ F) f ≫
      (latchingExtension r j ℓ ≫ limit.lift _ (matchingCone r G j))) ≫
        limit.π (matchingTarget r j ⋙ G) g =
    (colimit.ι (latchingSource r j ⋙ F) f ≫
      (colimit.desc _ (latchingCocone r F j) ≫ matchingExtension r j ℓ)) ≫
        limit.π (matchingTarget r j ⋙ G) g
  rw [ι_latchingExtension_assoc, Category.assoc, Category.assoc, limit.lift_π,
    colimit.ι_desc_assoc, Category.assoc, matchingExtension_π]
  rw [← G.map_comp, ← Category.assoc, ← F.map_comp]
  exact (ℓ.naturality (crossing r j f g)).symm

end SerrePositivity.Reedy
