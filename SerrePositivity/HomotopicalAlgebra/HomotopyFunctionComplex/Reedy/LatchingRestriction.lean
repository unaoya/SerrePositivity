module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.NestedLatching
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow

/-! # Relative latching arrows after restriction to a direct boundary -/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) {j : J} (g : LatchingIndex r j)
  {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r g.obj.left) C]

instance latchingNested_hasColimits : HasColimitsOfShape (LatchingIndex (latchingReedy r j) g) C :=
  hasColimitsOfShape_of_equivalence (latchingNestedEquivalence r g)

abbrev latchingRestrictionIso (F : J ⥤ C) :
    (latchingEvaluation r g.obj.left).obj F ≅
      (latchingEvaluation (latchingReedy r j) g).obj (latchingSource r j ⋙ F) :=
  HasColimit.isoOfEquivalence
    (F := latchingSource r g.obj.left ⋙ F)
    (G := latchingSource (latchingReedy r j) g ⋙ latchingSource r j ⋙ F)
    (latchingNestedEquivalence r g) (Iso.refl (latchingSource r g.obj.left ⋙ F))

@[reassoc (attr := simp)]
lemma ι_latchingRestrictionIso_hom (F : J ⥤ C) (h : LatchingIndex r g.obj.left) :
    colimit.ι (latchingSource r g.obj.left ⋙ F) h ≫ (latchingRestrictionIso r g F).hom =
      colimit.ι (latchingSource (latchingReedy r j) g ⋙ latchingSource r j ⋙ F)
        ((latchingNestedFunctor r g).obj h) := by
  simpa using HasColimit.ι_isoOfEquivalence_hom
    (F := latchingSource r g.obj.left ⋙ F)
    (G := latchingSource (latchingReedy r j) g ⋙ latchingSource r j ⋙ F)
    (latchingNestedEquivalence r g) (Iso.refl (latchingSource r g.obj.left ⋙ F)) h

@[reassoc]
lemma latchingRestrictionIso_comparison (F : J ⥤ C) :
    (latchingRestrictionIso r g F).hom ≫
      (latchingComparison (latchingReedy r j) g).app (latchingSource r j ⋙ F) =
        (latchingComparison r g.obj.left).app F := by
  apply colimit.hom_ext
  intro h
  change colimit.ι (latchingSource r g.obj.left ⋙ F) h ≫
      ((latchingRestrictionIso r g F).hom ≫
        colimit.desc (latchingSource (latchingReedy r j) g ⋙ latchingSource r j ⋙ F)
          (latchingCocone (latchingReedy r j) (latchingSource r j ⋙ F) g)) =
    colimit.ι (latchingSource r g.obj.left ⋙ F) h ≫
      colimit.desc _ (latchingCocone r F g.obj.left)
  rw [← Category.assoc, ι_latchingRestrictionIso_hom, colimit.ι_desc, colimit.ι_desc]
  rfl

@[reassoc]
lemma latchingRestrictionIso_naturality {F G : J ⥤ C} (τ : F ⟶ G) :
    (latchingEvaluation r g.obj.left).map τ ≫ (latchingRestrictionIso r g G).hom =
      (latchingRestrictionIso r g F).hom ≫
        (latchingEvaluation (latchingReedy r j) g).map 
          (Functor.whiskerLeft (latchingSource r j) τ) := by
  apply colimit.hom_ext
  intro h
  change colimit.ι (latchingSource r g.obj.left ⋙ F) h ≫
      (colim.map (Functor.whiskerLeft (latchingSource r g.obj.left) τ) ≫
        (latchingRestrictionIso r g G).hom) =
    colimit.ι (latchingSource r g.obj.left ⋙ F) h ≫
      ((latchingRestrictionIso r g F).hom ≫
        colim.map (Functor.whiskerLeft (latchingSource (latchingReedy r j) g)
          (Functor.whiskerLeft (latchingSource r j) τ)))
  rw [← Category.assoc, colimit.ι_map, Category.assoc, ι_latchingRestrictionIso_hom,
    ← Category.assoc, ι_latchingRestrictionIso_hom, colimit.ι_map]
  rfl

variable [HasPushouts C] {F G : J ⥤ C} (τ : F ⟶ G)

abbrev latchingRestrictionPushoutMap :=
  pushout.map ((latchingEvaluation r g.obj.left).map τ) ((latchingComparison r g.obj.left).app F)
    ((latchingEvaluation (latchingReedy r j) g).map (Functor.whiskerLeft (latchingSource r j) τ))
    ((latchingComparison (latchingReedy r j) g).app (latchingSource r j ⋙ F))
    (latchingRestrictionIso r g G).hom (𝟙 (F.obj g.obj.left)) (latchingRestrictionIso r g F).hom
    (latchingRestrictionIso_naturality r g τ)
    (by simpa using (latchingRestrictionIso_comparison r g F).symm)

set_option backward.isDefEq.respectTransparency.types false in
instance latchingRestrictionPushoutMap_isIso : IsIso (latchingRestrictionPushoutMap r g τ) := by
  exact pushout.map_isIso _ _ _ _ (latchingRestrictionIso r g G).hom
    (𝟙 (F.obj g.obj.left)) (latchingRestrictionIso r g F).hom _ _

set_option backward.isDefEq.respectTransparency.types false in
def relativeLatchingRestrictionIso : Arrow.mk (relativeLatchingMap r g.obj.left τ) ≅
    Arrow.mk (relativeLatchingMap (latchingReedy r j) g
      (Functor.whiskerLeft (latchingSource r j) τ)) :=
  Arrow.isoMk (asIso (latchingRestrictionPushoutMap r g τ)) (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.comp_id]
    change latchingRestrictionPushoutMap r g τ ≫
      relativeLatchingMap (latchingReedy r j) g (Functor.whiskerLeft (latchingSource r j) τ) =
        relativeLatchingMap r g.obj.left τ
    apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc, Category.assoc, inl_relativeLatchingMap,
        inl_relativeLatchingMap]
      exact latchingRestrictionIso_comparison r g G
    · rw [← Category.assoc, pushout.inr_desc]
      exact (congrArg (fun f ↦ f ≫ relativeLatchingMap (latchingReedy r j) g
        (Functor.whiskerLeft (latchingSource r j) τ)) (Category.id_comp _)).trans
          ((inr_relativeLatchingMap (latchingReedy r j) g
            (Functor.whiskerLeft (latchingSource r j) τ)).trans
              (inr_relativeLatchingMap r g.obj.left τ).symm))

end SerrePositivity.Reedy
