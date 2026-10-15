module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.NestedMatching
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeArrow

/-! # Relative matching arrows after restriction to an inverse boundary -/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) {j : J} (g : MatchingIndex r j)
  {C : Type u'} [Category.{v'} C]
  [HasLimitsOfShape (MatchingIndex r g.obj.right) C]

instance matchingNested_hasLimits : HasLimitsOfShape (MatchingIndex (matchingReedy r j) g) C :=
  hasLimitsOfShape_of_equivalence (matchingNestedEquivalence r g)

abbrev matchingRestrictionIso (F : J ⥤ C) :
    (matchingEvaluation (matchingReedy r j) g).obj (matchingTarget r j ⋙ F) ≅
      (matchingEvaluation r g.obj.right).obj F :=
  (HasLimit.isoOfEquivalence
    (F := matchingTarget r g.obj.right ⋙ F)
    (G := matchingTarget (matchingReedy r j) g ⋙ matchingTarget r j ⋙ F)
    (matchingNestedEquivalence r g)
    (Iso.refl (matchingTarget r g.obj.right ⋙ F))).symm

@[reassoc (attr := simp)]
lemma matchingRestrictionIso_hom_π (F : J ⥤ C) (h : MatchingIndex r g.obj.right) :
    (matchingRestrictionIso r g F).hom ≫ limit.π (matchingTarget r g.obj.right ⋙ F) h =
      limit.π (matchingTarget (matchingReedy r j) g ⋙ matchingTarget r j ⋙ F)
        ((matchingNestedFunctor r g).obj h) := by
  simpa using HasLimit.isoOfEquivalence_inv_π
    (F := matchingTarget r g.obj.right ⋙ F)
    (G := matchingTarget (matchingReedy r j) g ⋙ matchingTarget r j ⋙ F)
    (matchingNestedEquivalence r g)
    (Iso.refl (matchingTarget r g.obj.right ⋙ F)) h

@[reassoc]
lemma matchingRestrictionIso_comparison (F : J ⥤ C) :
    (matchingComparison (matchingReedy r j) g).app (matchingTarget r j ⋙ F) ≫
      (matchingRestrictionIso r g F).hom = (matchingComparison r g.obj.right).app F := by
  apply limit.hom_ext
  intro h
  change (limit.lift (matchingTarget (matchingReedy r j) g ⋙ matchingTarget r j ⋙ F)
      (matchingCone (matchingReedy r j) (matchingTarget r j ⋙ F) g) ≫
      (matchingRestrictionIso r g F).hom) ≫ limit.π (matchingTarget r g.obj.right ⋙ F) h =
    limit.lift (matchingTarget r g.obj.right ⋙ F) (matchingCone r F g.obj.right) ≫
      limit.π (matchingTarget r g.obj.right ⋙ F) h
  rw [Category.assoc, matchingRestrictionIso_hom_π, limit.lift_π, limit.lift_π]
  rfl

@[reassoc]
lemma matchingRestrictionIso_naturality {F G : J ⥤ C} (τ : F ⟶ G) :
    (matchingEvaluation (matchingReedy r j) g).map (Functor.whiskerLeft (matchingTarget r j) τ) ≫
      (matchingRestrictionIso r g G).hom = (matchingRestrictionIso r g F).hom ≫
        (matchingEvaluation r g.obj.right).map τ := by
  apply limit.hom_ext
  intro h
  change (lim.map (Functor.whiskerLeft
      (matchingTarget (matchingReedy r j) g)
      (Functor.whiskerLeft (matchingTarget r j) τ)) ≫
      (matchingRestrictionIso r g G).hom) ≫ limit.π (matchingTarget r g.obj.right ⋙ G) h =
    ((matchingRestrictionIso r g F).hom ≫
      lim.map (Functor.whiskerLeft (matchingTarget r g.obj.right) τ)) ≫
        limit.π (matchingTarget r g.obj.right ⋙ G) h
  rw [Category.assoc, matchingRestrictionIso_hom_π, limit.map_π,
    Category.assoc, limit.map_π, ← Category.assoc]
  exact (congrArg (fun f ↦ f ≫ τ.app h.obj.right)
    (matchingRestrictionIso_hom_π r g F h)).symm

variable [HasPullbacks C] {F G : J ⥤ C} (τ : F ⟶ G)

abbrev matchingRestrictionPullbackMap :=
  pullback.map
    ((matchingComparison (matchingReedy r j) g).app (matchingTarget r j ⋙ G))
    ((matchingEvaluation (matchingReedy r j) g).map (Functor.whiskerLeft (matchingTarget r j) τ))
    ((matchingComparison r g.obj.right).app G) ((matchingEvaluation r g.obj.right).map τ)
    (𝟙 (G.obj g.obj.right))
    (matchingRestrictionIso r g F).hom (matchingRestrictionIso r g G).hom
    (by simpa using matchingRestrictionIso_comparison r g G)
    (matchingRestrictionIso_naturality r g τ)

set_option backward.isDefEq.respectTransparency.types false in
instance matchingRestrictionPullbackMap_isIso :
    IsIso (matchingRestrictionPullbackMap r g τ) := by
  exact pullback.map_isIso _ _ _ _ (𝟙 (G.obj g.obj.right))
    (matchingRestrictionIso r g F).hom (matchingRestrictionIso r g G).hom _ _

set_option backward.isDefEq.respectTransparency.types false in
def relativeMatchingRestrictionIso :
    Arrow.mk (relativeMatchingMap (matchingReedy r j) g
      (Functor.whiskerLeft (matchingTarget r j) τ)) ≅
        Arrow.mk (relativeMatchingMap r g.obj.right τ) :=
  Arrow.isoMk (Iso.refl _) (asIso (matchingRestrictionPullbackMap r g τ)) (by
    simp only [Iso.refl_hom, Category.id_comp]
    change relativeMatchingMap r g.obj.right τ =
      relativeMatchingMap (matchingReedy r j) g (Functor.whiskerLeft (matchingTarget r j) τ) ≫
        matchingRestrictionPullbackMap r g τ
    apply pullback.hom_ext
    · change relativeMatchingMap r g.obj.right τ ≫ pullback.fst _ _ =
        (relativeMatchingMap (matchingReedy r j) g
          (Functor.whiskerLeft (matchingTarget r j) τ) ≫
          matchingRestrictionPullbackMap r g τ) ≫ pullback.fst _ _
      rw [Category.assoc, pullback.lift_fst, relativeMatchingMap_fst]
      change τ.app g.obj.right =
        relativeMatchingMap (matchingReedy r j) g (Functor.whiskerLeft (matchingTarget r j) τ) ≫
          (pullback.fst _ _ ≫ 𝟙 ((matchingTarget r j ⋙ G).obj g))
      exact (relativeMatchingMap_fst (matchingReedy r j) g
        (Functor.whiskerLeft (matchingTarget r j) τ)).symm.trans
          (congrArg (fun f ↦ relativeMatchingMap (matchingReedy r j) g
            (Functor.whiskerLeft (matchingTarget r j) τ) ≫ f)
              (Category.comp_id (pullback.fst _ _)).symm)
    · change relativeMatchingMap r g.obj.right τ ≫ pullback.snd _ _ =
        (relativeMatchingMap (matchingReedy r j) g
          (Functor.whiskerLeft (matchingTarget r j) τ) ≫
          matchingRestrictionPullbackMap r g τ) ≫ pullback.snd _ _
      rw [Category.assoc, pullback.lift_snd, relativeMatchingMap_snd,
        ← Category.assoc, relativeMatchingMap_snd]
      exact (matchingRestrictionIso_comparison r g F).symm)

end SerrePositivity.Reedy
