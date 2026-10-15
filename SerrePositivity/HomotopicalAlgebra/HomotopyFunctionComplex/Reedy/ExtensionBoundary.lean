module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionTransformation

/-! # Recovering the latching-to-matching factorization of an extension -/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)
  {C : Type u'} [Category.{v'} C]

abbrev lowerLatchingEvaluation [HasColimitsOfShape (LatchingIndex r j) C] :
    (Lower r (r.deg j) ⥤ C) ⥤ C :=
  (Functor.whiskeringLeft _ _ C).obj (latchingSourceLower r j) ⋙ colim

abbrev lowerMatchingEvaluation [HasLimitsOfShape (MatchingIndex r j) C] :
    (Lower r (r.deg j) ⥤ C) ⥤ C :=
  (Functor.whiskeringLeft _ _ C).obj (matchingTargetLower r j) ⋙ lim


lemma lowerBoundary_naturality [HasColimitsOfShape (LatchingIndex r j) C]
    [HasLimitsOfShape (MatchingIndex r j) C] {H K : Lower r (r.deg j) ⥤ C} (τ : H ⟶ K) :
    (lowerLatchingEvaluation r j).map τ ≫ lowerBoundary r j K =
      lowerBoundary r j H ≫ (lowerMatchingEvaluation r j).map τ := by
  change colim.map (Functor.whiskerLeft (latchingSourceLower r j) τ) ≫ _ =
    _ ≫ lim.map (Functor.whiskerLeft (matchingTargetLower r j) τ)
  apply colimit.hom_ext (F := latchingSourceLower r j ⋙ H)
  intro f
  apply limit.hom_ext (F := matchingTargetLower r j ⋙ K)
  intro g
  simp only [Category.assoc, colimit.ι_map_assoc, ι_lowerBoundary_π,
    limit.map_π, ι_lowerBoundary_π_assoc]
  exact (τ.naturality (crossing r j f g)).symm

namespace BoundaryExtension
variable {r j} {H K : Lower r (r.deg j) ⥤ C} (d : BoundaryExtension r j H)

abbrev latchingCocone : Cocone (latchingSourceLower r j ⋙ H) where
  pt := d.obj
  ι :=
    { app f := d.incoming (x := (latchingSourceLower r j).obj f) f.obj.hom f.property.1
      naturality f g φ := by
        change H.map ((latchingSourceLower r j).map φ) ≫
          d.incoming (x := (latchingSourceLower r j).obj g) g.obj.hom g.property.1 =
          d.incoming (x := (latchingSourceLower r j).obj f) f.obj.hom f.property.1 ≫ 𝟙 _
        have h := d.incoming_naturality ((latchingSourceLower r j).map φ)
          g.obj.hom g.property.1 (by
            change direct (φ.hom.left ≫ g.obj.hom)
            rw [Over.w]
            exact f.property.1)
        change H.map ((latchingSourceLower r j).map φ) ≫
          d.incoming (x := (latchingSourceLower r j).obj g) g.obj.hom g.property.1 =
          d.incoming (x := (latchingSourceLower r j).obj f) (φ.hom.left ≫ g.obj.hom) _ at h
        simpa only [Over.w, Category.comp_id] using h }

abbrev matchingCone : Cone (matchingTargetLower r j ⋙ H) where
  pt := d.obj
  π :=
    { app f := d.outgoing (x := (matchingTargetLower r j).obj f) f.obj.hom f.property.1
      naturality f g φ := by
        change 𝟙 _ ≫
          d.outgoing (x := (matchingTargetLower r j).obj g) g.obj.hom g.property.1 =
          d.outgoing (x := (matchingTargetLower r j).obj f) f.obj.hom f.property.1 ≫
          H.map ((matchingTargetLower r j).map φ)
        have h := d.outgoing_naturality f.obj.hom ((matchingTargetLower r j).map φ)
          f.property.1 (by
            change inverse (f.obj.hom ≫ φ.hom.right)
            rw [Under.w]
            exact g.property.1)
        change d.outgoing (x := (matchingTargetLower r j).obj f) f.obj.hom f.property.1 ≫
          H.map ((matchingTargetLower r j).map φ) =
          d.outgoing (x := (matchingTargetLower r j).obj g) (f.obj.hom ≫ φ.hom.right) _ at h
        simpa only [Under.w, Category.id_comp] using h.symm }

variable [HasColimitsOfShape (LatchingIndex r j) C]
  [HasLimitsOfShape (MatchingIndex r j) C]

abbrev latchingMap : (lowerLatchingEvaluation r j).obj H ⟶ d.obj :=
  colimit.desc _ d.latchingCocone

abbrev matchingMap : d.obj ⟶ (lowerMatchingEvaluation r j).obj H :=
  limit.lift _ d.matchingCone

omit [HasLimitsOfShape (MatchingIndex r j) C] in
@[reassoc (attr := simp)]
lemma ι_latchingMap (f : LatchingIndex r j) :
    colimit.ι (latchingSourceLower r j ⋙ H) f ≫ d.latchingMap =
      d.incoming (x := (latchingSourceLower r j).obj f) f.obj.hom f.property.1 := colimit.ι_desc _ _

omit [HasColimitsOfShape (LatchingIndex r j) C] in
@[reassoc (attr := simp)]
lemma matchingMap_π (g : MatchingIndex r j) :
    d.matchingMap ≫ limit.π (matchingTargetLower r j ⋙ H) g =
      d.outgoing (x := (matchingTargetLower r j).obj g) g.obj.hom g.property.1 := limit.lift_π _ _

lemma boundary_fac : d.latchingMap ≫ d.matchingMap = lowerBoundary r j H := by
  apply colimit.hom_ext (F := latchingSourceLower r j ⋙ H)
  intro f
  apply limit.hom_ext (F := matchingTargetLower r j ⋙ H)
  intro g
  simp only [Category.assoc, ι_latchingMap_assoc, matchingMap_π,
    ι_lowerBoundary_π]
  exact d.crossing (x := (latchingSourceLower r j).obj f)
    (y := (matchingTargetLower r j).obj g) f.obj.hom g.obj.hom f.property.1 g.property.1

variable {d} {e : BoundaryExtension r j K} {τ : H ⟶ K} (m : Map d e τ)

omit [HasLimitsOfShape (MatchingIndex r j) C] in
@[reassoc]
lemma Map.latching_naturality :
    (lowerLatchingEvaluation r j).map τ ≫ e.latchingMap = d.latchingMap ≫ m.hom := by
  change colim.map (Functor.whiskerLeft (latchingSourceLower r j) τ) ≫ e.latchingMap = _
  apply colimit.hom_ext (F := latchingSourceLower r j ⋙ H)
  intro f
  rw [← Category.assoc, colimit.ι_map, Category.assoc, ι_latchingMap,
    ι_latchingMap_assoc]
  exact (m.incoming (x := (latchingSourceLower r j).obj f) f.obj.hom f.property.1).symm

omit [HasColimitsOfShape (LatchingIndex r j) C] in
@[reassoc]
lemma Map.matching_naturality :
    m.hom ≫ e.matchingMap = d.matchingMap ≫ (lowerMatchingEvaluation r j).map τ := by
  change m.hom ≫ e.matchingMap =
    d.matchingMap ≫ lim.map (Functor.whiskerLeft (matchingTargetLower r j) τ)
  apply limit.hom_ext (F := matchingTargetLower r j ⋙ K)
  intro g
  rw [Category.assoc, matchingMap_π, Category.assoc, limit.map_π,
    ← Category.assoc]
  change m.hom ≫ e.outgoing (x := (matchingTargetLower r j).obj g) g.obj.hom g.property.1 =
    (d.matchingMap ≫ limit.π (matchingTargetLower r j ⋙ H) g) ≫ τ.app _
  rw [matchingMap_π]
  exact (m.outgoing (x := (matchingTargetLower r j).obj g) g.obj.hom g.property.1).symm


variable {left right : MorphismProperty C}

@[simp]
lemma boundaryExtension_latchingMap
    (q : MorphismProperty.MapFactorizationData left right (lowerBoundary r j H)) :
    (boundaryExtension r j H q).latchingMap = q.i := by
  apply colimit.hom_ext (F := latchingSourceLower r j ⋙ H)
  intro f
  rw [ι_latchingMap]
  rfl

@[simp]
lemma boundaryExtension_matchingMap
    (q : MorphismProperty.MapFactorizationData left right (lowerBoundary r j H)) :
    (boundaryExtension r j H q).matchingMap = q.p := by
  apply limit.hom_ext (F := matchingTargetLower r j ⋙ H)
  intro g
  rw [matchingMap_π]
  rfl

/-- A map of the two boundary factorizations induces a map of the whole extensions. -/
def mapOfBoundary (d : BoundaryExtension r j H) (e : BoundaryExtension r j K)
    (τ : H ⟶ K) (t : d.obj ⟶ e.obj)
    (hl : (lowerLatchingEvaluation r j).map τ ≫ e.latchingMap =
      d.latchingMap ≫ t)
    (hm : t ≫ e.matchingMap =
      d.matchingMap ≫ (lowerMatchingEvaluation r j).map τ) :
    Map d e τ where
  hom := t
  incoming {x} f hf := by
    let a : LatchingIndex r j := ⟨Over.mk f, hf, not_identities_into_top r j x f⟩
    have h := congrArg (fun k ↦ colimit.ι (latchingSourceLower r j ⋙ H) a ≫ k) hl
    change colimit.ι (latchingSourceLower r j ⋙ H) a ≫
        (colim.map (Functor.whiskerLeft (latchingSourceLower r j) τ) ≫ e.latchingMap) =
      colimit.ι (latchingSourceLower r j ⋙ H) a ≫ (d.latchingMap ≫ t) at h
    simp only [colimit.ι_map_assoc, ι_latchingMap, ι_latchingMap_assoc] at h
    exact h.symm
  outgoing {x} f hf := by
    let a : MatchingIndex r j := ⟨Under.mk f, hf, not_identities_from_top r j x f⟩
    have h := congrArg (fun k ↦ k ≫ limit.π (matchingTargetLower r j ⋙ K) a) hm
    change (t ≫ e.matchingMap) ≫ limit.π (matchingTargetLower r j ⋙ K) a =
      (d.matchingMap ≫ lim.map (Functor.whiskerLeft (matchingTargetLower r j) τ)) ≫
        limit.π (matchingTargetLower r j ⋙ K) a at h
    simp only [Category.assoc, matchingMap_π, limit.map_π] at h
    change t ≫ e.outgoing f hf =
      d.matchingMap ≫ (limit.π (matchingTargetLower r j ⋙ H) a ≫ τ.app x) at h
    rw [← Category.assoc, matchingMap_π] at h
    exact h.symm

end BoundaryExtension
end SerrePositivity.Reedy
