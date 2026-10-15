module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionBoundary

/-! # The relative boundary map for a one-object factorization step

A factorization below the new object determines a map from the relative
latching pushout to the relative matching pullback. Factoring this actual
map supplies the new intermediate object of the diagram factorization.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.RelativeExtension
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  {r : ReedyStructure inverse direct α} {j : J}
  {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C]
  {F G : Lower r (r.deg j) ⥤ C} {d : BoundaryExtension r j F}
  {e : BoundaryExtension r j G} {τ : F ⟶ G} (m : d.Map e τ)
  {lowerLeft lowerRight : MorphismProperty (Lower r (r.deg j) ⥤ C)}
  (a : MorphismProperty.MapFactorizationData lowerLeft lowerRight τ)

abbrev Domain := pushout ((lowerLatchingEvaluation r j).map a.i) d.latchingMap
abbrev Codomain := pullback e.matchingMap ((lowerMatchingEvaluation r j).map a.p)

abbrev top : (lowerLatchingEvaluation r j).obj a.Z ⟶ Codomain (e := e) a :=
  pullback.lift ((lowerLatchingEvaluation r j).map a.p ≫ e.latchingMap)
    (lowerBoundary r j a.Z) (by
      rw [Category.assoc, e.boundary_fac, lowerBoundary_naturality])

abbrev bottom : d.obj ⟶ Codomain (e := e) a :=
  pullback.lift m.hom (d.matchingMap ≫ (lowerMatchingEvaluation r j).map a.i) (by
    rw [Category.assoc, ← Functor.map_comp, a.fac, m.matching_naturality])

omit [HasPushouts C] in
lemma compatibility : (lowerLatchingEvaluation r j).map a.i ≫ top (e := e) a =
    d.latchingMap ≫ bottom m a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, ← Functor.map_comp, a.fac, m.latching_naturality]
  · simp only [Category.assoc, pullback.lift_snd]
    rw [lowerBoundary_naturality, ← d.boundary_fac, Category.assoc]

abbrev map : Domain (d := d) a ⟶ Codomain (e := e) a :=
  pushout.desc (top (e := e) a) (bottom m a) (compatibility m a)

@[reassoc (attr := simp)]
lemma inl_map_fst : pushout.inl _ _ ≫ map m a ≫ pullback.fst _ _ =
    (lowerLatchingEvaluation r j).map a.p ≫ e.latchingMap := by
  rw [pushout.inl_desc_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma inl_map_snd : pushout.inl _ _ ≫ map m a ≫ pullback.snd _ _ =
    lowerBoundary r j a.Z := by
  rw [pushout.inl_desc_assoc, pullback.lift_snd]

@[reassoc (attr := simp)]
lemma inr_map_fst : pushout.inr _ _ ≫ map m a ≫ pullback.fst _ _ = m.hom := by
  rw [pushout.inr_desc_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma inr_map_snd : pushout.inr _ _ ≫ map m a ≫ pullback.snd _ _ =
    d.matchingMap ≫ (lowerMatchingEvaluation r j).map a.i := by
  rw [pushout.inr_desc_assoc, pullback.lift_snd]

variable {left right : MorphismProperty C}
  (q : MorphismProperty.MapFactorizationData left right (map m a))

abbrev boundaryFactorization : MorphismProperty.MapFactorizationData ⊤ ⊤
    (lowerBoundary r j a.Z) where
  Z := q.Z
  i := pushout.inl _ _ ≫ q.i
  p := q.p ≫ pullback.snd _ _
  fac := by rw [Category.assoc, ← Category.assoc q.i, q.fac, inl_map_snd]
  hi := trivial
  hp := trivial

abbrev extension : BoundaryExtension r j a.Z :=
  boundaryExtension r j a.Z (boundaryFactorization m a q)


abbrev leftMap : d.Map (extension m a q) a.i :=
  BoundaryExtension.mapOfBoundary d (extension m a q) a.i (pushout.inr _ _ ≫ q.i)
    (by
      rw [BoundaryExtension.boundaryExtension_latchingMap]
      change (lowerLatchingEvaluation r j).map a.i ≫ (pushout.inl _ _ ≫ q.i) = _
      rw [← Category.assoc, pushout.condition, Category.assoc])
    (by
      rw [BoundaryExtension.boundaryExtension_matchingMap]
      change (pushout.inr _ _ ≫ q.i) ≫ (q.p ≫ pullback.snd _ _) = _
      rw [Category.assoc, ← Category.assoc q.i, q.fac, inr_map_snd])

abbrev rightMap : (extension m a q).Map e a.p :=
  BoundaryExtension.mapOfBoundary (extension m a q) e a.p (q.p ≫ pullback.fst _ _)
    (by
      rw [BoundaryExtension.boundaryExtension_latchingMap]
      change _ = (pushout.inl _ _ ≫ q.i) ≫ (q.p ≫ pullback.fst _ _)
      rw [Category.assoc, ← Category.assoc q.i, q.fac, inl_map_fst])
    (by
      rw [BoundaryExtension.boundaryExtension_matchingMap]
      change (q.p ≫ pullback.fst _ _) ≫ e.matchingMap =
        (q.p ≫ pullback.snd _ _) ≫ (lowerMatchingEvaluation r j).map a.p
      rw [Category.assoc, pullback.condition, Category.assoc])


/-- Relative latching map at the newly attached object. -/
abbrev relativeLeft : Domain (d := d) a ⟶ q.Z :=
  pushout.desc (extension m a q).latchingMap (leftMap m a q).hom
    (leftMap m a q).latching_naturality

/-- Relative matching map at the newly attached object. -/
abbrev relativeRight : q.Z ⟶ Codomain (e := e) a :=
  pullback.lift (rightMap m a q).hom (extension m a q).matchingMap
    (rightMap m a q).matching_naturality

lemma relativeLeft_eq : relativeLeft m a q = q.i := by
  apply pushout.hom_ext
  · rw [pushout.inl_desc, BoundaryExtension.boundaryExtension_latchingMap]
  · rw [pushout.inr_desc]
    rfl

lemma relativeRight_eq : relativeRight m a q = q.p := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    rfl
  · rw [pullback.lift_snd, BoundaryExtension.boundaryExtension_matchingMap]

lemma relativeLeft_mem : left (relativeLeft m a q) := by
  rw [relativeLeft_eq]
  exact q.hi

lemma relativeRight_mem : right (relativeRight m a q) := by
  rw [relativeRight_eq]
  exact q.hp

lemma leftMap_rightMap :
    (leftMap m a q).toNatTrans ≫ (rightMap m a q).toNatTrans = m.toNatTrans := by
  ext x
  cases x with
  | none =>
    change (pushout.inr _ _ ≫ q.i) ≫ (q.p ≫ pullback.fst _ _) = m.hom
    rw [Category.assoc, ← Category.assoc q.i, q.fac, inr_map_fst]
  | some x =>
    change a.i.app x ≫ a.p.app x = τ.app x
    exact congrArg (fun t ↦ t.app x) a.fac

/-- The actual extended intermediate diagram and the two natural transformations.
Membership in Reedy factorization classes is a separate subsequent assertion. -/
abbrev diagramFactorization : MorphismProperty.MapFactorizationData ⊤ ⊤ m.toNatTrans where
  Z := (extension m a q).toFunctor
  i := (leftMap m a q).toNatTrans
  p := (rightMap m a q).toNatTrans
  fac := leftMap_rightMap m a q
  hi := trivial
  hp := trivial

end SerrePositivity.Reedy.RelativeExtension
