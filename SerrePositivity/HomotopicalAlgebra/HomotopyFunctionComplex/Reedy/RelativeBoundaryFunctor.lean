module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FactorizationProblem

/-! # Functoriality of the relative boundary problem

The pushout-to-pullback arrow of a one-step factorization acts on squares
of lower factorizations. In particular, applying a chosen source
factorization functor yields middle-object maps with identity and
composition laws.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.FactorizationProblem
lemma component_left {D : Type*} [Category* D] {A B C E F G : D}
    {i : A ⟶ B} {u : B ⟶ C} {v : C ⟶ E} {p : E ⟶ F}
    {a : A ⟶ G} {k : G ⟶ C} {b : G ⟶ F}
    (h : i ≫ u = a ≫ k) (hb : k ≫ v ≫ p = b) :
    (i ≫ (u ≫ v)) ≫ p = a ≫ b := by
  calc
    _ = (i ≫ u) ≫ (v ≫ p) := by simp only [Category.assoc]
    _ = (a ≫ k) ≫ (v ≫ p) := congrArg (fun t ↦ t ≫ (v ≫ p)) h
    _ = a ≫ (k ≫ v ≫ p) := by simp only [Category.assoc]
    _ = a ≫ b := congrArg (fun t ↦ a ≫ t) hb

lemma component_right {D : Type*} [Category* D] {A B C E F G : D}
    {i : A ⟶ B} {v : B ⟶ C} {u : C ⟶ E} {p : E ⟶ F}
    {q : C ⟶ G} {z : G ⟶ F} {a : A ⟶ G}
    (h : u ≫ p = q ≫ z) (ha : i ≫ v ≫ q = a) :
    (i ≫ (v ≫ u)) ≫ p = a ≫ z := by
  calc
    _ = (i ≫ v) ≫ (u ≫ p) := by simp only [Category.assoc]
    _ = (i ≫ v) ≫ (q ≫ z) := congrArg (fun t ↦ (i ≫ v) ≫ t) h
    _ = (i ≫ v ≫ q) ≫ z := by simp only [Category.assoc]
    _ = a ≫ z := congrArg (fun t ↦ t ≫ z) ha

variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  {r : ReedyStructure inverse direct α} {j : J}
  {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C]

abbrev boundaryMap (a : FactorizationProblem r j C) :=
  RelativeExtension.map a.source.hom.upper a.factor

abbrev domainMap {a b : FactorizationProblem r j C} (f : a ⟶ b) :
    RelativeExtension.Domain (d := a.source.left.extension) a.factor ⟶
      RelativeExtension.Domain (d := b.source.left.extension) b.factor :=
  pushout.map _ _ _ _ ((lowerLatchingEvaluation r j).map f.middle)
    f.boundary.left.upper.hom ((lowerLatchingEvaluation r j).map f.boundary.left.lower)
    (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (lowerLatchingEvaluation r j).map f.left.symm)
    f.boundary.left.upper.latching_naturality.symm

abbrev codomainMap {a b : FactorizationProblem r j C} (f : a ⟶ b) :
    RelativeExtension.Codomain (e := a.source.right.extension) a.factor ⟶
      RelativeExtension.Codomain (e := b.source.right.extension) b.factor :=
  pullback.map _ _ _ _ f.boundary.right.upper.hom ((lowerMatchingEvaluation r j).map f.middle)
    ((lowerMatchingEvaluation r j).map f.boundary.right.lower)
    f.boundary.right.upper.matching_naturality.symm (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (lowerMatchingEvaluation r j).map f.right.symm)

omit [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C] in
@[reassoc (attr := simp)]
lemma inl_domainMap {a b : FactorizationProblem r j C} (f : a ⟶ b) :
    pushout.inl _ _ ≫ domainMap f = (lowerLatchingEvaluation r j).map f.middle ≫
      pushout.inl _ _ := pushout.inl_desc _ _ _

omit [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C] in
@[reassoc (attr := simp)]
lemma inr_domainMap {a b : FactorizationProblem r j C} (f : a ⟶ b) :
    pushout.inr _ _ ≫ domainMap f = f.boundary.left.upper.hom ≫ pushout.inr _ _ :=
  pushout.inr_desc _ _ _

omit [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] in
@[reassoc (attr := simp)]
lemma codomainMap_fst {a b : FactorizationProblem r j C} (f : a ⟶ b) :
    codomainMap f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.boundary.right.upper.hom :=
  pullback.lift_fst _ _ _

omit [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] in
@[reassoc (attr := simp)]
lemma codomainMap_snd {a b : FactorizationProblem r j C} (f : a ⟶ b) :
    codomainMap f ≫ pullback.snd _ _ = pullback.snd _ _ ≫
      (lowerMatchingEvaluation r j).map f.middle := pullback.lift_snd _ _ _

lemma boundaryMap_naturality {a b : FactorizationProblem r j C} (f : a ⟶ b) :
    domainMap f ≫ boundaryMap b = boundaryMap a ≫ codomainMap f := by
  dsimp only [boundaryMap]
  apply pushout.hom_ext
  · apply pullback.hom_ext
    · calc
        _ = (lowerLatchingEvaluation r j).map f.middle ≫
            ((lowerLatchingEvaluation r j).map b.factor.p ≫ b.source.right.extension.latchingMap) :=
          component_left (inl_domainMap f)
            (RelativeExtension.inl_map_fst b.source.hom.upper b.factor)
        _ = ((lowerLatchingEvaluation r j).map a.factor.p ≫
            a.source.right.extension.latchingMap) ≫ f.boundary.right.upper.hom := by
          have hr : (lowerLatchingEvaluation r j).map f.middle ≫
              (lowerLatchingEvaluation r j).map b.factor.p =
            (lowerLatchingEvaluation r j).map a.factor.p ≫
              (lowerLatchingEvaluation r j).map f.boundary.right.lower := by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg (lowerLatchingEvaluation r j).map f.right
          have hn := f.boundary.right.upper.latching_naturality
          rw [← Category.assoc, hr, Category.assoc, hn, ← Category.assoc]
        _ = _ := (component_right (codomainMap_fst f)
          (RelativeExtension.inl_map_fst a.source.hom.upper a.factor)).symm
    · calc
        _ = (lowerLatchingEvaluation r j).map f.middle ≫ lowerBoundary r j b.factor.Z :=
          component_left (inl_domainMap f)
            (RelativeExtension.inl_map_snd b.source.hom.upper b.factor)
        _ = lowerBoundary r j a.factor.Z ≫ (lowerMatchingEvaluation r j).map f.middle :=
          lowerBoundary_naturality r j f.middle
        _ = _ := (component_right (codomainMap_snd f)
          (RelativeExtension.inl_map_snd a.source.hom.upper a.factor)).symm
  · apply pullback.hom_ext
    · calc
        _ = f.boundary.left.upper.hom ≫ b.source.hom.upper.hom :=
          component_left (inr_domainMap f)
            (RelativeExtension.inr_map_fst b.source.hom.upper b.factor)
        _ = a.source.hom.upper.hom ≫ f.boundary.right.upper.hom :=
          congrArg (fun m ↦ m.upper.hom) f.boundary.w
        _ = _ := (component_right (codomainMap_fst f)
          (RelativeExtension.inr_map_fst a.source.hom.upper a.factor)).symm
    · calc
        _ = f.boundary.left.upper.hom ≫
            (b.source.left.extension.matchingMap ≫ (lowerMatchingEvaluation r j).map b.factor.i) :=
          component_left (inr_domainMap f)
            (RelativeExtension.inr_map_snd b.source.hom.upper b.factor)
        _ = (a.source.left.extension.matchingMap ≫
            (lowerMatchingEvaluation r j).map a.factor.i) ≫
            (lowerMatchingEvaluation r j).map f.middle := by
          have hl : (lowerMatchingEvaluation r j).map f.boundary.left.lower ≫
              (lowerMatchingEvaluation r j).map b.factor.i =
            (lowerMatchingEvaluation r j).map a.factor.i ≫
              (lowerMatchingEvaluation r j).map f.middle := by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg (lowerMatchingEvaluation r j).map f.left
          have hn := f.boundary.left.upper.matching_naturality
          rw [← Category.assoc, hn, Category.assoc, hl, ← Category.assoc]
        _ = _ := (component_right (codomainMap_snd f)
          (RelativeExtension.inr_map_snd a.source.hom.upper a.factor)).symm

omit [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C] in
lemma domainMap_id (a : FactorizationProblem r j C) : domainMap (𝟙 a) = 𝟙 _ := by
  apply pushout.hom_ext
  · rw [inl_domainMap, Category.comp_id]
    change (lowerLatchingEvaluation r j).map (𝟙 a.factor.Z) ≫ pushout.inl _ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [inr_domainMap, Category.comp_id]
    exact Category.id_comp _

omit [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] in
lemma codomainMap_id (a : FactorizationProblem r j C) : codomainMap (𝟙 a) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [codomainMap_fst, Category.id_comp]
    exact Category.comp_id _
  · rw [codomainMap_snd, Category.id_comp]
    change pullback.snd _ _ ≫ (lowerMatchingEvaluation r j).map (𝟙 a.factor.Z) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

omit [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C] in
lemma domainMap_comp {a b c : FactorizationProblem r j C} (f : a ⟶ b) (g : b ⟶ c) :
    domainMap (f ≫ g) = domainMap f ≫ domainMap g := by
  apply pushout.hom_ext
  · calc
      _ = (lowerLatchingEvaluation r j).map (f.middle ≫ g.middle) ≫ pushout.inl _ _ :=
        inl_domainMap (f ≫ g)
      _ = (lowerLatchingEvaluation r j).map f.middle ≫
          ((lowerLatchingEvaluation r j).map g.middle ≫ pushout.inl _ _) := by
        rw [Functor.map_comp, Category.assoc]
      _ = (lowerLatchingEvaluation r j).map f.middle ≫
          (pushout.inl _ _ ≫ domainMap g) :=
        congrArg (fun t ↦ (lowerLatchingEvaluation r j).map f.middle ≫ t) (inl_domainMap g).symm
      _ = ((lowerLatchingEvaluation r j).map f.middle ≫ pushout.inl _ _) ≫ domainMap g :=
        (Category.assoc _ _ _).symm
      _ = (pushout.inl _ _ ≫ domainMap f) ≫ domainMap g :=
        congrArg (fun t ↦ t ≫ domainMap g) (inl_domainMap f).symm
      _ = _ := Category.assoc _ _ _
  · calc
      _ = (f.boundary.left.upper.hom ≫ g.boundary.left.upper.hom) ≫ pushout.inr _ _ :=
        inr_domainMap (f ≫ g)
      _ = f.boundary.left.upper.hom ≫ (g.boundary.left.upper.hom ≫ pushout.inr _ _) :=
        Category.assoc _ _ _
      _ = f.boundary.left.upper.hom ≫ (pushout.inr _ _ ≫ domainMap g) :=
        congrArg (fun t ↦ f.boundary.left.upper.hom ≫ t) (inr_domainMap g).symm
      _ = (f.boundary.left.upper.hom ≫ pushout.inr _ _) ≫ domainMap g :=
        (Category.assoc _ _ _).symm
      _ = (pushout.inr _ _ ≫ domainMap f) ≫ domainMap g :=
        congrArg (fun t ↦ t ≫ domainMap g) (inr_domainMap f).symm
      _ = _ := Category.assoc _ _ _

omit [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] in
lemma codomainMap_comp {a b c : FactorizationProblem r j C} (f : a ⟶ b) (g : b ⟶ c) :
    codomainMap (f ≫ g) = codomainMap f ≫ codomainMap g := by
  apply pullback.hom_ext
  · rw [codomainMap_fst, Category.assoc, codomainMap_fst, ← Category.assoc, codomainMap_fst]
    exact (Category.assoc _ _ _).symm
  · rw [codomainMap_snd, Category.assoc, codomainMap_snd, ← Category.assoc, codomainMap_snd]
    change pullback.snd _ _ ≫ (lowerMatchingEvaluation r j).map (f.middle ≫ g.middle) = _
    rw [Functor.map_comp, Category.assoc]

variable (r j C) in
def relativeBoundaryFunctor : FactorizationProblem r j C ⥤ Arrow C where
  obj a := Arrow.mk (boundaryMap a)
  map f := Arrow.homMk (domainMap f) (codomainMap f) (boundaryMap_naturality f)
  map_id a := by
    apply Arrow.hom_ext
    · exact domainMap_id a
    · exact codomainMap_id a
  map_comp f g := by
    apply Arrow.hom_ext
    · exact domainMap_comp f g
    · exact codomainMap_comp f g

end SerrePositivity.Reedy.FactorizationProblem
