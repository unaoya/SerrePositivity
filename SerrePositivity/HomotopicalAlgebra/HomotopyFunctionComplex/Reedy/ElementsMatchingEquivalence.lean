module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsFinite
public import Mathlib.CategoryTheory.Equivalence

/-! # Actual matching-index equivalence for a category of elements

Every outgoing base arrow has one lift from the fixed element. This
identifies the whole matching category, its arrows and target diagram,
without fullness or object injectivity of the elements projection.
-/

@[expose] public section
universe v u w t
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] (F : J ⥤ Type w)
  {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (x : F.Elements)

lemma elements_map_identities {a b : F.Elements} (f : a ⟶ b)
    (h : MorphismProperty.identities F.Elements f) : MorphismProperty.identities J f.hom := by
  cases h
  exact MorphismProperty.ofHoms.mk _

abbrev elementsMatchingLift (q : MatchingIndex r x.obj) :
    MatchingIndex (elementsReedy F r) x :=
  ⟨elementsUnderLift F x q.obj, q.property.1,
    fun h => q.property.2 (elements_map_identities F _ h)⟩

def elementsMatchingForget : MatchingIndex (elementsReedy F r) x ⥤ MatchingIndex r x.obj where
  obj := elementsMatchingCode F r x
  map φ := ObjectProperty.homMk (Under.homMk φ.hom.right.hom
    (congrArg (fun f => f.hom) (Under.w φ.hom)))

/-- An actual lift of a matching triangle, retaining its exact base triangle. -/
def elementsMatchingPreimage {q q' : MatchingIndex (elementsReedy F r) x}
    (φ : elementsMatchingCode F r x q ⟶ elementsMatchingCode F r x q') : q ⟶ q' := by
  refine ObjectProperty.homMk (Under.homMk (Functor.Elements.homMk φ.hom.right ?_) ?_)
  · have hw : q.obj.hom.hom ≫ φ.hom.right = q'.obj.hom.hom := Under.w φ.hom
    rw [← q.obj.hom.map_val, ← ConcreteCategory.comp_apply, ← F.map_comp, hw]
    exact q'.obj.hom.map_val
  · exact Functor.Elements.hom_ext (Under.w φ.hom)

def elementsMatchingFullyFaithful : (elementsMatchingForget F r x).FullyFaithful where
  preimage := elementsMatchingPreimage F r x
  map_preimage φ := by
    apply ObjectProperty.hom_ext
    exact Under.UnderMorphism.ext rfl
  preimage_map φ := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    exact Functor.Elements.hom_ext rfl

lemma elementsMatchingLift_code (q : MatchingIndex r x.obj) :
    elementsMatchingCode F r x (elementsMatchingLift F r x q) = q := by
  rcases q with ⟨q, hq⟩
  obtain ⟨y, f, rfl⟩ := Under.mk_surjective q
  rfl

instance elementsMatchingForget_full : (elementsMatchingForget F r x).Full :=
  (elementsMatchingFullyFaithful F r x).full
instance elementsMatchingForget_faithful : (elementsMatchingForget F r x).Faithful :=
  (elementsMatchingFullyFaithful F r x).faithful
instance elementsMatchingForget_essSurj : (elementsMatchingForget F r x).EssSurj where
  mem_essImage q := ⟨elementsMatchingLift F r x q, ⟨eqToIso (elementsMatchingLift_code F r x q)⟩⟩
instance elementsMatchingForget_isEquivalence : (elementsMatchingForget F r x).IsEquivalence where

abbrev elementsMatchingEquivalence : MatchingIndex (elementsReedy F r) x ≌
    MatchingIndex r x.obj := (elementsMatchingForget F r x).asEquivalence

lemma elementsMatchingTarget_eq : elementsMatchingForget F r x ⋙ matchingTarget r x.obj =
    matchingTarget (elementsReedy F r) x ⋙ Functor.Elements.π F := rfl

lemma elements_op_map_identities {a b : F.Elementsᵒᵖ} (f : a ⟶ b)
    (h : MorphismProperty.identities F.Elementsᵒᵖ f) :
    MorphismProperty.identities Jᵒᵖ f.unop.hom.op := by
  cases h
  exact (MorphismProperty.identities Jᵒᵖ).id_mem _

abbrev elementsLatchingOpCode (q : LatchingIndex (elementsReedy F r).op (Opposite.op x)) :
    LatchingIndex r.op (Opposite.op x.obj) :=
  ⟨(Over.post (Functor.Elements.π F).op).obj q.obj, q.property.1, fun h => q.property.2
    ((MorphismProperty.identities_op_iff _).2 (elements_identities F q.obj.hom.unop
      ((MorphismProperty.identities_op_iff _).1 h)))⟩

def elementsLatchingOpForget : LatchingIndex (elementsReedy F r).op (Opposite.op x) ⥤
    LatchingIndex r.op (Opposite.op x.obj) where
  obj := elementsLatchingOpCode F r x
  map φ := ObjectProperty.homMk (Over.homMk φ.hom.left.unop.hom.op
    (congrArg (fun f => f.unop.hom.op) (Over.w φ.hom)))

def elementsLatchingOpPreimage
    {q q' : LatchingIndex (elementsReedy F r).op (Opposite.op x)}
    (φ : elementsLatchingOpCode F r x q ⟶ elementsLatchingOpCode F r x q') : q ⟶ q' := by
  refine ObjectProperty.homMk (Over.homMk
    (Functor.Elements.homMk (x := q'.obj.left.unop) (y := q.obj.left.unop)
      φ.hom.left.unop ?_).op ?_)
  · have hw : q'.obj.hom.unop.hom ≫ φ.hom.left.unop = q.obj.hom.unop.hom :=
      congrArg Quiver.Hom.unop (Over.w φ.hom)
    rw [← q'.obj.hom.unop.map_val, ← ConcreteCategory.comp_apply, ← F.map_comp, hw]
    exact q.obj.hom.unop.map_val
  · apply Quiver.Hom.unop_inj
    exact Functor.Elements.hom_ext (congrArg Quiver.Hom.unop (Over.w φ.hom))

def elementsLatchingOpFullyFaithful : (elementsLatchingOpForget F r x).FullyFaithful where
  preimage := elementsLatchingOpPreimage F r x
  map_preimage φ := by
    apply ObjectProperty.hom_ext
    exact Over.OverMorphism.ext rfl
  preimage_map φ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Quiver.Hom.unop_inj
    exact Functor.Elements.hom_ext rfl

abbrev elementsLatchingOpLift (q : LatchingIndex r.op (Opposite.op x.obj)) :
    LatchingIndex (elementsReedy F r).op (Opposite.op x) :=
  ⟨Over.mk (Functor.Elements.homMk
    (y := F.elementsMk q.obj.left.unop (F.map q.obj.hom.unop x.val)) q.obj.hom.unop rfl).op,
    q.property.1, fun h => q.property.2 (elements_op_map_identities F _ h)⟩

lemma elementsLatchingOpLift_code (q : LatchingIndex r.op (Opposite.op x.obj)) :
    elementsLatchingOpCode F r x (elementsLatchingOpLift F r x q) = q := by
  rcases q with ⟨q, hq⟩
  obtain ⟨y, f, rfl⟩ := Over.mk_surjective q
  rfl

instance elementsLatchingOpForget_full : (elementsLatchingOpForget F r x).Full :=
  (elementsLatchingOpFullyFaithful F r x).full
instance elementsLatchingOpForget_faithful : (elementsLatchingOpForget F r x).Faithful :=
  (elementsLatchingOpFullyFaithful F r x).faithful
instance elementsLatchingOpForget_essSurj : (elementsLatchingOpForget F r x).EssSurj where
  mem_essImage q := ⟨elementsLatchingOpLift F r x q,
    ⟨eqToIso (elementsLatchingOpLift_code F r x q)⟩⟩
instance elementsLatchingOpForget_isEquivalence :
    (elementsLatchingOpForget F r x).IsEquivalence where

abbrev elementsLatchingOpEquivalence : LatchingIndex (elementsReedy F r).op (Opposite.op x) ≌
    LatchingIndex r.op (Opposite.op x.obj) := (elementsLatchingOpForget F r x).asEquivalence

lemma elementsLatchingOpSource_eq : elementsLatchingOpForget F r x ⋙
    latchingSource r.op (Opposite.op x.obj) =
      latchingSource (elementsReedy F r).op (Opposite.op x) ⋙ (Functor.Elements.π F).op := rfl

end SerrePositivity.Reedy
