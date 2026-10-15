module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeBoundaryFunctor

/-! # Functorial one-object Reedy factorization

A chosen source factorization functor acts on the relative boundary functor.
Its middle maps satisfy the attaching laws, define an actual functor on the
category of factorization problems, and commute with both factor legs.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy.FactorizationProblem
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  {r : ReedyStructure inverse direct α} {j : J}
  {C : Type u'} [Category.{v'} C]
  [HasColimitsOfShape (LatchingIndex r j) C] [HasLimitsOfShape (MatchingIndex r j) C]
  [HasPushouts C] [HasPullbacks C]
  {left right : MorphismProperty C} (data : MorphismProperty.FunctorialFactorizationData left right)

abbrev chosenFactor (a : FactorizationProblem r j C) := data.factorizationData (boundaryMap a)

abbrev chosenMap {a b : FactorizationProblem r j C} (f : a ⟶ b) :=
  data.mapZ ((relativeBoundaryFunctor r j C).map f)

abbrev chosenExtension (a : FactorizationProblem r j C) :=
  RelativeExtension.extension a.source.hom.upper a.factor (chosenFactor data a)

-- Keep the transparency convention used by Mathlib's `i_mapZ` and `mapZ_p`.
set_option backward.isDefEq.respectTransparency.types false in
abbrev extensionMap {a b : FactorizationProblem r j C} (f : a ⟶ b) :
    (chosenExtension data a).Map (chosenExtension data b) f.middle :=
  BoundaryExtension.mapOfBoundary (chosenExtension data a) (chosenExtension data b) f.middle
    (chosenMap data f) (by
      rw [BoundaryExtension.boundaryExtension_latchingMap,
        BoundaryExtension.boundaryExtension_latchingMap]
      change (lowerLatchingEvaluation r j).map f.middle ≫
          (pushout.inl _ _ ≫ (chosenFactor data b).i) =
        (pushout.inl _ _ ≫ (chosenFactor data a).i) ≫ chosenMap data f
      have h := data.i_mapZ ((relativeBoundaryFunctor r j C).map f)
      change (chosenFactor data a).i ≫ chosenMap data f = domainMap f ≫ (chosenFactor data b).i at h
      have hd := inl_domainMap f
      rw [← Category.assoc, ← hd, Category.assoc, ← h, ← Category.assoc]) (by
      rw [BoundaryExtension.boundaryExtension_matchingMap,
        BoundaryExtension.boundaryExtension_matchingMap]
      change chosenMap data f ≫ ((chosenFactor data b).p ≫ pullback.snd _ _) =
        ((chosenFactor data a).p ≫ pullback.snd _ _) ≫ (lowerMatchingEvaluation r j).map f.middle
      have h := data.mapZ_p ((relativeBoundaryFunctor r j C).map f)
      change chosenMap data f ≫ (chosenFactor data b).p =
        (chosenFactor data a).p ≫ codomainMap f at h
      have hc := codomainMap_snd f
      rw [← Category.assoc, h, Category.assoc, hc, ← Category.assoc])

variable (r j C) in
def extensionFunctor : FactorizationProblem r j C ⥤ BoundaryDiagram r j C where
  obj a := BoundaryDiagram.ofExtension (chosenExtension data a)
  map f := BoundaryDiagram.homOfMap (extensionMap data f)
  map_id a := by
    apply BoundaryDiagram.Hom.ext
    · rfl
    · change data.Z.map ((relativeBoundaryFunctor r j C).map (𝟙 a)) = 𝟙 _
      rw [Functor.map_id, Functor.map_id]
  map_comp f g := by
    apply BoundaryDiagram.Hom.ext
    · rfl
    · change data.Z.map ((relativeBoundaryFunctor r j C).map (f ≫ g)) =
        data.Z.map ((relativeBoundaryFunctor r j C).map f) ≫
          data.Z.map ((relativeBoundaryFunctor r j C).map g)
      rw [Functor.map_comp, Functor.map_comp]

variable (r j C) in
set_option backward.isDefEq.respectTransparency.types false in
def leftTransformation : sourceFunctor r j C ⟶ extensionFunctor r j C data where
  app a := BoundaryDiagram.homOfMap
    (RelativeExtension.leftMap a.source.hom.upper a.factor (chosenFactor data a))
  naturality a b f := by
    apply BoundaryDiagram.Hom.ext
    · exact f.left
    · change f.boundary.left.upper.hom ≫ (pushout.inr _ _ ≫ (chosenFactor data b).i) =
        (pushout.inr _ _ ≫ (chosenFactor data a).i) ≫ chosenMap data f
      have h := data.i_mapZ ((relativeBoundaryFunctor r j C).map f)
      change (chosenFactor data a).i ≫ chosenMap data f = domainMap f ≫ (chosenFactor data b).i at h
      have hd := inr_domainMap f
      rw [← Category.assoc, ← hd, Category.assoc, ← h, ← Category.assoc]

variable (r j C) in
set_option backward.isDefEq.respectTransparency.types false in
def rightTransformation : extensionFunctor r j C data ⟶ targetFunctor r j C where
  app a := BoundaryDiagram.homOfMap
    (RelativeExtension.rightMap a.source.hom.upper a.factor (chosenFactor data a))
  naturality a b f := by
    apply BoundaryDiagram.Hom.ext
    · exact f.right
    · change chosenMap data f ≫ ((chosenFactor data b).p ≫ pullback.fst _ _) =
        ((chosenFactor data a).p ≫ pullback.fst _ _) ≫ f.boundary.right.upper.hom
      have h := data.mapZ_p ((relativeBoundaryFunctor r j C).map f)
      change chosenMap data f ≫ (chosenFactor data b).p =
        (chosenFactor data a).p ≫ codomainMap f at h
      have hc := codomainMap_fst f
      rw [← Category.assoc, h, Category.assoc, hc, ← Category.assoc]

variable (r j C) in
abbrev originalTransformation : sourceFunctor r j C ⟶ targetFunctor r j C :=
  Functor.whiskerLeft (boundaryFunctor r j C) Arrow.leftToRight

lemma left_right : leftTransformation r j C data ≫ rightTransformation r j C data =
    originalTransformation r j C := by
  ext a
  apply BoundaryDiagram.Hom.ext
  · exact a.factor.fac
  · change (pushout.inr _ _ ≫ (chosenFactor data a).i) ≫
        ((chosenFactor data a).p ≫ pullback.fst _ _) = a.source.hom.upper.hom
    rw [Category.assoc, ← Category.assoc (chosenFactor data a).i,
      (chosenFactor data a).fac, RelativeExtension.inr_map_fst]

lemma leftTransformation_mem (a : FactorizationProblem r j C) :
    left (((BoundaryDiagram.relativeLatchingArrow r j C).obj
      (Arrow.mk ((leftTransformation r j C data).app a))).hom) :=
  RelativeExtension.relativeLeft_mem a.source.hom.upper a.factor (chosenFactor data a)

lemma rightTransformation_mem (a : FactorizationProblem r j C) :
    right (((BoundaryDiagram.relativeMatchingArrow r j C).obj
      (Arrow.mk ((rightTransformation r j C data).app a))).hom) :=
  RelativeExtension.relativeRight_mem a.source.hom.upper a.factor (chosenFactor data a)

end SerrePositivity.Reedy.FactorizationProblem
