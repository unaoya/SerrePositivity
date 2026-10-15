module

public import SerrePositivity.Spectra.Pointed.Cofiber
public import SerrePositivity.Spectra.Pointed.AdjoinBasepoint
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # The actual pointed pushout presenting an unpointed cofiber

For f : X -> Y, its quotient Y / X is the pushout of X+ -> Y+ and
X+ -> point in the pointed category. The proof uses the actual quotient
and its maps. Applying a colimit-preserving functor therefore gives the
corresponding pushout, in particular for parameter tensor in spectra.
-/

@[expose] public section
universe v u vD uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.PointedObject
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [HasBinaryCoproducts C] {X Y : C} (f : X ⟶ Y) [HasPushout f (toUnit X)]

def cofiberProjection : adjoin Y ⟶ cofiber f :=
  (adjoinHomEquiv Y (cofiber f)).symm (cofiberQuotient f)

@[simp] lemma cofiberProjection_underlying :
    coprod.inl ≫ (cofiberProjection f).right = cofiberQuotient f := by
  simp [cofiberProjection, adjoinHomEquiv]

lemma cofiberProjection_condition :
    adjoinFunctor.map f ≫ cofiberProjection f = toPoint (adjoin X) ≫ fromPoint (cofiber f) := by
  apply Under.UnderMorphism.ext
  apply coprod.hom_ext
  · simp [adjoinFunctor, cofiberProjection, adjoinHomEquiv, toPoint, fromPoint,
      cofiberQuotient_condition, adjoin, comp_toUnit_assoc]
  · simp [adjoinFunctor, cofiberProjection, adjoinHomEquiv, toPoint, fromPoint,
      adjoin, comp_toUnit_assoc]

def cofiberPushoutCocone :
    PushoutCocone (adjoinFunctor.map f) (toPoint (adjoin X)) :=
  PushoutCocone.mk (cofiberProjection f) (fromPoint (cofiber f)) (cofiberProjection_condition f)

omit [HasPushout f (toUnit X)] in
lemma cofiberPushout_desc_condition
    (s : PushoutCocone (adjoinFunctor.map f) (toPoint (adjoin X))) :
    f ≫ coprod.inl ≫ s.inl.right = toUnit X ≫ s.pt.hom := by
  have hs : s.inr.right = s.pt.hom := by simpa [point] using Under.w s.inr
  have hc := congrArg (fun k ↦ coprod.inl ≫ k.right) s.condition
  simpa [adjoinFunctor, toPoint, hs, adjoin, comp_toUnit_assoc] using hc

def cofiberPushoutIsColimit : IsColimit (cofiberPushoutCocone f) := by
  refine PushoutCocone.IsColimit.mk (cofiberProjection_condition f) ?_ ?_ ?_ ?_
  · intro s
    exact cofiberDesc f s.pt (coprod.inl ≫ s.inl.right) (cofiberPushout_desc_condition f s)
  · intro s
    apply (adjoinHomEquiv Y s.pt).injective
    change coprod.inl ≫ (cofiberProjection f).right ≫ _ = _
    rw [← Category.assoc, cofiberProjection_underlying, cofiberQuotient_desc]
    rfl
  · intro s
    exact point_isZero.eq_of_src _ _
  · intro s m hm _
    apply cofiber_hom_ext f
    rw [cofiberQuotient_desc]
    have h := congrArg (fun k ↦ coprod.inl ≫ k.right) hm
    simpa [← Category.assoc] using h

lemma cofiber_isPushout : IsPushout (adjoinFunctor.map f) (toPoint (adjoin X))
    (cofiberProjection f) (fromPoint (cofiber f)) where
  w := cofiberProjection_condition f
  isColimit' := ⟨cofiberPushoutIsColimit f⟩

lemma map_cofiber_isPushout {D : Type uD} [Category.{vD} D]
    (F : PointedObject C ⥤ D)
    [PreservesColimit (span (adjoinFunctor.map f) (toPoint (adjoin X))) F] :
    IsPushout (F.map (adjoinFunctor.map f)) (F.map (toPoint (adjoin X)))
      (F.map (cofiberProjection f)) (F.map (fromPoint (cofiber f))) :=
  (cofiber_isPushout f).map F

end SerrePositivity.PointedObject
