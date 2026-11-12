module

public import SerrePositivity.HomotopicalAlgebra.Pointed.CylinderCone
public import SerrePositivity.HomotopicalAlgebra.Diagram.SpanHomotopyColimit
public import Mathlib.CategoryTheory.Category.ULift

/-! # Ordinary suspension from the homotopy pushout of zero <- X -> zero

The span shape is lifted into the generating universe, independently of
the category's object and Hom universes. A good-cylinder quotient is
compared to this actual homotopy colimit by a zigzag of weak equivalences:
the cone span computes its pushout, and its contractible leaf may be
replaced by zero. No stable-model or suspension-equivalence input is used.
-/

@[expose] public section
universe w v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped ZeroObject
open SerrePositivity.DiagramModel

namespace SerrePositivity.HomotopySuspension
abbrev Shape := ULiftHom.{w} (ULift.{w} WalkingSpan)
abbrev shapeEquivalence : Shape.{w} ≌ WalkingSpan :=
  (ULiftHomULiftCategory.equiv.{w, w} WalkingSpan).symm

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]

abbrev liftSpan {A B D : C} (f : A ⟶ B) (g : A ⟶ D) : Shape.{w} ⥤ C :=
  shapeEquivalence.functor ⋙ span f g

def zeroSpanFunctor : C ⥤ (WalkingSpan ⥤ C) where
  obj X := span (0 : X ⟶ (0 : C)) (0 : X ⟶ (0 : C))
  map f := spanHomMk f (𝟙 _) (𝟙 _) (by simp) (by simp)
  map_id X := by ext (_ | _ | _) <;> simp
  map_comp f g := by ext (_ | _ | _) <;> simp

def spanFunctor : C ⥤ (Shape.{w} ⥤ C) :=
  zeroSpanFunctor ⋙ (Functor.whiskeringLeft _ _ _).obj shapeEquivalence.functor

variable [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

abbrev functor : C ⥤ C := spanFunctor ⋙ HomotopyColimit.functor Shape.{w} I J

lemma map_weakEquivalence {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C ((functor I J).map f) := by
  apply HomotopyColimit.map_weakEquivalence
  intro k
  have hs : ∀ j : WalkingSpan, weakEquivalences C ((zeroSpanFunctor.map f).app j) := by
    rintro (_ | _ | _)
    · exact hf
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
  exact hs (shapeEquivalence.functor.obj k)

variable {H : Type uH} [Category.{vH} H]
  (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)]

lemma inverts : (weakEquivalences C).IsInvertedBy (functor I J ⋙ Q) := by
  intro X Y f hf
  exact Localization.inverts Q (weakEquivalences C) _ (map_weakEquivalence I J f hf)

def localizedFunctor : H ⥤ H := Localization.lift (functor I J ⋙ Q) (inverts I J Q) Q

def localizationIso : Q ⋙ localizedFunctor I J Q ≅ functor I J ⋙ Q :=
  Localization.fac (functor I J ⋙ Q) (inverts I J Q) Q

section Proper
variable [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
  {A B D S : C} {f : A ⟶ B} {g : A ⟶ D} {l : B ⟶ S} {r : D ⟶ S}

def pushoutComparison (sq : IsPushout f g l r) :
    (HomotopyColimit.functor Shape.{w} I J).obj (liftSpan f g) ⟶ S :=
  (HomotopyColimit.comparison Shape.{w} I J).app (liftSpan f g) ≫
    ((colimit.isColimit (liftSpan f g)).coconePointUniqueUpToIso
      (sq.isColimit.whiskerEquivalence shapeEquivalence)).hom

include I J in
omit [HasZeroObject C] [HasZeroMorphisms C] in
lemma pushoutComparison_weakEquivalence (sq : IsPushout f g l r) (hf : cofibrations C f) :
    weakEquivalences C (pushoutComparison I J sq) := by
  have hD : cofibrations C ((liftSpan.{w} f g).map
      (shapeEquivalence.inverse.map WalkingSpan.Hom.fst)) := hf
  exact (weakEquivalences C).comp_mem _ _
    (HomotopyColimit.comparison_weakEquivalence_of_span Shape.{w} shapeEquivalence
      I J (liftSpan f g) hD)
    ((weakEquivalences C).of_isIso _)
end Proper

section Cylinder
variable {X S : C} (P : Cylinder X) [IsCofibrant X] [P.IsGood]
  (q : P.I ⟶ S) (sq : IsPushout P.i (0 : X ⨿ X ⟶ (0 : C)) q (0 : (0 : C) ⟶ S))

def coneSpanComparisonBase : span (ModelCylinder.coneEndpoint P) (0 : X ⟶ (0 : C)) ⟶
    span (0 : X ⟶ (0 : C)) (0 : X ⟶ (0 : C)) :=
  spanHomMk (𝟙 X) (0 : ModelCylinder.cone P ⟶ (0 : C)) (𝟙 (0 : C)) (by simp) (by simp)

def coneSpanComparison : liftSpan.{w} (ModelCylinder.coneEndpoint P) (0 : X ⟶ (0 : C)) ⟶
    (spanFunctor.{w} (C := C)).obj X :=
  Functor.whiskerLeft shapeEquivalence.functor (coneSpanComparisonBase P)

omit [IsLocallyPresentable.{w} C] in
lemma coneSpanComparison_objectwiseWeakEquivalence (k : Shape.{w}) :
    weakEquivalences C ((coneSpanComparison P).app k) := by
  have := ModelCylinder.coneCollapse_weakEquivalence P
  have hs : ∀ j : WalkingSpan, weakEquivalences C ((coneSpanComparisonBase P).app j) := by
    rintro (_ | _ | _)
    · exact (weakEquivalences C).id_mem _
    · exact mem_weakEquivalences (0 : ModelCylinder.cone P ⟶ (0 : C))
    · exact (weakEquivalences C).id_mem _
  exact hs (shapeEquivalence.functor.obj k)

lemma coneSpan_hocolim_weakEquivalence : weakEquivalences C
    ((HomotopyColimit.functor Shape.{w} I J).map (coneSpanComparison P)) :=
  HomotopyColimit.map_weakEquivalence Shape.{w} I J _
    (coneSpanComparison_objectwiseWeakEquivalence P)

variable [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

def cylinderQuotientIso : Q.obj ((functor I J).obj X) ≅ Q.obj S := by
  have := ModelCylinder.coneEndpoint_cofibration P
  let a := (HomotopyColimit.functor Shape.{w} I J).map (coneSpanComparison P)
  let b := pushoutComparison I J (ModelCylinder.coneQuotient_isPushout P q sq)
  have ha : weakEquivalences C a := coneSpan_hocolim_weakEquivalence I J P
  have hb : weakEquivalences C b := pushoutComparison_weakEquivalence I J _
    (mem_cofibrations (ModelCylinder.coneEndpoint P))
  have : IsIso (Q.map a) := Localization.inverts Q (weakEquivalences C) a ha
  have : IsIso (Q.map b) := Localization.inverts Q (weakEquivalences C) b hb
  exact (asIso (Q.map a)).symm ≪≫ asIso (Q.map b)

end Cylinder
end SerrePositivity.HomotopySuspension
