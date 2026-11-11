module

public import SerrePositivity.HomotopicalAlgebra.Pointed.HomotopySuspension
public import SerrePositivity.HomotopicalAlgebra.Pointed.CylinderConeMap

/-! # Naturality of the ordinary suspension comparison

The homotopy-colimit comparison is natural for actual pushout cocones.
Maps of cylinders and their quotients then make the two weak-equivalence
legs commute. Cancellation of the inverted leg proves naturality of the
localized cylinder-quotient isomorphism.
-/

@[expose] public section
universe w v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel
open scoped ZeroObject

namespace SerrePositivity.HomotopySuspension
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

section Pushout
variable {A B D S A' B' D' S' : C}
  {f : A ⟶ B} {g : A ⟶ D} {l : B ⟶ S} {r : D ⟶ S}
  {f' : A' ⟶ B'} {g' : A' ⟶ D'} {l' : B' ⟶ S'} {r' : D' ⟶ S'}
  (sq : IsPushout f g l r) (sq' : IsPushout f' g' l' r')
  (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D') (z : S ⟶ S')
  (ef : f ≫ b = a ≫ f') (eg : g ≫ c = a ≫ g')
  (el : l ≫ z = b ≫ l') (er : r ≫ z = c ≫ r')

include el er in
omit [HasZeroObject C] [HasZeroMorphisms C] in
lemma pushoutComparison_naturality :
    (HomotopyColimit.functor Shape.{w} I J).map
        (Functor.whiskerLeft shapeEquivalence.functor (spanHomMk a b c ef eg)) ≫
      pushoutComparison I J sq' = pushoutComparison I J sq ≫ z := by
  let τ : liftSpan.{w} f g ⟶ liftSpan f' g' :=
    Functor.whiskerLeft shapeEquivalence.functor (spanHomMk a b c ef eg)
  let eS := (colimit.isColimit (liftSpan.{w} f g)).coconePointUniqueUpToIso
    (sq.isColimit.whiskerEquivalence shapeEquivalence)
  let eT := (colimit.isColimit (liftSpan.{w} f' g')).coconePointUniqueUpToIso
    (sq'.isColimit.whiskerEquivalence shapeEquivalence)
  have hs k : colimit.ι (liftSpan f g) k ≫ eS.hom =
      sq.cocone.ι.app (shapeEquivalence.functor.obj k) :=
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ k
  have ht k : colimit.ι (liftSpan f' g') k ≫ eT.hom =
      sq'.cocone.ι.app (shapeEquivalence.functor.obj k) :=
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ k
  have hc : ∀ k : WalkingSpan, sq.cocone.ι.app k ≫ z =
      (spanHomMk a b c ef eg).app k ≫ sq'.cocone.ι.app k := by
    rintro (_ | _ | _)
    · change (f ≫ l) ≫ z = a ≫ f' ≫ l'
      rw [Category.assoc, el, ← Category.assoc, ef, Category.assoc]
    · exact el
    · exact er
  have he : (colim : (Shape.{w} ⥤ C) ⥤ C).map τ ≫ eT.hom = eS.hom ≫ z := by
    apply colimit.hom_ext
    intro k
    rw [colimit.ι_map_assoc, ht, ← Category.assoc, hs]
    exact (hc (shapeEquivalence.functor.obj k)).symm
  change (HomotopyColimit.functor Shape.{w} I J).map τ ≫
      ((HomotopyColimit.comparison Shape.{w} I J).app _ ≫ eT.hom) =
    ((HomotopyColimit.comparison Shape.{w} I J).app _ ≫ eS.hom) ≫ z
  rw [← Category.assoc, (HomotopyColimit.comparison Shape.{w} I J).naturality τ,
    Category.assoc, he, Category.assoc]
end Pushout

section Cylinder
variable {X Y S T : C} (P : Cylinder X) (R : Cylinder Y)
  (f : X ⟶ Y) (k : P.I ⟶ R.I)
  (h₀ : P.i₀ ≫ k = f ≫ R.i₀) (h₁ : P.i₁ ≫ k = f ≫ R.i₁)

def coneSpanBaseMap : span (ModelCylinder.coneEndpoint P) (0 : X ⟶ (0 : C)) ⟶
    span (ModelCylinder.coneEndpoint R) (0 : Y ⟶ (0 : C)) :=
  spanHomMk f (ModelCylinder.coneMap P R f k h₀) (𝟙 (0 : C))
    (ModelCylinder.coneEndpoint_coneMap P R f k h₀ h₁) (by simp)

def coneSpanMap : liftSpan.{w} (ModelCylinder.coneEndpoint P) (0 : X ⟶ (0 : C)) ⟶
    liftSpan.{w} (ModelCylinder.coneEndpoint R) (0 : Y ⟶ (0 : C)) :=
  Functor.whiskerLeft shapeEquivalence.functor (coneSpanBaseMap P R f k h₀ h₁)

omit [IsLocallyPresentable.{w} C] in
lemma coneSpanComparison_naturality :
    coneSpanMap P R f k h₀ h₁ ≫ coneSpanComparison R =
      coneSpanComparison P ≫ (spanFunctor.{w} (C := C)).map f := by
  have h : coneSpanBaseMap P R f k h₀ h₁ ≫ coneSpanComparisonBase R =
      coneSpanComparisonBase P ≫ zeroSpanFunctor.map f := by
    ext (_ | _ | _) <;> simp [coneSpanBaseMap, coneSpanComparisonBase, zeroSpanFunctor]
  apply NatTrans.ext
  funext j
  exact congr_app h (shapeEquivalence.functor.obj j)

variable [IsCofibrant X] [IsCofibrant Y] [P.IsGood] [R.IsGood]
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
  {H : Type uH} [Category.{vH} H]
  (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)]
  (q : P.I ⟶ S) (r : R.I ⟶ T)
  (sq : IsPushout P.i (0 : X ⨿ X ⟶ (0 : C)) q (0 : (0 : C) ⟶ S))
  (sr : IsPushout R.i (0 : Y ⨿ Y ⟶ (0 : C)) r (0 : (0 : C) ⟶ T))
  (z : S ⟶ T) (hz : q ≫ z = k ≫ r)

lemma cylinderQuotientIso_fac :
    Q.map ((HomotopyColimit.functor Shape.{w} I J).map (coneSpanComparison P)) ≫
      (cylinderQuotientIso I J Q P q sq).hom =
        Q.map (pushoutComparison I J (ModelCylinder.coneQuotient_isPushout P q sq)) := by
  have : IsIso (Q.map ((HomotopyColimit.functor Shape.{w} I J).map (coneSpanComparison P))) :=
    Localization.inverts Q (weakEquivalences C) _ (coneSpan_hocolim_weakEquivalence I J P)
  change _ ≫ (inv _ ≫ _) = _
  simp

include k h₀ h₁ hz in
lemma cylinderQuotientIso_naturality :
    Q.map ((functor I J).map f) ≫ (cylinderQuotientIso I J Q R r sr).hom =
      (cylinderQuotientIso I J Q P q sq).hom ≫ Q.map z := by
  let Hc := HomotopyColimit.functor Shape.{w} I J
  let d := coneSpanMap P R f k h₀ h₁
  have hA : Hc.map d ≫ Hc.map (coneSpanComparison R) =
      Hc.map (coneSpanComparison P) ≫ (functor I J).map f := by
    change Hc.map d ≫ Hc.map (coneSpanComparison R) =
      Hc.map (coneSpanComparison P) ≫ Hc.map ((spanFunctor.{w} (C := C)).map f)
    simpa only [d, Functor.map_comp] using
      congrArg Hc.map (coneSpanComparison_naturality P R f k h₀ h₁)
  have hB : Hc.map d ≫ pushoutComparison I J (ModelCylinder.coneQuotient_isPushout R r sr) =
      pushoutComparison I J (ModelCylinder.coneQuotient_isPushout P q sq) ≫ z :=
    pushoutComparison_naturality I J (ModelCylinder.coneQuotient_isPushout P q sq)
      (ModelCylinder.coneQuotient_isPushout R r sr) f (ModelCylinder.coneMap P R f k h₀)
      (𝟙 (0 : C)) z (ModelCylinder.coneEndpoint_coneMap P R f k h₀ h₁) (by simp)
      (ModelCylinder.coneQuotient_naturality P R f k h₀ q r sq sr z hz) (by simp)
  have : IsIso (Q.map (Hc.map (coneSpanComparison P))) :=
    Localization.inverts Q (weakEquivalences C) _ (coneSpan_hocolim_weakEquivalence I J P)
  apply (cancel_epi (Q.map (Hc.map (coneSpanComparison P)))).mp
  rw [← Category.assoc, ← Q.map_comp, ← hA, Q.map_comp, Category.assoc,
    cylinderQuotientIso_fac I J (P := R) (Q := Q) (q := r) (sq := sr),
    ← Q.map_comp, hB, Q.map_comp,
    ← cylinderQuotientIso_fac I J (P := P) (Q := Q) (q := q) (sq := sq), Category.assoc]

end Cylinder
end SerrePositivity.HomotopySuspension
