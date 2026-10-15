module
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Yoneda

/-! # 準同型を反転するcoyonedaと局所化のHom

Homの宇宙は局所化前後で独立。ULiftで値域をそろえ、局所化の普遍性のみを使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ v₁ v₂
namespace SerrePositivity.DifferentialGraded.LocalizationHom
open CategoryTheory Opposite
variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
variable (W : MorphismProperty C) (L : C ⥤ E) [L.IsLocalization W] (P : C)

abbrev source : C ⥤ Type (max v₁ v₂) := uliftCoyoneda.{v₂}.obj (op P)
abbrev target : E ⥤ Type (max v₁ v₂) := uliftCoyoneda.{v₁}.obj (op (L.obj P))

variable (hP : W.IsInvertedBy (coyoneda.obj (op P)))

include hP in
lemma source_inverts : W.IsInvertedBy (uliftCoyoneda.{v₂}.obj (op P)) := by
  intro X Y f hf
  have : IsIso ((coyoneda.obj (op P)).map f) := hP f hf
  change IsIso (uliftFunctor.{v₂}.map ((coyoneda.obj (op P)).map f))
  infer_instance

def model : E ⥤ Type (max v₁ v₂) :=
  Localization.lift (source P) (source_inverts W P hP) L

def fac : L ⋙ model W L P hP ≅ source P :=
  Localization.fac (source P) (source_inverts W P hP) L

def sourceMap : source P ⟶ L ⋙ target L P where
  app X := ↾fun f => ULift.up (L.map f.down)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro g
    change ULift.up (L.map (g.down ≫ f)) = ULift.up (L.map g.down ≫ L.map f)
    exact congrArg ULift.up (L.map_comp g.down f)

def comparison : model W L P hP ⟶ target L P :=
  (Localization.whiskeringLeftFunctor' L W (Type (max v₁ v₂))).preimage
    ((fac W L P hP).hom ≫ sourceMap L P)

lemma comparison_fac :
    Functor.whiskerLeft L (comparison W L P hP) =
      (fac W L P hP).hom ≫ sourceMap L P :=
  (Localization.whiskeringLeftFunctor' L W (Type (max v₁ v₂))).map_preimage _

def identityElement : (model W L P hP).obj (L.obj P) :=
  (fac W L P hP).inv.app P (ULift.up (𝟙 P))

lemma comparison_identity :
    (comparison W L P hP).app (L.obj P) (identityElement W L P hP) = ULift.up (𝟙 (L.obj P)) := by
  have h := congrArg (fun a => a (identityElement W L P hP))
    (congr_app (comparison_fac W L P hP) P)
  change (comparison W L P hP).app (L.obj P) (identityElement W L P hP) =
    ULift.up (L.map (((fac W L P hP).hom.app P
      ((fac W L P hP).inv.app P (ULift.up (𝟙 P)))).down)) at h
  have he := congrArg (fun a => a (ULift.up (𝟙 P)))
    (congr_app (fac W L P hP).inv_hom_id P)
  change (fac W L P hP).hom.app P ((fac W L P hP).inv.app P (ULift.up (𝟙 P))) = ULift.up (𝟙 P) at he
  rw [he, Functor.map_id] at h
  exact h

def inverseComparison : target L P ⟶ model W L P hP where
  app X := ↾fun g => (model W L P hP).map g.down (identityElement W L P hP)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro g
    change (model W L P hP).map (g.down ≫ f) (identityElement W L P hP) =
      (model W L P hP).map f ((model W L P hP).map g.down (identityElement W L P hP))
    rw [Functor.map_comp]
    rfl

lemma inverseComparison_comparison :
    inverseComparison W L P hP ≫ comparison W L P hP = 𝟙 (target L P) := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro g
  have h := congrArg (fun a => a (identityElement W L P hP))
    ((comparison W L P hP).naturality g.down)
  change (comparison W L P hP).app X
      ((model W L P hP).map g.down (identityElement W L P hP)) =
    ULift.up (((comparison W L P hP).app (L.obj P) (identityElement W L P hP)).down ≫ g.down) at h
  rw [comparison_identity] at h
  change (comparison W L P hP).app X
    ((model W L P hP).map g.down (identityElement W L P hP)) = g
  simpa only [Category.id_comp, ULift.up_down] using h

lemma comparison_inverseComparison :
    comparison W L P hP ≫ inverseComparison W L P hP = 𝟙 (model W L P hP) := by
  apply Localization.natTrans_ext L W
  intro X
  apply ConcreteCategory.hom_ext
  intro x
  have hc := congrArg (fun a => a x) (congr_app (comparison_fac W L P hP) X)
  change (comparison W L P hP).app (L.obj X) x =
    ULift.up (L.map (((fac W L P hP).hom.app X x).down)) at hc
  change (model W L P hP).map (((comparison W L P hP).app (L.obj X) x).down)
    (identityElement W L P hP) = x
  rw [hc]
  let g := ((fac W L P hP).hom.app X x).down
  have hn := congrArg (fun a => a (ULift.up (𝟙 P))) ((fac W L P hP).inv.naturality g)
  dsimp [source, uliftCoyoneda, uliftYoneda, yoneda, uliftFunctor, identityElement] at hn
  simp only [Category.id_comp] at hn
  change (fac W L P hP).inv.app X (ULift.up g) =
    (model W L P hP).map (L.map g) (identityElement W L P hP) at hn
  rw [← hn]
  exact congrArg (fun a => a x) (congr_app (fac W L P hP).hom_inv_id X)

def homEquiv (X : E) : (L.obj P ⟶ X) ≃ (model W L P hP).obj X where
  toFun f := (model W L P hP).map f (identityElement W L P hP)
  invFun x := ((comparison W L P hP).app X x).down
  left_inv f := by
    have h := congrArg (fun a => a (ULift.up f))
      (congr_app (inverseComparison_comparison W L P hP) X)
    exact congrArg ULift.down h
  right_inv x :=
    congrArg (fun a => a x) (congr_app (comparison_inverseComparison W L P hP) X)

def mapEquiv (X : C) : (P ⟶ X) ≃ (L.obj P ⟶ L.obj X) :=
  Equiv.ulift.symm.trans (((fac W L P hP).app X).symm.toEquiv.trans
    (homEquiv W L P hP (L.obj X)).symm)

lemma mapEquiv_apply (X : C) (f : P ⟶ X) : mapEquiv W L P hP X f = L.map f := by
  have h := congrArg (fun a => a ((fac W L P hP).inv.app X (ULift.up f)))
    (congr_app (comparison_fac W L P hP) X)
  change (comparison W L P hP).app (L.obj X) ((fac W L P hP).inv.app X (ULift.up f)) =
    ULift.up (L.map (((fac W L P hP).hom.app X
      ((fac W L P hP).inv.app X (ULift.up f))).down)) at h
  have he := congrArg (fun a => a (ULift.up f))
    (congr_app (fac W L P hP).inv_hom_id X)
  change (fac W L P hP).hom.app X ((fac W L P hP).inv.app X (ULift.up f)) = ULift.up f at he
  rw [he] at h
  exact congrArg ULift.down h

include hP in
lemma map_bijective (X : C) : Function.Bijective (L.map (X := P) (Y := X)) := by
  have h : (fun f : P ⟶ X => mapEquiv W L P hP X f) = L.map := by
    funext f
    exact mapEquiv_apply W L P hP X f
  rw [← h]
  exact (mapEquiv W L P hP X).bijective

end SerrePositivity.DifferentialGraded.LocalizationHom
