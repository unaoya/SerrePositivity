module

public import SerrePositivity.CategoryTheory.AnchoredChainTransport
public import Mathlib.CategoryTheory.Elements

/-! # One category of changing central arrows and its actual factorization parameters

Objects are actual arrows. A morphism changes the source contravariantly
and the target covariantly, recording the equation for the new center.
This is the category of elements of the ordinary Hom bifunctor.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.ArrowContext
variable (D : Type u) [Category.{v} D]

abbrev homs : Dᵒᵖ × D ⥤ Type v := Functor.uncurry.obj coyoneda
abbrev Index := (homs D).Elements
abbrev projection : Index D ⥤ Dᵒᵖ × D := Functor.Elements.π (homs D)

variable {D}
abbrev source (q : Index D) : D := q.obj.1.unop
abbrev target (q : Index D) : D := q.obj.2
abbrev arrow (q : Index D) : source q ⟶ target q := q.val
abbrev ofArrow {X Y : D} (f : X ⟶ Y) : Index D := (homs D).elementsMk (Opposite.op X, Y) f

lemma equation {q r : Index D} (f : q ⟶ r) :
    (f.hom.1.unop ≫ arrow q) ≫ f.hom.2 = arrow r := f.map_val

/-- Actual transport of factorization categories as the center changes. -/
abbrev factorizationMap {q r : Index D} (f : q ⟶ r) :
    ArrowFactorization (arrow q) ⥤ ArrowFactorization (arrow r) :=
  ArrowFactorization.transport (arrow q) f.hom.1.unop f.hom.2 (arrow r) (equation f)

variable (D)
/-- All changing-center factorization categories in one strict diagram. -/
def factorizations : Index D ⥤ Cat.{v, max u v} where
  obj q := Cat.of (ArrowFactorization (arrow q))
  map f := (factorizationMap f).toCatHom
  map_id q := by
    apply Cat.Hom.ext
    exact ArrowFactorization.transport_id (arrow q)
  map_comp f g := by
    apply Cat.Hom.ext
    exact (ArrowFactorization.transport_comp _ _ _ _ (equation f) _ _ _ (equation g)).symm


/-- One whole chain parameter diagram, for all centers and all simplicial operators. -/
def parameters : Index D ⥤ SSet.{max u v} where
  obj q := AnchoredChain.simplicial (arrow q)
  map f := AnchoredChain.mapFunctor (factorizationMap f)
  map_id q := by
    change AnchoredChain.mapFunctor (ArrowFactorization.transport (arrow q)
      (𝟙 _) (𝟙 _) (arrow q) _) = _
    rw [ArrowFactorization.transport_id, AnchoredChain.mapFunctor_id]
  map_comp f g := (AnchoredChain.mapFunctor_comp _ _).trans
    (congrArg (fun F => AnchoredChain.mapFunctor F)
      (ArrowFactorization.transport_comp _ _ _ _ (equation f) _ _ _ (equation g))) |>.symm

lemma parameters_diagram {q r : Index D} (f : q ⟶ r) {n : ℕ} (c : AnchoredChain (arrow q) n) :
    (((parameters D).map f).app (Opposite.op (SimplexCategory.mk n)) c).diagram = c.diagram :=
  AnchoredChain.transport_diagram _ _ _ _ (equation f) c

lemma parameters_cut {q r : Index D} (f : q ⟶ r) {n : ℕ}
    (c : AnchoredChain (arrow q) n) (j : Fin (n + 1)) :
    (((parameters D).map f).app (Opposite.op (SimplexCategory.mk n)) c).cut j =
      (factorizationMap f).obj (c.cut j) := AnchoredChain.mapFunctor_cut _ c j

end SerrePositivity.ArrowContext
