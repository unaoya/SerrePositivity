module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLift
public import Mathlib.CategoryTheory.ShrinkYoneda

/-! # Shrinking a simplicial value whose degrees have already been proved small

The inverse equivalences define every simplicial operator, so this retains
all face and degeneracy identities. No homotopical smallness assumption is substituted.
-/

@[expose] public section
universe v w uD vD
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.SmallSimplicialValue
variable (X : SSet.{max w v}) (hX : ∀ n, Small.{v} (X.obj n))

def shrink : SSet.{v} := by
  letI : FunctorToTypes.Small.{v} X := hX
  exact FunctorToTypes.shrink X

def liftIso : SSet.uliftFunctor.{max w v, v}.obj (shrink X hX) ≅ X := by
  letI : FunctorToTypes.Small.{v} X := hX
  exact NatIso.ofComponents
    (fun n => (Equiv.ulift.trans (equivShrink.{v} (X.obj n)).symm).toIso) (by
      intro n m f
      ext x
      change (equivShrink.{v} (X.obj m)).symm
          (equivShrink.{v} (X.obj m) (X.map f ((equivShrink.{v} (X.obj n)).symm x.down))) = _
      exact (equivShrink.{v} (X.obj m)).symm_apply_apply _)

variable {D : Type uD} [Category.{vD} D]
  (F : D ⥤ SSet.{max w v}) (hF : ∀ d n, Small.{v} ((F.obj d).obj n))

/-- All base morphisms are shrunk simultaneously. The base category may be large. -/
def shrinkDiagram : D ⥤ SSet.{v} where
  obj d := shrink (F.obj d) (hF d)
  map {d e} f := by
    letI : FunctorToTypes.Small.{v} (F.obj d) := hF d
    letI : FunctorToTypes.Small.{v} (F.obj e) := hF e
    exact FunctorToTypes.shrinkMap (F.map f)
  map_id d := by
    ext n x
    change equivShrink _ ((F.map (𝟙 d)).app n ((equivShrink _).symm x)) = x
    rw [F.map_id]
    exact (equivShrink _).apply_symm_apply x
  map_comp f g := by
    ext n x
    change equivShrink _ ((F.map (f ≫ g)).app n ((equivShrink _).symm x)) = _
    rw [F.map_comp]
    exact (congrArg (equivShrink _) (congrArg ((F.map g).app n)
      ((equivShrink _).symm_apply_apply _))).symm

def diagramLiftIso : shrinkDiagram F hF ⋙ SSet.uliftFunctor.{max w v, v} ≅ F :=
  NatIso.ofComponents (fun d => liftIso (F.obj d) (hF d)) (by
    intro d e f
    ext n x
    change (equivShrink _).symm
        (equivShrink _ ((F.map f).app n ((equivShrink _).symm x.down))) = _
    exact (equivShrink _).symm_apply_apply _)

end SerrePositivity.SimplicialModel.SmallSimplicialValue
