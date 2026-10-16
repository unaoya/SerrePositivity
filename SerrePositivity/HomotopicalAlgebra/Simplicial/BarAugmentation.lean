module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLift

/-! # Actual augmentation of the model-free bar construction to any cocone -/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] {F : D ⥤ SSet.{v}}
  {K : SSet.{v}} (a : F ⟶ (Functor.const D).obj K)

/-- Evaluate the first element of a bar chain in the actual cocone. -/
def augmentation : (functor D).obj F ⟶ SSet.uliftFunctor.{max uD vD, v}.obj K where
  app n := ↾fun c => ULift.up ((a.app (c.obj 0).obj).app n (c.obj 0).val)
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    apply ULift.ext
    let i := θ.unop.toOrderHom 0
    let e := c.obj i
    let e₀ := c.obj 0
    let f := c.map (homOfLE (Fin.zero_le i))
    have ha := congrArg (fun k : F.obj e₀.obj ⟶ K => k.app n e₀.val)
      (a.naturality f.hom)
    change (a.app e.obj).app n ((F.map f.hom).app n e₀.val) =
      (a.app e₀.obj).app n e₀.val at ha
    have hf : (F.map f.hom).app n e₀.val = e.val := f.map_val
    rw [hf] at ha
    have hn := congrArg (fun k => k e.val) ((a.app e.obj).naturality θ)
    exact hn.trans (congrArg (fun z => K.map θ z) ha)

end SerrePositivity.SimplicialModel.BarConstruction
