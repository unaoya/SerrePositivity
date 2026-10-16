module

public import SerrePositivity.CategoryTheory.SimplexChainParameter
public import Mathlib.CategoryTheory.Elements

/-! # An actual natural map from the nerve of a simplex category to its simplicial set

For a chain of face and degeneracy maps, all vertices are taken inside the
same first simplex using the actual prefix operators. No weak equivalence
of this map or model structure is assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.SimplexNerveAugmentation
variable (X : SSet.{v})

abbrev parameter {n : ℕ} (c : ComposableArrows X.Elements n) :
    SimplexCategory.mk n ⟶ (c.obj 0).obj.unop :=
  SimplexChainParameter.parameter (c ⋙ Functor.Elements.π X)

abbrev simplex {n : ℕ} (c : ComposableArrows X.Elements n) :
    X.obj (Opposite.op (SimplexCategory.mk n)) :=
  X.map (parameter X c).op (c.obj 0).val

lemma simplex_operator {n m : ℕ} (c : ComposableArrows X.Elements n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    X.map θ.op (simplex X c) =
      simplex X ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  let d := (SimplexCategory.toCat.map θ).toFunctor ⋙ c
  let k := c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))
  change X.map θ.op (X.map (parameter X c).op (c.obj 0).val) =
    X.map (parameter X d).op (c.obj (θ.toOrderHom 0)).val
  calc
    _ = X.map (θ ≫ parameter X c).op (c.obj 0).val :=
      (congrArg (fun f => f (c.obj 0).val) (X.map_comp (parameter X c).op θ.op)).symm
    _ = X.map (parameter X d).op (X.map k.hom (c.obj 0).val) := by
      rw [show θ ≫ parameter X c = parameter X d ≫ k.hom.unop from
        SimplexChainParameter.reindex (c ⋙ Functor.Elements.π X) θ]
      exact congrArg (fun f => f (c.obj 0).val) (X.map_comp k.hom (parameter X d).op)
    _ = _ := congrArg (fun x => X.map (parameter X d).op x) k.map_val

def augmentation : nerve X.Elements ⟶ X where
  app _ := ↾fun c => simplex X c
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    exact (simplex_operator X c θ.unop).symm

lemma naturality {Y : SSet.{v}} (f : X ⟶ Y) :
    nerveMap f.mapElements ≫ augmentation Y = augmentation X ≫ f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  exact (congrArg (fun k => k (c.obj 0).val)
    (f.naturality (parameter X c).op)).symm

end SerrePositivity.SimplicialModel.SimplexNerveAugmentation
