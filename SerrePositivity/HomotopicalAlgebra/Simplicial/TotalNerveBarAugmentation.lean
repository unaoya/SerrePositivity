module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction
public import SerrePositivity.CategoryTheory.SimplexChainParameter
public import SerrePositivity.CategoryTheory.LabelledChain
public import Mathlib.CategoryTheory.Functor.Currying

/-! # The actual total-element nerve maps to the diagonal bar

Every chain uses one common parameter in its first simplex, then sends
the same restricted label along all actual prefix maps. This constructs
the bridge map without a model structure or a weak equivalence assertion.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction.TotalNerve
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

abbrev values := Functor.uncurry.obj F
abbrev Total := (values F).Elements
abbrev degrees {n : ℕ} (c : ComposableArrows (Total F) n) :
    Fin (n + 1) ⥤ SimplexCategoryᵒᵖ :=
  c ⋙ Functor.Elements.π (values F) ⋙ CategoryTheory.Prod.snd _ _
abbrev objects {n : ℕ} (c : ComposableArrows (Total F) n) : Fin (n + 1) ⥤ D :=
  c ⋙ Functor.Elements.π (values F) ⋙ CategoryTheory.Prod.fst _ _

abbrev initialLabel {n : ℕ} (c : ComposableArrows (Total F) n) :
    (F.obj ((objects F c).obj 0)).obj (Opposite.op (SimplexCategory.mk n)) :=
  (F.obj ((objects F c).obj 0)).map (SimplexChainParameter.parameter (degrees F c)).op
    (c.obj 0).val

lemma initialLabel_reindex {n m : ℕ} (c : ComposableArrows (Total F) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (F.obj ((objects F c).obj (θ.toOrderHom 0))).map θ.op
        ((F.map ((objects F c).map (homOfLE (Fin.zero_le (θ.toOrderHom 0))))).app
          (Opposite.op (SimplexCategory.mk n)) (initialLabel F c)) =
      initialLabel F ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  let d := (SimplexCategory.toCat.map θ).toFunctor ⋙ c
  let h := c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))
  let T := F.obj ((objects F c).obj (θ.toOrderHom 0))
  let z := (F.map h.hom.1).app (c.obj 0).obj.2 (c.obj 0).val
  have hz : T.map h.hom.2 z = (c.obj (θ.toOrderHom 0)).val := h.map_val
  have hn := congrArg (fun f => f (c.obj 0).val)
    ((F.map h.hom.1).naturality (SimplexChainParameter.parameter (degrees F c)).op)
  change (F.map h.hom.1).app (Opposite.op (SimplexCategory.mk n))
    ((F.obj (c.obj 0).obj.1).map
      (SimplexChainParameter.parameter (degrees F c)).op (c.obj 0).val) =
        T.map (SimplexChainParameter.parameter (degrees F c)).op z at hn
  change T.map θ.op ((F.map h.hom.1).app (Opposite.op (SimplexCategory.mk n))
    ((F.obj (c.obj 0).obj.1).map
      (SimplexChainParameter.parameter (degrees F c)).op (c.obj 0).val)) = _
  rw [hn]
  calc
    _ = T.map (θ ≫ SimplexChainParameter.parameter (degrees F c)).op z :=
      (congrArg (fun f => f z) (T.map_comp
        (SimplexChainParameter.parameter (degrees F c)).op θ.op)).symm
    _ = T.map (SimplexChainParameter.parameter (degrees F d)).op
        (T.map h.hom.2 z) := by
      rw [SimplexChainParameter.reindex]
      exact congrArg (fun f => f z)
        (T.map_comp h.hom.2 (SimplexChainParameter.parameter (degrees F d)).op)
    _ = _ := congrArg (fun x => T.map
      (SimplexChainParameter.parameter (degrees F d)).op x) hz

abbrev simplex {n : ℕ} (c : ComposableArrows (Total F) n) :
    ComposableArrows ((F.flip.obj (Opposite.op (SimplexCategory.mk n))).Elements) n :=
  LabelledChain.lift (F.flip.obj (Opposite.op (SimplexCategory.mk n))) (objects F c)
    (initialLabel F c)

lemma first_vertex {n : ℕ} (c : ComposableArrows (Total F) n) :
    (simplex F c).obj 0 =
      (F.flip.obj (Opposite.op (SimplexCategory.mk n))).elementsMk
        ((objects F c).obj 0) (initialLabel F c) := by
  change (F.flip.obj (Opposite.op (SimplexCategory.mk n))).elementsMk _
    ((F.flip.obj (Opposite.op (SimplexCategory.mk n))).map
      ((objects F c).map (𝟙 0)) (initialLabel F c)) = _
  rw [(objects F c).map_id, CategoryTheory.Functor.map_id]
  rfl

lemma simplex_operator {n m : ℕ} (c : ComposableArrows (Total F) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (SimplexCategory.toCat.map θ).toFunctor ⋙ simplex F c ⋙ (F.flip.map θ.op).mapElements =
      simplex F ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  change ((SimplexCategory.toCat.map θ).toFunctor ⋙
    LabelledChain.lift (F.flip.obj (Opposite.op (SimplexCategory.mk n)))
      (objects F c) (initialLabel F c)) ⋙ (F.flip.map θ.op).mapElements = _
  rw [LabelledChain.reindex, LabelledChain.map]
  apply congrArg (LabelledChain.lift (F.flip.obj (Opposite.op (SimplexCategory.mk m)))
    (objects F ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)))
  exact initialLabel_reindex F c θ

def augmentation : nerve (Total F) ⟶ (BarConstruction.functor D).obj F where
  app _ := ↾fun c => simplex F c
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    exact (simplex_operator F c θ.unop).symm

end SerrePositivity.SimplicialModel.BarConstruction.TotalNerve
