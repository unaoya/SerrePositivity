module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # Lifting a whole chain from its original first label

All labels are transported by the actual prefix maps. Reindexing uses the
transported label at the new first vertex, and maps of value diagrams
transport the same whole labelled chain.
-/

@[expose] public section
universe uD vD w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.LabelledChain
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ Type w)
  {n : ℕ} (c : ComposableArrows D n) (x : F.obj (c.obj 0))

lemma eqToHom_hom {a b : F.Elements} (h : a = b) :
    (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by
  cases h
  rfl

def lift : ComposableArrows F.Elements n where
  obj i := F.elementsMk (c.obj i) (F.map (c.map (homOfLE (Fin.zero_le i))) x)
  map {i j} h := Functor.Elements.homMk (c.map h) (by
    change F.map (c.map h) (F.map (c.map (homOfLE (Fin.zero_le i))) x) = _
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← c.map_comp]
    rfl)
  map_id i := by
    apply Functor.Elements.hom_ext
    exact c.map_id i
  map_comp h k := by
    apply Functor.Elements.hom_ext
    exact c.map_comp h k

lemma reindex {m : ℕ} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (SimplexCategory.toCat.map θ).toFunctor ⋙ lift F c x =
      lift F ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
        (F.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))) x) := by
  refine CategoryTheory.Functor.ext (fun i => Functor.Elements.ext _ _ rfl ?_) ?_
  · change F.map (𝟙 _) (F.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom i)))) x) = _
    rw [F.map_id, types_id_apply]
    change F.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom i)))) x =
      F.map (c.map (homOfLE (θ.toOrderHom.monotone (Fin.zero_le i))))
        (F.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))) x)
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← c.map_comp]
    rfl
  · intro i j h
    apply Functor.Elements.hom_ext
    simp [lift, eqToHom_hom]

lemma map {G : D ⥤ Type w} (a : F ⟶ G) :
    lift F c x ⋙ a.mapElements = lift G c (a.app (c.obj 0) x) := by
  refine CategoryTheory.Functor.ext (fun i => Functor.Elements.ext _ _ rfl ?_) ?_
  · change G.map (𝟙 _) (a.app (c.obj i) (F.map (c.map (homOfLE (Fin.zero_le i))) x)) = _
    rw [G.map_id, types_id_apply]
    exact congrArg (fun f => f x) (a.naturality (c.map (homOfLE (Fin.zero_le i))))
  · intro i j h
    apply Functor.Elements.hom_ext
    simp [lift, eqToHom_hom]

end SerrePositivity.LabelledChain
