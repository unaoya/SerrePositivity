module

public import SerrePositivity.CategoryTheory.NerveSimplexStart
public import SerrePositivity.CategoryTheory.LabelledChain
public import SerrePositivity.CategoryTheory.NerveHomotopyUniverse
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveAugmentation

/-! # The first-simplex functor recovers the actual nerve augmentation

All original simplex operators and their prefix maps are used. The
identity is an equality of whole simplicial maps, before localization.
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.NerveSimplexFirstFunctor
variable (D : Type u) [Category.{v} D]

def first : (nerve D).Elements ⥤ D where
  obj s := s.val.obj 0
  map f := NerveSimplexStart.startMap f.op
  map_id s := NerveSimplexStart.startMap_id (Opposite.op s)
  map_comp f g := NerveSimplexStart.startMap_comp g.op f.op

lemma canonical_chain {n : ℕ} (δ : ComposableArrows SimplexCategoryᵒᵖ n)
    (z : (nerve D).obj (δ.obj 0)) :
    LabelledChain.lift (nerve D) δ z ⋙ first D =
      (SimplexCategory.toCat.map (SimplexChainParameter.parameter δ)).toFunctor ⋙ z := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have he : δ.map (homOfLE (Fin.zero_le i)) ≫ δ.map h =
      δ.map (homOfLE (Fin.zero_le j)) := (δ.map_comp _ _).symm
  have hi := congrArg (fun f => f.unop.toOrderHom 0) he
  change z.map (homOfLE ((δ.map (homOfLE (Fin.zero_le i))).unop.toOrderHom.monotone
      (Fin.zero_le ((δ.map h).unop.toOrderHom 0)))) ≫
      eqToHom (congrArg z.obj hi) = _
  rw [← eqToHom_map z hi, ← z.map_comp]
  apply congrArg z.map
  exact Subsingleton.elim _ _

lemma chain_augmentation {n : ℕ} (c : ComposableArrows (nerve D).Elements n) :
    c ⋙ first D =
      (SimplicialModel.SimplexNerveAugmentation.augmentation (nerve D)).app
        (Opposite.op (SimplexCategory.mk n)) c := by
  calc
    _ = LabelledChain.lift (nerve D)
        (c ⋙ Functor.Elements.π (nerve D)) (c.obj 0).val ⋙ first D :=
      congrArg (fun e => e ⋙ first D) (LabelledChain.reconstruct (nerve D) c).symm
    _ = _ := canonical_chain D _ _

lemma augmentation_eq : NerveHomotopyUniverse.map (first D) =
    SSet.uliftFunctor.{max u v, max u v}.map
      (SimplicialModel.SimplexNerveAugmentation.augmentation (nerve D)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  apply ULift.ext
  exact chain_augmentation D c.down

end SerrePositivity.NerveSimplexFirstFunctor
