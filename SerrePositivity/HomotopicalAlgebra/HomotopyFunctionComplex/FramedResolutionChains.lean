module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # Lift arbitrary finite composition chains using their actual frame maps

All longer arrows are composed in the framed category. Reindexing is done
on the lifted diagram itself; it never independently reselects its frames.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.FramedResolution
variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ}

abbrev chainArrow (F : ComposableArrows (ResolutionObject C) n) (i : Fin n) :=
  F.map (homOfLE (Fin.castSucc_le_succ i))

/-- The supplied adjacent frame maps, rather than freshly chosen composite lifts, are used. -/
def liftChain (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (chainArrow F i)) :
    ComposableArrows (FramedResolution C) n :=
  ComposableArrows.mkOfObjOfMapSucc (fun i => ofResolution (F.obj i))
    (fun i => ⟨chainArrow F i, (φ i).val, (φ i).property⟩)

@[simp]
lemma liftChain_obj (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (chainArrow F i)) (i : Fin (n + 1)) :
    (liftChain F φ).obj i = ofResolution (F.obj i) := rfl

lemma liftChain_adjacent (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (chainArrow F i))
    (i : ℕ) (hi : i < n) :
    (liftChain F φ).map' i (i + 1) =
      (⟨chainArrow F ⟨i, hi⟩, (φ ⟨i, hi⟩).val, (φ ⟨i, hi⟩).property⟩ :
        ofResolution (F.obj ⟨i, by omega⟩) ⟶ ofResolution (F.obj ⟨i + 1, by omega⟩)) :=
  ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi

lemma liftChain_forget (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (chainArrow F i)) :
    liftChain F φ ⋙ forget = F := by
  refine ComposableArrows.ext (F := liftChain F φ ⋙ forget) (G := F) (fun _ => rfl) ?_
  intro i hi
  have h := congrArg (fun q => q.map) (liftChain_adjacent F φ i hi)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change ((liftChain F φ).map' i (i + 1)).map = F.map' i (i + 1)
  exact h

/-- Every finite simplex lifts, with the objects and all original inner arrows retained. -/
lemma nerveForget_surjective (k : SimplexCategoryᵒᵖ) :
    Function.Surjective ((nerveMap (forget (C := C))).app k) := by
  intro F
  exact ⟨liftChain F (fun i => ResolutionLiftPrecomposition.lift (chainArrow F i)),
    liftChain_forget F _⟩

/-- Faces and degeneracies of an actual lifted chain project to the corresponding base chain. -/
lemma liftChain_reindex_forget (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (chainArrow F i))
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (θ.toOrderHom.monotone.functor ⋙ liftChain F φ) ⋙ forget =
      θ.toOrderHom.monotone.functor ⋙ F :=
  congrArg (fun G => θ.toOrderHom.monotone.functor ⋙ G) (liftChain_forget F φ)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- One contravariant diagram of target functors for an entire actual framed chain. -/
abbrev chainHom (F : ComposableArrows (FramedResolution C) n) :
    (Fin (n + 1))ᵒᵖ ⥤ C ⥤ SSet.{v} := F.op ⋙ hom hcof hfib

lemma chainHom_reindex (F : ComposableArrows (FramedResolution C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    chainHom hcof hfib (θ.toOrderHom.monotone.functor ⋙ F) =
      θ.toOrderHom.monotone.functor.op ⋙ chainHom hcof hfib F := rfl

lemma chainHom_composition (F : ComposableArrows (FramedResolution C) n)
    {i j k : (Fin (n + 1))ᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) (Z : C) :
    ((chainHom hcof hfib F).map (a ≫ b)).app Z =
      ((chainHom hcof hfib F).map a).app Z ≫ ((chainHom hcof hfib F).map b).app Z :=
  congr_app ((chainHom hcof hfib F).map_comp a b) Z

end SerrePositivity.HomotopyFunctionComplex.FramedResolution
