module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-! # Pointwise parametrized adjunctions and evaluated pullback objects -/

@[expose] public section
universe s t v₁ u₁ v₂ u₂ v₃ u₃
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.PointwiseAdjunction
variable (K : Type t) [Category.{s} K]
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]

abbrev pointwise (F : C₁ ⥤ C₂ ⥤ C₃) : C₁ ⥤ (K ⥤ C₂) ⥤ (K ⥤ C₃) :=
  F ⋙ Functor.whiskeringRight K C₂ C₃

def adjunction {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (adj : F ⊣₂ G) :
    pointwise K F ⊣₂ pointwise K G where
  adj X := (adj.adj X).whiskerRight K
  unit_whiskerRight_map f := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext k
    simpa using congr_app (adj.unit_whiskerRight_map f) (M.obj k)

def evaluatePullbackObjObj (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂) [HasPullbacks C₂]
    {A B : C₁} (i : A ⟶ B) {X Y : K ⥤ C₃} (p : X ⟶ Y)
    (sq : (pointwise K G).PullbackObjObj i p) (k : K) :
    G.PullbackObjObj i (p.app k) where
  pt := sq.pt.obj k
  fst := sq.fst.app k
  snd := sq.snd.app k
  isPullback := sq.isPullback.map ((evaluation K C₂).obj k)
  π := sq.π.app k
  π_fst := congr_app sq.π_fst k
  π_snd := congr_app sq.π_snd k

end SerrePositivity.PointwiseAdjunction
