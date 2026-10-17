module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceFunctor
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # A strict small diagram of relative choices over all restrictions of a parameter

One root choice, including any whole family of root choices, transports
naturally to every parameter over T. No independent natural selection is
assumed, and no model structure is needed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ParameterChoiceDiagram
variable (T K : SSet.{v})

abbrev target : (Over T)ᵒᵖ ⥤ SSet.{v} :=
  (Over.forget T).op ⋙ MonoidalClosed.internalHom.flip.obj K

def restriction : (Functor.const (Over T)ᵒᵖ).obj ((ihom T).obj K) ⟶ target T K where
  app σ := (pre σ.unop.hom).app K
  naturality {σ τ} φ := by
    change (𝟙 _) ≫ (pre τ.unop.hom).app K =
      (pre σ.unop.hom).app K ≫ (pre φ.unop.left).app K
    rw [Category.id_comp]
    have h : (pre σ.unop.hom).app K ≫ (pre φ.unop.left).app K =
        (pre (φ.unop.left ≫ σ.unop.hom)).app K :=
      RelativeChoiceSpace.restriction_comp φ.unop.left σ.unop.hom
    rw [h, Over.w φ.unop]

def parameterize {A : SSet.{v}} (a : A ⟶ (ihom T).obj K) :
    (Functor.const (Over T)ᵒᵖ).obj A ⟶ target T K :=
  (Functor.const (Over T)ᵒᵖ).map a ≫ restriction T K

variable {A B : SSet.{v}} (i : A ⟶ B) (b : A ⟶ (ihom T).obj K)

abbrev diagram : (Over T)ᵒᵖ ⥤ SSet.{v} :=
  RelativeChoiceFunctor.functor (target T K) i (parameterize T K b)

abbrev projection : diagram T K i b ⟶
    (Functor.const (Over T)ᵒᵖ).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0)) :=
  RelativeChoiceFunctor.projection (target T K) i (parameterize T K b)

def transport : (Functor.const (Over T)ᵒᵖ).obj (RelativeChoiceSpace.obj i b) ⟶ diagram T K i b where
  app σ := RelativeChoiceSpace.postMap i b ((parameterize T K b).app σ)
    ((restriction T K).app σ) rfl
  naturality {σ τ} φ := by
    change (𝟙 _) ≫ _ = _
    rw [Category.id_comp]
    dsimp only [diagram, RelativeChoiceFunctor.functor]
    apply pullback.hom_ext
    · simp only [Category.assoc, RelativeChoiceSpace.postMap_inclusion,
        RelativeChoiceSpace.postMap_inclusion_assoc]
      rw [← (ihom B).map_comp]
      have h : (restriction T K).app σ ≫ (target T K).map φ = (restriction T K).app τ :=
        ((restriction T K).naturality φ).symm.trans (Category.id_comp _)
      rw [h]
    · simp only [Category.assoc, RelativeChoiceSpace.postMap_projection]

variable {L : SSet.{v}} (c : L ⟶ RelativeChoiceSpace.obj i b)

def family : (Functor.const (Over T)ᵒᵖ).obj L ⟶ diagram T K i b :=
  (Functor.const (Over T)ᵒᵖ).map c ≫ transport T K i b

lemma family_evaluation (σ : (Over T)ᵒᵖ) :
    RelativeChoiceSpace.family i ((parameterize T K b).app σ) ((family T K i b c).app σ) =
      RelativeChoiceSpace.family i b c ≫ (restriction T K).app σ :=
  RelativeChoiceSpace.family_postMap i b ((parameterize T K b).app σ)
    ((restriction T K).app σ) rfl c

variable (a : B ⟶ (ihom T).obj K) (ha : i ≫ a = b)

def point : (Functor.const (Over T)ᵒᵖ).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ⟶
    diagram T K i b :=
  family T K i b (RelativeChoiceSpace.ofExtension i b a ha)

lemma point_app (σ : (Over T)ᵒᵖ) : (point T K i b a ha).app σ =
    RelativeChoiceSpace.ofExtension i ((parameterize T K b).app σ)
      (a ≫ (restriction T K).app σ) (by rw [← Category.assoc, ha]; rfl) :=
  RelativeChoiceSpace.postMap_ofExtension i b ((parameterize T K b).app σ)
    ((restriction T K).app σ) rfl a ha

lemma point_projection : point T K i b a ha ≫ projection T K i b = 𝟙 _ := by
  apply NatTrans.ext
  funext σ
  rw [NatTrans.comp_app, point_app]
  exact RelativeChoiceSpace.ofExtension_projection _ _ _ _

end SerrePositivity.SimplicialModel.ParameterChoiceDiagram
