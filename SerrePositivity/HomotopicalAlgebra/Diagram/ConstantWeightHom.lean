module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightRealization
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! # Maps out of a constant representable weight

Maps of K-opposite diagrams from a constant standard simplex to the
pointwise cosimplicial Hom are precisely cocones from the corresponding
degree of the frame family. This is an actual equivalence of natural
transformations, without model or enrichment assumptions.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits ConcreteCategory
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.ConstantWeightHom
abbrev degree (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
    (A : K ⥤ SimplexCategory ⥤ C) (n : SimplexCategory) : K ⥤ C :=
  A ⋙ (CategoryTheory.evaluation SimplexCategory C).obj n

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  (A : K ⥤ SimplexCategory ⥤ C) (n : SimplexCategory) (Y : C)

abbrev weight : Kᵒᵖ ⥤ SSet.{w} := (Functor.const Kᵒᵖ).obj (SSet.stdSimplex.{w}.obj n)

/-- Componentwise simplicial Yoneda, including the compatibility in K. -/
def homEquiv :
    (weight K n ⟶ (FrameWeightRealization.hom K A).obj Y) ≃
      (degree K A n ⟶ (Functor.const K).obj Y) where
  toFun a := {
    app k := SSet.yonedaEquiv (a.app (Opposite.op k))
    naturality k l f := by
      let x : (SSet.stdSimplex.{w}.obj n).obj (Opposite.op n) :=
        SSet.stdSimplex.objEquiv.symm (𝟙 n)
      have h := types_congr_hom (congr_app (a.naturality f.op) (Opposite.op n)) x
      have he : SSet.yonedaEquiv (a.app (Opposite.op k)) =
          (A.map f).app n ≫ SSet.yonedaEquiv (a.app (Opposite.op l)) := h
      exact he.symm.trans (Category.comp_id _).symm }
  invFun b := {
    app k := SSet.yonedaEquiv.symm (b.app k.unop)
    naturality k l f := by
      change 𝟙 _ ≫ SSet.yonedaEquiv.symm (b.app l.unop) =
        SSet.yonedaEquiv.symm (b.app k.unop) ≫ ((FrameWeightRealization.hom K A).obj Y).map f
      have he := SSet.yonedaEquiv_symm_comp
        (X := ((FrameWeightRealization.hom K A).obj Y).obj k)
        (Y := ((FrameWeightRealization.hom K A).obj Y).obj l)
        (n := n) (b.app k.unop) (((FrameWeightRealization.hom K A).obj Y).map f)
      have hb : b.app l.unop = (A.map f.unop).app n ≫ b.app k.unop :=
        ((b.naturality f.unop).trans (Category.comp_id _)).symm
      have hc := congrArg (fun t : (A.obj l.unop).obj n ⟶ Y =>
        (SSet.yonedaEquiv (X := ((FrameWeightRealization.hom K A).obj Y).obj l) (n := n)).symm t) hb
      exact (Category.id_comp _).trans (hc.trans he.symm) }
  left_inv a := by
    apply NatTrans.ext
    funext k
    exact SSet.yonedaEquiv.symm_apply_apply (a.app k)
  right_inv b := by
    apply NatTrans.ext
    funext k
    exact (SSet.yonedaEquiv
      (X := ((FrameWeightRealization.hom K A).obj Y).obj (Opposite.op k))
      (n := n)).apply_symm_apply (b.app k)

variable {Y}

@[reassoc]
lemma homEquiv_target_naturality {Z : C} (f : Y ⟶ Z)
    (a : weight K n ⟶ (FrameWeightRealization.hom K A).obj Y) :
    homEquiv K A n Z (a ≫ (FrameWeightRealization.hom K A).map f) =
      homEquiv K A n Y a ≫ (Functor.const K).map f := by
  apply NatTrans.ext
  funext k
  rfl

end SerrePositivity.DiagramModel.ConstantWeightHom
