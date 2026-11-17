module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConstantComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RealizationHomNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom

/-!
# 実現の一点比較と元の frame augmentation の照合

概要：Hovey §5 の一点への実現比較は同じ augmentation の全単体を回収する。
方針：実際の随伴の単体の式、零単体の終対象性、Kan 拡張単位の自然性を使う。
規約：元の零次同型と augmentation を選び直さない。
使われ方：通常の錐の始域 frame の族の正規化。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{0, u} C]
  (B : SimplexCategory ⥤ C) {Y : C}

/-- 概要：一点比較の実現随伴像は同じ augmentation の指定成分（Hovey §5）。
方針：零単体へのすべての射の一致と実現単位の自然性を使う。
規約：任意の単体集合と全次元・全単体を含む。
使われ方：元の定値図式比較から作った錐の族の計算。 -/
lemma realizationAugmentation_homEquiv (a : B ⟶ (Functor.const SimplexCategory).obj Y)
    (X : SSet.{u}) (t : X ⟶ ⊤_ SSet.{u}) (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    (((Realization.adjunction B).homEquiv X Y
      ((Realization.functor B).map t ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realizationPointIso B).hom ≫
        a.app (SimplexCategory.mk 0))).app n) x = a.app n.unop := by
  let c := QuillenStandardFrame.collapse n.unop
  let e := (Realization.representableIso B).app (SimplexCategory.mk 0)
  have hc : uliftYonedaEquiv.symm x ≫ t ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.liftedZeroPointIso.inv = uliftYoneda.map c :=
    (SimplexCategory.isTerminalZero.isTerminalObj uliftYoneda.{u, 0, 0} _).hom_ext _ _
  have hm : (Realization.functor B).map (uliftYonedaEquiv.symm x) ≫
        (Realization.functor B).map t ≫ (Realization.functor B).map _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.liftedZeroPointIso.inv =
      (Realization.functor B).map (uliftYoneda.map c) := by
    rw [← (Realization.functor B).map_comp, ← (Realization.functor B).map_comp, hc]
  have hu : B.map c ≫ e.hom =
      (Realization.unit B).app n.unop ≫ (Realization.functor B).map (uliftYoneda.map c) :=
    (Realization.unit B).naturality c
  have he : (Realization.unit B).app n.unop ≫
        (Realization.functor B).map (uliftYoneda.map c) ≫ e.inv = B.map c := by
    rw [← Category.assoc, ← hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ha : B.map c ≫ a.app (SimplexCategory.mk 0) = a.app n.unop := by
    have h := a.naturality c
    change B.map c ≫ a.app (SimplexCategory.mk 0) = a.app n.unop ≫ 𝟙 Y at h
    exact h.trans (Category.comp_id _)
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.realizationHomEquiv_app]
  change (Realization.unit B).app n.unop ≫
    (Realization.functor B).map (uliftYonedaEquiv.symm x) ≫
      (Realization.functor B).map t ≫ ((Realization.functor B).map _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.liftedZeroPointIso.inv ≫
        e.inv) ≫ a.app (SimplexCategory.mk 0) = _
  calc
    _ = ((Realization.unit B).app n.unop ≫
        ((Realization.functor B).map (uliftYonedaEquiv.symm x) ≫
          (Realization.functor B).map t ≫
            (Realization.functor B).map _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.liftedZeroPointIso.inv) ≫ e.inv) ≫
              a.app (SimplexCategory.mk 0) := by simp only [Category.assoc]
    _ = _ := by rw [hm, he, ha]

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
