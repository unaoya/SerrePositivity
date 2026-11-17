module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowEdgeComposition

/-!
概要：元の実射の twisted-arrow 頂点と nerve の同じ辺の合成の照合。
方針：同じ重みの逆と同じ合成三角形の像を計算する。
規約：始域と標的と元の実射を保ち、標的に模型構造を仮定しない。
使われ方：元の単位ラベルの original pairing の像の同じ二射の合成への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 元の実射の同じ twisted-arrow 頂点を辺へ戻すと、同じ実射の nerve の辺の像になる。 -/
lemma twistedArrowVertexEdge_nerve_arrow {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (F : nerve C ⟶ E) {x y : C} (g : x ⟶ y) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      ((edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm (ComposableArrows.mk₁ g) ≫ F))) =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk g).map F)) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change SSet.yonedaEquiv ((edgewiseWeightIso 0).inv ≫
      ((edgewiseWeightIso 0).hom ≫ SSet.yonedaEquiv.symm (ComposableArrows.mk₁ g) ≫ F)) =
    F.app _ (nerve.edgeMk g).edge
  rw [Iso.inv_hom_id_assoc, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 元の同じ二射の合成の辺の像の類は、同じ二つの辺の像の類の合成になる。 -/
lemma mappedNerveEdgeHom_comp {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (F : nerve C ⟶ E) {x y z : C} (g : x ⟶ y) (h : y ⟶ z) :
    HomotopyCategory.homMk ((nerve.edgeMk (g ≫ h)).map F) =
      HomotopyCategory.homMk ((nerve.edgeMk g).map F) ≫
        HomotopyCategory.homMk ((nerve.edgeMk h).map F) := by
  obtain ⟨t⟩ := (nerve.nonempty_compStruct_iff g h (g ≫ h)).2 rfl
  exact (HomotopyCategory.homMk_comp_homMk (t.map F)).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end
