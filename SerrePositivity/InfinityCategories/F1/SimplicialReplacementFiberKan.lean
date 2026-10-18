module

public import SerrePositivity.InfinityCategories.F1.SimplicialReplacementFiber

/-!
概要：simplicial replacement の頂点 fiber の Kan 性。
方針：係数値との厳密な同型でホーンを移し、充填を戻す。
規約：全空間の充填性を仮定せず、指定した係数値の Kan 性だけを使う。
使われ方：Kerodon Proposition 5.3.4.8、scaffold の fiber 同値の始域。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：Kan な係数値に対応する simplicial replacement の fiber は Kan 複体。
方針：標準 fiber 比較の逆でホーンを係数値へ写して充填し、標準比較で戻す。
規約：底の圏と他の係数値には追加仮定を要求しない。
使われ方：Kerodon Proposition 5.3.4.8、fiber 上の圏同値の構成。 -/
instance simplicialReplacementFiber_kanComplex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) [KanComplex (F.obj c)] :
    KanComplex (vertexFiber (simplicialReplacementProjection F) (nerveVertex c)) := by
  let e := asIso (simplicialReplacementFiberMap F c)
  apply kanComplex_of_rightHornFillers
  intro n i _ a
  obtain ⟨H, hH⟩ := KanComplex.hornFilling (a ≫ e.inv)
  refine ⟨H ≫ e.hom, ?_⟩
  rw [← Category.assoc, ← hH, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories
