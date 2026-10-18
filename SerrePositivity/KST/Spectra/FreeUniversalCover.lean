module

public import SerrePositivity.KST.Spectra.FreeCochainWeight

/-!
概要：EG の斉次座標を各次数で非斉次座標の自由 G 軌道へ移した単体的図式。
方針：隣り合う座標の比による同型で顔・退化を共役する。
規約：各次数は G×(Fin n → G)、第二因子への作用は自明。
使われ方：Goerss–Jardine VIII §2。群 cochain の非斉次座標の図式を厳密に保持する。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.GroupActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：EG の非斉次座標の単体的な自由作用の図式。
方針：標準 EG の顔・退化を各次数の自由軌道の同型で共役する。
規約：各単体次数の関手法則は同型の両逆から従う。
使われ方：Goerss–Jardine VIII §2。非斉次群 cochain の重みの図式。 -/
def freeUniversalCover (G : Type u) [Group G] : SimplicialObject (Action (Type u) G) where
  obj n := Action.leftRegular G ⊗ Action.trivial G (Fin n.unop.len → G)
  map {n m} f :=
    (Action.diagonalSuccIsoTensorTrivial G n.unop.len).inv ≫
      (classifyingSpaceUniversalCover G).map f ≫
        (Action.diagonalSuccIsoTensorTrivial G m.unop.len).hom
  map_id n := by
    rw [CategoryTheory.Functor.map_id]
    change (Action.diagonalSuccIsoTensorTrivial G n.unop.len).inv ≫
        𝟙 (Action.diagonal G (n.unop.len + 1)) ≫
          (Action.diagonalSuccIsoTensorTrivial G n.unop.len).hom = 𝟙 _
    rw [Category.id_comp, Iso.inv_hom_id]
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- 概要：標準 EG と自由軌道の非斉次座標の図式の自然同型。
方針：各次数の連続する座標の比の同型を束ねる。
規約：単体的 G 集合の実際の自然同型。
使われ方：Goerss–Jardine VIII §2。cochain の顔・退化の座標式を移す比較。 -/
def universalCoverFreeNatIso (G : Type u) [Group G] :
    classifyingSpaceUniversalCover G ≅ freeUniversalCover G :=
  NatIso.ofComponents (fun n ↦ Action.diagonalSuccIsoTensorTrivial G n.unop.len)
    (fun f ↦ by
      change (classifyingSpaceUniversalCover G).map f ≫ _ = _ ≫ (_ ≫ _ ≫ _)
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp])

end

end SerrePositivity.KST.Spectra.GroupActionCochains
