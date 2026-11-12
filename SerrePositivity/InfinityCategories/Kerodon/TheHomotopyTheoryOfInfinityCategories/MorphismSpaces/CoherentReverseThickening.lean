module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentEnrichedOpposite

/-!
概要：有限順序の反転による simplicial thickening の反対への豊穣関手。
方針：頂点を rev で順序双対へ移し、path の双対によって反対の thickening にする。
規約：単体の添字の反転も同時に明示する。
使われ方：Kerodon §4.6.7（Tag 01LA） の coherent nerve の反対と左右の Hom の係数比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：持ち上げた有限順序の頂点の反転は順序双対への単調写像。
方針：Fin.rev の反単調性を順序双対の単調性として使う。
規約：coherent nerve の定義と同じ ULift の宇宙を使う。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent simplex の頂点の反転。 -/
def coherentReverseOrder (n : ℕ) :
    ULift.{u} (Fin (n + 1)) →o (ULift.{u} (Fin (n + 1)))ᵒᵈ where
  toFun i := OrderDual.toDual (ULift.up i.down.rev)
  monotone' i j h := by
    change j.down.rev ≤ i.down.rev
    exact Fin.rev_le_rev.mpr h

/-- 概要：有限順序の反転は単体の添字写像の反転と可換。
方針：各頂点で rev の定義と二回の反転の恒等性を計算する。
規約：反転後の添字写像は SimplexCategory.rev.map を使う。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent simplex の自然性。 -/
lemma coherentReverseOrder_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (coherentReverseOrder n).comp α.toOrderHom.uliftMap =
      ((SimplexCategory.rev.map α).toOrderHom.uliftMap).dual.comp (coherentReverseOrder m) := by
  apply DFunLike.ext
  intro i
  apply ULift.ext
  change (α.toOrderHom i.down).rev =
    (SimplexCategory.rev.map α).toOrderHom i.down.rev
  rw [SimplexCategory.rev_map_apply, Fin.rev_rev]
  rfl

/-- 概要：標準の thickening は頂点反転により自分の反対へ豊穣関手を持つ。
方針：反転の単調写像による関手と、順序双対の path の反転を合成する。
規約：対象の像は反転した頂点の反対。
使われ方：Kerodon §4.6.7（Tag 01LA） の coherent nerve の反対の単体の構成。 -/
def coherentReverseThickening (n : ℕ) :
    EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n + 1))))
      (SimplicialThickening (ULift.{u} (Fin (n + 1))))ᵒᵖ :=
  (SimplicialThickening.functor (coherentReverseOrder n)).comp SSet
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentThickeningDual (ULift.{u} (Fin (n + 1)))ᵒᵈ)

/-- 概要：thickening の反対への頂点反転は、添字写像を反転した前合成と可換。
方針：順序写像の可換性、thickening の関手性、順序双対の自然性を合成する。
規約：全ての面と退化を一つの式で扱う。
使われ方：Kerodon §4.6.7（Tag 01LA） の coherent nerve の反対の単体的自然性。 -/
lemma coherentReverseThickening_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet
      (coherentReverseThickening n) =
      (coherentReverseThickening m).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctorOp
          (SimplicialThickening.functor (SimplexCategory.rev.map α).toOrderHom.uliftMap)) := by
  unfold coherentReverseThickening
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc, ← SimplicialThickening.functor_comp,
    coherentReverseOrder_naturality, SimplicialThickening.functor_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentThickeningDual_naturality,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentEnrichedFunctor_comp_assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
