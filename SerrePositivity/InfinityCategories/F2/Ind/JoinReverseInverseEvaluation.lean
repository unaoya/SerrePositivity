module

public import SerrePositivity.InfinityCategories.Stable.JoinReverse

/-!
概要：join の反転形状の逆射を元の明示的な切断反転の逆で計算する。
方針：元の順方向の全単射性と同型の逆射則を使う。
規約：全次数で同じ実際の射。使われ方：反転と宇宙持ち上げの全射の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 反転形状の逆射の各単体は、元の明示した切断反転同値の逆そのもの。 -/
lemma joinReverseIso_inv_app (K L : SSet.{u}) (n : ℕ)
    (s : (join L.op K.op) _⦋n⦌) :
    (stableJoinReverseIso K L).inv.app (Opposite.op ⦋n⦌) s =
      (stableAugJoinReverseEquiv K L (n + 1)).symm s := by
  apply (stableAugJoinReverseEquiv K L (n + 1)).injective
  rw [Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (stableJoinReverseIso K L).inv_hom_id (Opposite.op ⦋n⦌)) s

end SerrePositivity.InfinityCategories.F2.Ind
