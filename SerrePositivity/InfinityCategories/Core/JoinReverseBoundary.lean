module
public import SerrePositivity.InfinityCategories.Core.JoinReverseFactors
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorMiddle

/-! # join の反転と左右の包含

概要：join の反転は左右の因子の包含を交換する。
方針：切断零と全区間の補数を計算し、空因子の一点性を使う。
規約：単体的な射の厳密な等式。使われ方：S4 の slice／coslice の固定条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：反転した左包含は右包含になる。
方針：各次数で全区間の切断を零へ移し、反転した二因子を比較する。
規約：始域は K.op。使われ方：余錐と錐の固定条件の双対化。 -/
lemma stableJoinReverse_inl (K L : SSet.{u}) :
    SSet.opFunctor.map (joinInl K L) ≫ (stableJoinReverseIso K L).hom =
      joinInr L.op K.op := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  let t := stableAugJoinInl K L (n + 1) (SSet.opObjEquiv x)
  change stableAugJoinReversePairEquiv K L (n + 1) t = stableAugJoinInr L.op K.op (n + 1) x
  refine stableAugJoin_hext _ _ (Nat.sub_self _) ?_ ?_
  · exact stableAugEmpty_heq L.op (Nat.sub_self (n + 1)) _
  · apply stableAugOpEquiv_heq K (by omega : n + 1 - (n + 1 - (n + 1)) = n + 1)
    exact (heq_of_eq (stableAugJoinReversePair_right K L (n + 1) t)).trans (cast_heq _ _)

/-- 概要：反転した右包含は左包含になる。
方針：各次数で零の切断を全区間へ移す。
規約：始域は L.op。使われ方：余錐と錐の射影の双対化。 -/
lemma stableJoinReverse_inr (K L : SSet.{u}) :
    SSet.opFunctor.map (joinInr K L) ≫ (stableJoinReverseIso K L).hom =
      joinInl L.op K.op := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  let t := stableAugJoinInr K L (n + 1) (SSet.opObjEquiv x)
  change stableAugJoinReversePairEquiv K L (n + 1) t = stableAugJoinInl L.op K.op (n + 1) x
  refine stableAugJoin_hext _ _ rfl ?_ ?_
  · apply stableAugOpEquiv_heq L (r := n + 1) (r' := n + 1) rfl
    exact heq_of_eq (stableAugJoinReversePair_left K L (n + 1) t)
  · exact (stableAugEmpty_heq K.op (Nat.sub_self (n + 1)) _).trans
      (stableAugEmpty_heq K.op (Nat.sub_self (n + 1)) _).symm

/-- 概要：右包含の後で join の逆反転を取ると元の左包含の op になる。
方針：左包含の式に逆同型を合成する。
規約：射の等式。使われ方：slice の反転の固定条件。 -/
lemma stableJoinReverse_inr_inv (K L : SSet.{u}) :
    joinInr L.op K.op ≫ (stableJoinReverseIso K L).inv = SSet.opFunctor.map (joinInl K L) := by
  rw [← stableJoinReverse_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：左包含の後で join の逆反転を取ると元の右包含の op になる。
方針：右包含の式に逆同型を合成する。
規約：射の等式。使われ方：coslice の反転の固定条件。 -/
lemma stableJoinReverse_inl_inv (K L : SSet.{u}) :
    joinInl L.op K.op ≫ (stableJoinReverseIso K L).inv = SSet.opFunctor.map (joinInr K L) := by
  rw [← stableJoinReverse_inr, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories
