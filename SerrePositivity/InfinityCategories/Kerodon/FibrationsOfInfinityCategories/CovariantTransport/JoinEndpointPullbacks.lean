module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinLeftBoundaryCorner
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinRightBoundaryCorner

/-!
概要：join の両因子の包含と joinMap の自然性は pullback をなす。
方針：左端・右端に対応する切断を保存することから因子への一意の復元を得る。
規約：因子の射の単射性や充填性を要求しない。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、Theorem 5.2.4.1（Tag 024N）、relative join の両端 fiber。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：join の左包含の自然性の正方形は pullback。
方針：切断が最大なら単体は左包含から来ることを使い、左の係数の像を比較する。
規約：左右の因子の射は任意。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、relative join の零端の fiber の表示。 -/
lemma isPullback_joinInl_naturality {A B K L : SSet.{u}} (f : A ⟶ B) (g : K ⟶ L) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K) f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B L) := by
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap f g
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨⟨n⟩⟩
  let d := Opposite.op ⦋n⦌
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨NatTrans.congr_app hw d, ?_, ?_⟩
  · intro a a' h
    exact congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h.1).2)
  · intro s b h
    have hc := congrArg (fun z ↦ z.1.val) h
    change s.1.val = n + 1 at hc
    obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinSimplex_exists_inl_of_cut s hc
    refine ⟨a, ha, ?_⟩
    apply (mono_iff_injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B L).app d)).mp inferInstance
    have hh := ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app hw d) a
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K).app d a) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B L).app d (f.app d a) at hh
    rw [ha] at hh
    exact hh.symm.trans h

/-- 概要：join の右包含の自然性の正方形は pullback。
方針：切断が零なら単体は右包含から来ることを使い、右の係数の像を比較する。
規約：左右の因子の射は任意。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、relative join の一端の fiber の表示。 -/
lemma isPullback_joinInr_naturality {A B K L : SSet.{u}} (f : A ⟶ B) (g : K ⟶ L) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K) g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B L) := by
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap f g
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨⟨n⟩⟩
  let d := Opposite.op ⦋n⦌
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨NatTrans.congr_app hw d, ?_, ?_⟩
  · intro a a' h
    exact congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h.1).2)
  · intro s b h
    have hc := congrArg (fun z ↦ z.1.val) h
    change s.1.val = 0 at hc
    obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinSimplex_exists_inr_of_cut s hc
    refine ⟨a, ha, ?_⟩
    apply (mono_iff_injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B L).app d)).mp inferInstance
    have hh := ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app hw d) a
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K).app d a) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B L).app d (g.app d a) at hh
    rw [ha] at hh
    exact hh.symm.trans h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
