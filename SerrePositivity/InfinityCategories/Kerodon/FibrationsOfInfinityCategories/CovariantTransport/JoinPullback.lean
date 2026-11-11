module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinLeftPullback

/-!
概要：通常の join の両因子に関する pullback の保存。
方針：各次数で切断を一致させ、前半と後半の補った単体の pullback を独立に使う。
規約：いずれの因子にも単射性を要求しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join と任意の底変換の交換。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：二つの pullback の正方形の join は pullback。
方針：像の切断の一致を取り出し、両成分の持ち上げと一意性を同じ切断で組み合わせる。
規約：空区間でも補った単体の pullback を使う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、構造射の pullback と relative join の定義の貼り合わせ。 -/
lemma join_isPullback {P A B C Q D E F : SSet.{u}}
    {a : P ⟶ A} {b : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    {c : Q ⟶ D} {d : Q ⟶ E} {h : D ⟶ F} {k : E ⟶ F}
    (hP : IsPullback a b f g) (hQ : IsPullback c d h k) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap a c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap b d) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f h) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g k) := by
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap a c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f h = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap b d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g k := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, hP.w, hQ.w]
  apply IsPullback.of_forall_isPullback_app
  intro n
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨congrArg (fun m : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join P Q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join C F ↦ m.app n) hw, ?_, ?_⟩
  · rintro ⟨s, x, y⟩ ⟨s', x', y'⟩ ⟨h₁, h₂⟩
    have hs : s = s' := congrArg Sigma.fst h₁
    subst s'
    have hl₁ := congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h₁).2)
    have hl₂ := congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h₂).2)
    have hr₁ := congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h₁).2)
    have hr₂ := congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h₂).2)
    have hx : x = x' := Types.ext_of_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_augHom_isPullback hP s.val) hl₁ hl₂
    have hy : y = y' := Types.ext_of_isPullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_augHom_isPullback hQ (n.unop.len + 1 - s.val)) hr₁ hr₂
    exact congrArg (Sigma.mk s) (Prod.ext hx hy)
  · rintro ⟨s, x, y⟩ ⟨s', z, w⟩ he
    have hs : s = s' := congrArg Sigma.fst he
    subst s'
    have hl := congrArg Prod.fst (eq_of_heq (Sigma.mk.inj he).2)
    have hr := congrArg Prod.snd (eq_of_heq (Sigma.mk.inj he).2)
    obtain ⟨p, hp₁, hp₂⟩ := Types.exists_of_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_augHom_isPullback hP s.val) x z hl
    obtain ⟨q, hq₁, hq₂⟩ := Types.exists_of_isPullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.join_augHom_isPullback hQ (n.unop.len + 1 - s.val)) y w hr
    refine ⟨⟨s, p, q⟩, ?_, ?_⟩
    · refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (by rfl) ?_ ?_
      · exact hp₁
      · exact hq₁
    · refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ (by rfl) ?_ ?_
      · exact hp₂
      · exact hq₂

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
