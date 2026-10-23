module

public import SerrePositivity.InfinityCategories.Core.Join
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：固定した右因子との通常の join による pullback の保存。
方針：各次数で切断と右成分を一致させ、補った左単体の pullback を使う。
規約：空の左区間では一点の pullback とする。
使われ方：Kerodon Proposition 5.2.4.5、relative join の右錐の比較の全射性への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：単体集合の pullback は空区間を補った単体の型でも pullback。
方針：空区間では一点性、非空区間では各次数の pullback を使う。
規約：r は頂点数。
使われ方：Kerodon Proposition 5.2.4.5、右錐の pullback の次数ごとの計算。 -/
lemma join_augHom_isPullback {P A B C : SSet.{u}}
    {a : P ⟶ A} {b : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback a b f g) (r : ℕ) :
    IsPullback (↾(Join.augHom a r)) (↾(Join.augHom b r))
      (↾(Join.augHom f r)) (↾(Join.augHom g r)) := by
  cases r with
  | zero =>
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨rfl, ?_, ?_⟩
    · intro x y _
      exact @Subsingleton.elim PUnit inferInstance x y
    · intro x y _
      exact ⟨PUnit.unit, @Subsingleton.elim PUnit inferInstance _ _,
        @Subsingleton.elim PUnit inferInstance _ _⟩
  | succ r => exact h.app (Opposite.op (SimplexCategory.mk r))

/-- 概要：右因子を固定した通常の join は pullback の正方形を保つ。
方針：像の切断と右成分の一致を取り出し、左の pullback の持ち上げを同じ切断に戻す。
規約：右因子 K は任意。モデル構造や quasicategory 性は要求しない。
使われ方：Kerodon Proposition 5.2.4.5、relative join の定義の右錐への延長。 -/
lemma join_left_isPullback {P A B C : SSet.{u}}
    {a : P ⟶ A} {b : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback a b f g) (K : SSet.{u}) :
    IsPullback (joinMap a (𝟙 K)) (joinMap b (𝟙 K))
      (joinMap f (𝟙 K)) (joinMap g (𝟙 K)) := by
  have hw : joinMap a (𝟙 K) ≫ joinMap f (𝟙 K) =
      joinMap b (𝟙 K) ≫ joinMap g (𝟙 K) := by
    rw [← joinMap_comp, ← joinMap_comp, h.w]
  apply IsPullback.of_forall_isPullback_app
  intro n
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨congrArg (fun k : join P K ⟶ join C K ↦ k.app n) hw, ?_, ?_⟩
  · rintro ⟨c, p, k⟩ ⟨c', p', k'⟩ ⟨h₁, h₂⟩
    have hc : c = c' := congrArg Sigma.fst h₁
    subst c'
    have hl₁ := congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h₁).2)
    have hl₂ := congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h₂).2)
    have hp : p = p' := Types.ext_of_isPullback (join_augHom_isPullback h c.val) hl₁ hl₂
    have hr := congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h₁).2)
    have hk : k = k' := by simpa only [Join.augHom_id] using hr
    exact congrArg (Sigma.mk c) (Prod.ext hp hk)
  · rintro ⟨c, x, k⟩ ⟨c', y, k'⟩ he
    have hc : c = c' := congrArg Sigma.fst he
    subst c'
    have hl := congrArg Prod.fst (eq_of_heq (Sigma.mk.inj he).2)
    have hr := congrArg Prod.snd (eq_of_heq (Sigma.mk.inj he).2)
    have hk : k = k' := by simpa only [Join.augHom_id] using hr
    obtain ⟨p, hp₁, hp₂⟩ := Types.exists_of_isPullback (join_augHom_isPullback h c.val) x y hl
    refine ⟨⟨c, p, k⟩, ?_, ?_⟩
    · refine Join.Simplex.ext _ _ (by rfl) ?_ ?_
      · exact hp₁
      · exact Join.augHom_id K _ k
    · refine Join.Simplex.ext _ _ (by rfl) ?_ ?_
      · exact hp₂
      · exact (Join.augHom_id K _ k).trans hk

end SerrePositivity.InfinityCategories
