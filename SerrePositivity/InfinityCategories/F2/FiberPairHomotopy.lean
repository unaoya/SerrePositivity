module

public import SerrePositivity.InfinityCategories.F2.PullbackHomotopy

/-!
概要：同じ底の二つの fiber 内のホモトピーを元の引き戻し内で組み合わせる。
方針：底への二つの円柱が同じ定値射になることを使う。
規約：元の fiber の二射を端点に取る。
使われ方：積比較で同時に検出した二つのホモトピーを引き戻しへ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：共通頂点の二つの fiber 内のホモトピーは、引き戻し内のホモトピーを与える。
方針：fiber の包含で後合成し、底への円柱が定値で一致することを使う。
規約：元の指定端点を保持する。使われ方：積比較の単射性。 -/
def fiberPairHomotopy {A E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    (b : B _⦋0⦌) {s₀ s₁ : A ⟶ vertexFiber p b} {t₀ t₁ : A ⟶ vertexFiber q b}
    (H : SSet.Homotopy s₀ s₁) (G : SSet.Homotopy t₀ t₁) :
    SSet.Homotopy (fiberPairToPullback p q b s₀ t₀)
      (fiberPairToPullback p q b s₁ t₁) where
  h := pullback.lift (H.h ≫ vertexFiberι p b) (G.h ≫ vertexFiberι q b) (by
    rw [Category.assoc, Category.assoc, vertexFiberι_comp, vertexFiberι_comp,
      SSet.comp_const, SSet.comp_const])
  h₀ := by
    change SSet.ι₀ ≫ _ = fiberPairToPullback p q b s₀ t₀
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, H.h₀]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, G.h₀]
      exact (pullback.lift_snd _ _ _).symm
  h₁ := by
    change SSet.ι₁ ≫ _ = fiberPairToPullback p q b s₁ t₁
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, H.h₁]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, G.h₁]
      exact (pullback.lift_snd _ _ _).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.F2
