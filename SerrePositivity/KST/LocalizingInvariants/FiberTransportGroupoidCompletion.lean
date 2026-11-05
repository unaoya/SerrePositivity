module

public import SerrePositivity.KST.LocalizingInvariants.IntervalPullbackFiberInclusions

/-!
概要：区間上の引き戻しが両側 fibration なら、元の射影の実輸送は亜群化後に同値。
方針：与えた prism を同じ底区間と組にして引き戻しへ移し、両包含の同値で消去する。
規約：元の輸送関手と prism を変更しない。使われ方：分母上の元の cocartesian 輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma fiberTransport_groupoidCompletion_isEquivalence {E B : SSet.{u}}
    (p : E ⟶ B) (b : (Δ[1] : SSet.{u}) ⟶ B)
    [CartesianFibration (pullback.snd p b)] [CocartesianFibration (pullback.snd p b)]
    (f : vertexFiber p (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ⟶
      vertexFiber p (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (H : (Δ[1] : SSet.{u}) ⊗
      vertexFiber p (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H =
      vertexFiberι p (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h₁ : prismEndpoint 1 _ ≫ H = f ≫
      vertexFiberι p (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hb : H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ b) :
    IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMapOf f) := by
  let J := pullback.lift H (fst (Δ[1] : SSet.{u}) _) hb
  have hJ₀ : prismEndpoint 0 _ ≫ J = intervalPullbackFiberInclusion p b 0 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, J, pullback.lift_fst, intervalPullbackFiberInclusion_fst]
      exact h₀
    · simp only [Category.assoc, J, pullback.lift_snd, intervalPullbackFiberInclusion_snd]
      rfl
  have hJ₁ : prismEndpoint 1 _ ≫ J = f ≫ intervalPullbackFiberInclusion p b 1 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, J, pullback.lift_fst, intervalPullbackFiberInclusion_fst]
      exact h₁
    · simp only [Category.assoc, J, pullback.lift_snd, intervalPullbackFiberInclusion_snd,
        SSet.comp_const]
      rfl
  exact _root_.SerrePositivity.InfinityCategories.Derived.Localization.prismComparison_groupoidCompletion_isEquivalence _ _ f J hJ₀ hJ₁
    (intervalPullbackFiberInclusion_zero_groupoidCompletion_isEquivalence p b)
    (intervalPullbackFiberInclusion_one_groupoidCompletion_isEquivalence p b)

end SerrePositivity.KST.LocalizingInvariants
