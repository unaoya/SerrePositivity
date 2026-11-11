module
public import SerrePositivity.KST.Fibration.PrismLocalizedEquality
public import SerrePositivity.KST.Fibration.GroupoidCompletionKanMaps
public import SerrePositivity.KST.LocalizingInvariants.IntervalPullbackFiberInclusions

/-! # 両側 fibration の区間内で、実評価 prism によって同じ射の可逆性を検出する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 始点評価が局所化同型なら、同じ両側区間 prism の終点評価も局所化同型。 -/
theorem intervalPrism_target_localized_isIso {P E B : SSet.{u}}
    (p : E ⟶ B) (b : (Δ[1] : SSet.{u}) ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (pullback.snd p b)] [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.snd p b)]
    (f : P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p
      (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (g : P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p
      (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (H : (Δ[1] : SSet.{u}) ⊗ P ⟶ E)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P ≫ H = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 P ≫ H = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p _)
    (hb : H ≫ p = fst (Δ[1] : SSet.{u}) P ≫ b)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IsIso (AnodyneHomotopy.anodyneQ.map g) := by
  let J := pullback.lift H (fst (Δ[1] : SSet.{u}) P) hb
  have hJ₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P ≫ J = f ≫ intervalPullbackFiberInclusion p b 0 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, J, pullback.lift_fst, intervalPullbackFiberInclusion_fst]
      exact h₀
    · simp only [Category.assoc, J, pullback.lift_snd, intervalPullbackFiberInclusion_snd,
        SSet.comp_const]
      rfl
  have hJ₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 P ≫ J = g ≫ intervalPullbackFiberInclusion p b 1 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, J, pullback.lift_fst, intervalPullbackFiberInclusion_fst]
      exact h₁
    · simp only [Category.assoc, J, pullback.lift_snd, intervalPullbackFiberInclusion_snd,
        SSet.comp_const]
      rfl
  have h₀ := (groupoidCompletionMapOf_anodyneQ_isIso_iff _).mp
    (intervalPullbackFiberInclusion_zero_groupoidCompletion_isEquivalence p b).anodyneQ_isIso
  have h₁ := (groupoidCompletionMapOf_anodyneQ_isIso_iff _).mp
    (intervalPullbackFiberInclusion_one_groupoidCompletion_isEquivalence p b).anodyneQ_isIso
  have he := prism_localized_eq _ _ J hJ₀ hJ₁
  have hg : IsIso (AnodyneHomotopy.anodyneQ.map g ≫
      AnodyneHomotopy.anodyneQ.map (intervalPullbackFiberInclusion p b 1)) := by
    rw [← Functor.map_comp, ← he, Functor.map_comp]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hg

end SerrePositivity.KST.Fibration
