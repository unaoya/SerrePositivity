module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomLifting

/-!
概要：相対指数の inner fibration 性を、内ホーンの逆像上の図式の延長で判定する。
方針：射影の持ち上げ問題と逆像の図式の延長の同値を内ホーンに適用する。
規約：cocartesian fibration に沿う逆像の同値性自体はここでは仮定として明示する。
使われ方：Kerodon §5.3.6（Tag 037W） の相対指数の inner fibration 性の幾何学的な入力を特定する。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：相対指数の inner fibration 性は全内ホーンの逆像上の図式の延長と同値。
方針：各ホーンの可換正方形を curry で往復する。
規約：K・C・D の quasicategory 性は不要。
使われ方：相対指数の充填性を逆像の射の性質へ移す。 -/
lemma fiberwiseHomProjection_innerFibration_iff {K C D : SSet.{u}} (p : K ⟶ C) :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) ↔
      ∀ (n : ℕ) (k : Fin (n + 3)), 0 < k → k < Fin.last (n + 2) →
        ∀ (b : (Δ[n + 2] : SSet.{u}) ⟶ C)
          (H₀ : pullback ((horn (n + 2) k).ι ≫ b) p ⟶ D),
        ∃ H : pullback b p ⟶ D,
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
            (Over.homMk (horn (n + 2) k).ι rfl :
              Over.mk ((horn (n + 2) k).ι ≫ b) ⟶ Over.mk b) ≫ H = H₀ := by
  constructor
  · intro hp n k h0 hn b H₀
    have := hp.mem _ (innerHornInclusions.intro k h0 hn)
    let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p ((horn (n + 2) k).ι ≫ b) H₀
    have sq : CommSq a (horn (n + 2) k).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) b :=
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry_projection p _ H₀⟩
    obtain ⟨f, hfi⟩ :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHom_hasLift_iff p sq).1 (inferInstance : sq.HasLift)
    refine ⟨f, hfi.trans ?_⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) p _).symm_apply_apply H₀
  · intro h
    constructor
    intro A B i hi
    obtain @⟨n, k, h0, hn⟩ := hi
    constructor
    intro a b sq
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHom_hasLift_iff p sq).2 (h n k h0 hn b _)

/-- 概要：内ホーンの逆像が前合成同値なら相対指数の射影は inner fibration。
方針：逆像の単射性で本質的全射性を厳密な図式の延長へ強める。
規約：逆像の同値性は明示的な仮定で、cocartesian fibration 性からの証明は別工程。
使われ方：Kerodon Lemma 5.3.6.6（Tag 02RK） を相対指数の inner fibration 性へ渡す。 -/
lemma fiberwiseHomProjection_innerFibration_of_hornEquivalences
    {K C D : SSet.{u}} (p : K ⟶ C) [Quasicategory D]
    (hp : ∀ (n : ℕ) (k : Fin (n + 3)), 0 < k → k < Fin.last (n + 2) →
      ∀ b : (Δ[n + 2] : SSet.{u}) ⟶ C,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
          (Over.homMk (horn (n + 2) k).ι rfl :
            Over.mk ((horn (n + 2) k).ι ≫ b) ⟶ Over.mk b))) :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) := by
  apply (fiberwiseHomProjection_innerFibration_iff p).2
  intro n k h0 hn b H₀
  let j : Over.mk ((horn (n + 2) k).ι ≫ b) ⟶ Over.mk b :=
    Over.homMk (horn (n + 2) k).ι rfl
  have : Mono j := by
    apply (Over.forget C).mono_of_mono_map
    change Mono (horn (n + 2) k).ι
    infer_instance
  let m := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map j
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence m := hp n k h0 hn b
  obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pre_surjective_of_essentiallySurjective m
    (hm D).choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H₀)
  obtain ⟨H, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).surjective v
  refine ⟨H, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ D).injective ?_⟩
  exact hv

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
