module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLocalOppositeExistence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonicalExistence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.OppositeLifting

/-!
概要：標準局所相対極限から元と底を厳密に保つ相対右 Kan 延長を構成する。
方針：局所相対極限を左の局所余極限へ反転し、左の厳密な存在定理を双対化する。
規約：δ は充満忠実な inner 単射、U は同値を持ち上げる。
使われ方：元の相対右 Kan 制限の頂点全射性。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：反転後の標準局所相対極限から反転後の厳密な右 Kan 延長が存在する。
方針：左の標準底余錐上の局所存在を回収して組み立て、元と底の等式を反転する。
規約：反転前の元と底の図式を入力する。
使われ方：二重反転を消す前の右の相対存在定理。 -/
lemma exists_kanRelativeRightCanonical_op_strict_extension_of_local_relative_limits
    {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (F₀ : K ⟶ D) (H₀ : C ⟶ E) (hFU : F₀ ≫ U = δ ≫ H₀)
    (hlocal : ∀ c : C.op _⦋0⦌,
      ∃ z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀) c),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone (SSet.opFunctor.map U) z ∧ z.val ≫ SSet.opFunctor.map U =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map H₀) c).val) :
    ∃ G : C.op ⟶ D.op, SSet.opFunctor.map δ ≫ G = SSet.opFunctor.map F₀ ∧
      G ≫ SSet.opFunctor.map U = SSet.opFunctor.map H₀ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom (SSet.opFunctor.map U) (SSet.opFunctor.map δ) G := by
  have hl : ∀ c : C _⦋0⦌, ∃ z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U z ∧ z.val ≫ U = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ H₀ c).val := by
    intro c
    obtain ⟨z, hz, hzu⟩ := hlocal (SSet.opObjEquiv.symm c)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftLocalColimit_of_op_rightLimit U δ F₀ H₀ hFU c z hz hzu
  obtain ⟨G, hGδ, hGU, hG⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits
      U hU δ hδ F₀ H₀ hFU hl
  refine ⟨SSet.opFunctor.map G, ?_, ?_,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeLeftKanExtendedFrom_iff_op_right U δ G).1 hG⟩
  · rw [← Functor.map_comp, hGδ]
  · rw [← Functor.map_comp, hGU]

/-- 概要：標準局所相対極限があれば元と底を厳密に保つ右 Kan 延長が存在する。
方針：反転したデータへ双対化した存在定理を適用し、反転関手の二乗の等式で戻す。
規約：元 F₀ と底 H₀ を自然同型ではなく等式で保つ。
使われ方：一般の isofibration 上の元の相対右 Kan 制限の存在部分。 -/
lemma exists_kanRelativeRightCanonical_strict_extension_of_local_relative_limits
    {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (F₀ : K ⟶ D) (H₀ : C ⟶ E) (hFU : F₀ ≫ U = δ ≫ H₀)
    (hlocal : ∀ c : C _⦋0⦌, ∃ z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram δ F₀ c),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone U z ∧ z.val ≫ U = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ H₀ c).val) :
    ∃ G : C ⟶ D, δ ≫ G = F₀ ∧ G ≫ U = H₀ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom U δ G := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have hFUop : SSet.opFunctor.map F₀ ≫ SSet.opFunctor.map U =
      SSet.opFunctor.map δ ≫ SSet.opFunctor.map H₀ := by
    simpa only [Functor.map_comp] using congrArg (SSet.opFunctor.map) hFU
  have h := exists_kanRelativeRightCanonical_op_strict_extension_of_local_relative_limits
    (SSet.opFunctor.map U) hU.op (SSet.opFunctor.map δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isFullyFaithful_op δ hδ)
    (SSet.opFunctor.map F₀) (SSet.opFunctor.map H₀) hFUop
  change (∀ c : (SSet.opFunctor ⋙ SSet.opFunctor).obj C _⦋0⦌,
    ∃ z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram ((SSet.opFunctor ⋙ SSet.opFunctor).map δ)
      ((SSet.opFunctor ⋙ SSet.opFunctor).map F₀) c),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone ((SSet.opFunctor ⋙ SSet.opFunctor).map U) z ∧
        z.val ≫ (SSet.opFunctor ⋙ SSet.opFunctor).map U =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone ((SSet.opFunctor ⋙ SSet.opFunctor).map δ)
            ((SSet.opFunctor ⋙ SSet.opFunctor).map H₀) c).val) →
    ∃ G : (SSet.opFunctor ⋙ SSet.opFunctor).obj C ⟶
        (SSet.opFunctor ⋙ SSet.opFunctor).obj D,
      (SSet.opFunctor ⋙ SSet.opFunctor).map δ ≫ G =
        (SSet.opFunctor ⋙ SSet.opFunctor).map F₀ ∧
      G ≫ (SSet.opFunctor ⋙ SSet.opFunctor).map U =
        (SSet.opFunctor ⋙ SSet.opFunctor).map H₀ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom ((SSet.opFunctor ⋙ SSet.opFunctor).map U)
        ((SSet.opFunctor ⋙ SSet.opFunctor).map δ) G at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.oppositeFunctor_square] at h
  exact h hlocal

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
