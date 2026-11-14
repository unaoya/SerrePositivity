module
public import SerrePositivity.KST.Fibration.RelativeSCofiberCriterion
public import SerrePositivity.KST.Fibration.Extension

/-! # 元の全 S_n における相対辺の二対三・底変換・拡大安定性

元の同じ全 Ar 評価を用いて工程 (a) の証明を各段に適用する。
商の存在や新しい分数模型を仮定しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ)
include h

/-- 元の実二単体における、相対 S_n 辺の二対三性。 -/
theorem relativeSConstruction_twoOfThree (τ : Δ[2] ⟶ sConstruction n B.obj) :
    let W := fun j : Fin 3 => SSet.yonedaEquiv (stdSimplex.δ j ≫ τ) ∈
      (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌)
    (W 2 → W 0 → W 1) ∧ (W 2 → W 1 → W 0) ∧ (W 0 → W 1 → W 2) := by
  have ht (j : Fin 3) := relativeSConstruction_mem_edge_iff h n
    (SSet.yonedaEquiv (stdSimplex.δ j ≫ τ))
  dsimp only
  constructor
  · intro h₂ h₀
    apply (ht 1).mpr
    intro a
    exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_twoOfThree h (τ ≫ sComponentEvaluation B.obj n a)).1
      ((ht 2).mp h₂ a) ((ht 0).mp h₀ a)
  · constructor
    · intro h₂ h₁
      apply (ht 0).mpr
      intro a
      exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_twoOfThree h (τ ≫ sComponentEvaluation B.obj n a)).2.1
        ((ht 2).mp h₂ a) ((ht 1).mp h₁ a)
    · intro h₀ h₁
      apply (ht 2).mpr
      intro a
      exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_twoOfThree h (τ ≫ sComponentEvaluation B.obj n a)).2.2
        ((ht 0).mp h₀ a) ((ht 1).mp h₁ a)

/-- 元の S_n の実押し出しに沿う、相対辺条件の保存・反映。 -/
theorem relativeSConstruction_pushout_iff (L : Δ[1] ⊗ Δ[1] ⟶ sConstruction n B.obj)
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow L).edge ∈ (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌) ↔
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow L).edge ∈ (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌) := by
  rw [relativeSConstruction_mem_edge_iff h, relativeSConstruction_mem_edge_iff h]
  apply forall_congr'
  intro a
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_pushout_iff h (L ≫ sComponentEvaluation B.obj n a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPushoutSquare (sComponentEvaluation B.obj n a) L hL)

/-- 元の S_n の実引き戻しに沿う、相対辺条件の保存・反映。 -/
theorem relativeSConstruction_pullback_iff (L : Δ[1] ⊗ Δ[1] ⟶ sConstruction n B.obj)
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare L) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow L).edge ∈ (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌) ↔
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow L).edge ∈ (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌) := by
  rw [relativeSConstruction_mem_edge_iff h, relativeSConstruction_mem_edge_iff h]
  apply forall_congr'
  intro a
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_pullback_iff h (L ≫ sComponentEvaluation B.obj n a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPullbackSquare (sComponentEvaluation B.obj n a) L hL)

/-- 元の二つの cofiber 図式間の同じホモトピーに対する、相対 S_n 辺の拡大安定性。 -/
theorem relativeSConstruction_extension (t d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (sConstruction n B.obj))
    (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t) (hd : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence d)
    (H : SSet.Homotopy t.square d.square)
    (h₀ : (componentEdge H (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1])) 0 0)).edge ∈
      (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌))
    (h₂ : (componentEdge H (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1])) 1 1)).edge ∈
      (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌)) :
    (componentEdge H (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1])) 1 0)).edge ∈
      (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌) := by
  apply (relativeSConstruction_mem_edge_iff h n _).mpr
  intro a
  let e := sComponentEvaluation B.obj n a
  let T := t.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := e))
  let D := d.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := e))
  let K : SSet.Homotopy T.square D.square := {
    h := H.h ≫ e
    h₀ := by rw [← Category.assoc, H.h₀]; rfl
    h₁ := by rw [← Category.assoc, H.h₁]; rfl }
  exact weakEquivalences_extension h T D
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := e) t ht)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := e) d hd) K
    ((relativeSConstruction_mem_edge_iff h n _).mp h₀ a)
    ((relativeSConstruction_mem_edge_iff h n _).mp h₂ a)

end SerrePositivity.KST.Fibration
