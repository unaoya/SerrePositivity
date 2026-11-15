module

public import SerrePositivity.AlgebraicGeometry.CoefficientArrowStage

/-!
概要：降ろした射と元の射の、段の底変換模型への比較の自然性。
方針：同時降下で保持した基底座標と固定模型への射影の式から、二射影で判定する。
規約：段の射の単射性・忠実平坦性を仮定しない。
使われ方：G2 の反転・三重交叉の式を極限で照合する入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {T S B : Scheme.{u}} {g : T ⟶ S}
  (a : CartesianModelArrow g) (b : T ⟶ B) (γ : B ⟶ S) (h : b ≫ γ = g)

/-- 元の射を段の標的へ lift した実際の射。 -/
def CartesianModelArrow.targetLiftAt : a.source ⟶ pullback γ a.targetMap :=
  pullback.lift (a.base ≫ b) a.arrow (by rw [Category.assoc, h, a.toBase])

/-- 段の源模型への比較自体も元の基底射の底変換。 -/
theorem CartesianModelArrow.isPullback_comparisonAt :
    IsPullback (a.comparisonAt b γ h) a.base (pullback.fst γ a.sourceMap) b := by
  have houter : IsPullback (a.comparisonAt b γ h ≫ pullback.snd γ a.sourceMap)
      a.base a.sourceMap (b ≫ γ) := by
    simpa only [CartesianModelArrow.comparisonAt, pullback.lift_snd, h] using a.cartesian
  exact houter.of_right
    (by simp only [CartesianModelArrow.comparisonAt, pullback.lift_fst])
    (IsPullback.of_hasPullback γ a.sourceMap).flip

/-- 元の比較と降ろした射は、段の標的への実際の射として可換。 -/
theorem CartesianModelArrow.comparisonAt_map
    (l : pullback γ a.sourceMap ⟶ pullback γ a.targetMap)
    (hl : l ≫ pullback.fst γ a.targetMap = pullback.fst γ a.sourceMap)
    (hn : a.comparisonAt b γ h ≫ l ≫ pullback.snd γ a.targetMap = a.arrow) :
    a.comparisonAt b γ h ≫ l = a.targetLiftAt b γ h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, hl, CartesianModelArrow.comparisonAt,
      CartesianModelArrow.targetLiftAt, pullback.lift_fst]
  · simpa only [Category.assoc, CartesianModelArrow.targetLiftAt, pullback.lift_snd] using hn

end SerrePositivity.AlgebraicGeometry
