module

public import SerrePositivity.EInfinity.BarrattEccles.Fibrancy
public import SerrePositivity.HomotopicalAlgebra.Quillen.DerivedFunctor
public import Mathlib.AlgebraicTopology.ModelCategory.Over
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# E 代数の slice での引き戻しと右導来関手

概要：BM 命題 4.1 のモデル構造で、底を固定した引き戻しは右 Quillen である。
方針：fibration と trivial fibration の基底変換安定性を使う。
規約：モデル構造は具体的な E のものを局所的に選ぶ。
使われ方：E2a-4 の homotopy 引き戻しを右導来関手として構成する。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra

variable (A : Type u) [CommRing A]

/-- 概要：E 代数の slice の基底変換は右 Quillen（BM 命題 4.1）。
方針：二つの右類の基底変換安定性を slice 射の底に適用する。
規約：基底変換射自体の fibration 仮定は不要。
使われ方：fibration 置換による homotopy 引き戻し。 -/
lemma overPullback_isRightQuillen {Y Z : (operad A).Algebra} (g : Y ⟶ Z) :
    let := modelCategory A
    SerrePositivity.Quillen.IsRightQuillen (Over.pullback g) := by
  let := modelCategory A
  constructor
  · intro X X' f hf
    exact (fibrations (operad A).Algebra).overPullbackMap g f hf
  · intro X X' f hf
    exact (trivialFibrations (operad A).Algebra).overPullbackMap g f hf

/-- 概要：slice の対象の底を取る関手は右 Quillen（BM 命題 4.1）。
方針：slice の二つの右類は底の射の逆像で定義されている。
規約：具体的な E のモデル構造を局所的に選ぶ。
使われ方：slice の導来引き戻しを E 代数として受け取る。 -/
lemma overForget_isRightQuillen (Y : (operad A).Algebra) :
    let := modelCategory A
    SerrePositivity.Quillen.IsRightQuillen (Over.forget Y) := by
  let := modelCategory A
  constructor <;> intro X X' f hf <;> exact hf

/-- 概要：固定した右脚との引き戻しを E 代数に値を取る関手にする（BM 命題 4.1）。
方針：slice の基底変換の後で底の代数を取る。
規約：左脚は Over Z の対象。
使われ方：homotopy 引き戻しの右導来関手の元の関手。 -/
def pullbackFunctor {Y Z : (operad A).Algebra} (g : Y ⟶ Z) :
    Over Z ⥤ (operad A).Algebra :=
  Over.pullback g ⋙ Over.forget Y

/-- 概要：固定した右脚との引き戻し関手は右 Quillen（BM 命題 4.1）。
方針：slice の基底変換と忘却の二つの保存則を合成する。
規約：モデル構造の入力仮定なし。
使われ方：fibration 置換で計算する右導来引き戻し。 -/
lemma pullbackFunctor_isRightQuillen {Y Z : (operad A).Algebra} (g : Y ⟶ Z) :
    let := modelCategory A
    SerrePositivity.Quillen.IsRightQuillen (pullbackFunctor A g) := by
  let := modelCategory A
  have := overPullback_isRightQuillen A g
  have := overForget_isRightQuillen A Y
  exact SerrePositivity.Quillen.isRightQuillen_comp (Over.forget Y) (Over.pullback g)

/-- 概要：homotopy 引き戻しの点ごとの右導来関手が存在する（Hovey §1.3）。
方針：引き戻しの右 Quillen 性に既存の fibrant 置換による導来構成を適用する。
規約：値の局所化は任意、E のモデル構造は局所的に選ぶ。
使われ方：具体的な fibration 置換で計算する引き戻しの導来性の根拠。 -/
lemma pullbackFunctor_hasPointwiseRightDerivedFunctor
    {Y Z : (operad A).Algebra} (g : Y ⟶ Z)
    {H : Type w} [Category.{v} H] (Q : (operad A).Algebra ⥤ H) :
    let := modelCategory A
    Q.IsLocalization (weakEquivalences (operad A).Algebra) →
      (pullbackFunctor A g ⋙ Q).HasPointwiseRightDerivedFunctor
        (weakEquivalences (Over Z)) := by
  let := modelCategory A
  change Q.IsLocalization (weakEquivalences (operad A).Algebra) → _
  intro hQ
  have := hQ
  have := pullbackFunctor_isRightQuillen A g
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
