module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 二つの四角形の貼り合わせの形状

概要：Δ[2] × Δ[1] の左・右・外側の四角形と、その共有辺を構成する。
方針：三つの余面で制限し、標準単体の有限頂点写像で辺の一致を計算する。
規約：第一座標を横方向とし、余面 2 が左、0 が右、1 が外側。
使われ方：S4 の HTT Lemma 4.4.2.1 とその引き戻しの双対。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：横に並んだ二四角形の指定した余面の四角形。
方針：第一座標の余面で前合成する。
規約：i=2 は左、i=0 は右、i=1 は外側。
使われ方：貼り合わせ定理の三つの普遍四角形。 -/
def pastingSquare {X : SSet.{u}} (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (i : Fin 3) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X := (stdSimplex.δ i ▷ Δ[1]) ≫ F

/-- 概要：長方形の下側の横の二単体。
方針：縦座標を零に固定する。
規約：長辺も含めた実際の二単体。
使われ方：貼り合わせの横の射の合成の照合。 -/
def pastingBottomTriangle {X : SSet.{u}} (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (Δ[2] : SSet.{u}) ⟶ X :=
  lift (𝟙 Δ[2]) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ F

/-- 概要：長方形の上側の横の二単体。
方針：縦座標を一に固定する。
規約：長辺も含めた実際の二単体。
使われ方：貼り合わせの横の射の合成の照合。 -/
def pastingTopTriangle {X : SSet.{u}} (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (Δ[2] : SSet.{u}) ⟶ X :=
  lift (𝟙 Δ[2]) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ F

/-- 概要：左四角形の右辺と右四角形の左辺は厳密に一致する。
方針：両方の第一座標が中央の頂点になることを計算する。
規約：普遍性は仮定しない。
使われ方：共有辺の図式の固定。 -/
lemma pastingSquare_sharedEdge {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ pastingSquare F 2 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ pastingSquare F 0 := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (stdSimplex.δ (2 : Fin 3) ▷ Δ[1])) ≫ F =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (stdSimplex.δ (0 : Fin 3) ▷ Δ[1])) ≫ F
  exact congrArg (fun e : (Δ[1] : SSet.{u}) ⟶ Δ[2] ⊗ Δ[1] ↦ e ≫ F)
    (SSet.yonedaEquiv.injective (Prod.ext (by decide) (by decide)))

/-- 概要：外側四角形の左辺は左四角形の左辺。
方針：第一座標がいずれも零になることを計算する。
規約：辺の厳密な等式。
使われ方：外側の cospan と内部の cospan の比較。 -/
lemma pastingSquare_outer_leftEdge {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ pastingSquare F 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ pastingSquare F 2 := by
  rfl

/-- 概要：外側四角形の右辺は右四角形の右辺。
方針：第一座標がいずれも最後の頂点になることを計算する。
規約：辺の厳密な等式。
使われ方：外側の span と内部の span の比較。 -/
lemma pastingSquare_outer_rightEdge {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ pastingSquare F 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ pastingSquare F 0 := by
  rfl

/-- 概要：各四角形の下辺は下側二単体の対応する辺。
方針：余面と縦座標零の包含が可換することを計算する。
規約：余面 i は左・右・外側のいずれでもよい。
使われ方：h C の横の射の合成を表す二単体。 -/
lemma pastingSquare_bottomEdge {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (i : Fin 3) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ pastingSquare F i = stdSimplex.δ i ≫ pastingBottomTriangle F := by
  rfl

/-- 概要：各四角形の上辺は上側二単体の対応する辺。
方針：余面と縦座標一の包含が可換することを計算する。
規約：余面 i は左・右・外側のいずれでもよい。
使われ方：h C の横の射の合成を表す二単体。 -/
lemma pastingSquare_topEdge {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (i : Fin 3) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ pastingSquare F i = stdSimplex.δ i ≫ pastingTopTriangle F := by
  rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
