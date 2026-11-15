module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionVertices

/-!
概要：二つの左因子の長さの比較から、残りの水平因子の各頂点を実際に作る。
方針：重みの差に対応する元のHomの対象を作り、全合成の重みで照合する。
規約：minusからplusへの非空の条件も証明する。射の構成は別に行う。
使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の分解の一意性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：許される重みに対応する元の実Homの対象。
方針：自己Homは増大順序集合、混合Homは対応する次元を使う。
規約：minusからplusへは正の重みを要求する。使われ方：Riehl–Verity Remark 3.3.8。 -/
def walkingAdjunctionObjectOfWeight (X Y : WalkingAdjunctionPoint) (w : ℕ)
    (_h : X = .minus → Y = .plus → 0 < w) : walkingAdjunctionHom X Y := by
  cases X <;> cases Y
  · exact augmentedOrdinalOfCard w
  · exact ⟨⦋w⦌⟩
  · exact ⟨⦋w - 1⦌⟩
  · exact op (augmentedOrdinalOfCard w)

/-- 概要：構成した実対象の重みは指定された重み。
方針：非空の混合Homの引算は正の条件から照合する。
規約：全四Homを含む。使われ方：Riehl–Verity Proposition 3.1.10 の残りの因子。 -/
lemma walkingAdjunctionObjectOfWeight_weight (X Y : WalkingAdjunctionPoint) (w : ℕ)
    (h : X = .minus → Y = .plus → 0 < w) :
    walkingAdjunctionWeight X Y (walkingAdjunctionObjectOfWeight X Y w h) = w := by
  cases X <;> cases Y
  · exact augmentedOrdinalCard_ofCard w
  · rfl
  · change w - 1 + 1 = w
    have hp := h rfl rfl
    omega
  · exact augmentedOrdinalCard_ofCard w

/-- 概要：左因子の長さが小さければ重みも小さい。
方針：長さと重みの端点の補正を比較する。
規約：中点は異なってよい。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionPrefix_weight_le {X M N : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B) :
    walkingAdjunctionWeight X M A ≤ walkingAdjunctionWeight X N B := by
  have h₁ := walkingAdjunctionVertexLength_weight X M A
  have h₂ := walkingAdjunctionVertexLength_weight X N B
  cases M <;> cases N <;> simp only [walkingAdjunctionTargetCorrection] at h₁ h₂ <;> omega

/-- 概要：minusからplusへ残りを取る場合、重みの差は正。
方針：長さと重みの補正の偶奇を使う。
規約：残りの実Homの非空条件を供給する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionPrefix_difference_admissible {X M N : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B) :
    M = .minus → N = .plus →
      0 < walkingAdjunctionWeight X N B - walkingAdjunctionWeight X M A := by
  intro hM hN
  subst M
  subst N
  have h₁ := walkingAdjunctionVertexLength_weight X .minus A
  have h₂ := walkingAdjunctionVertexLength_weight X .plus B
  simp only [walkingAdjunctionTargetCorrection] at h₁ h₂
  omega

/-- 概要：短い左因子と長い左因子の間の実際の残りの対象。
方針：重みの差を実Homの対象に戻す。
規約：存在を仮定せず元の四Hom内に作る。使われ方：Riehl–Verity Proposition 3.1.10。 -/
def walkingAdjunctionResidualObject {X M N : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B) :
    walkingAdjunctionHom M N :=
  walkingAdjunctionObjectOfWeight M N
    (walkingAdjunctionWeight X N B - walkingAdjunctionWeight X M A)
    (walkingAdjunctionPrefix_difference_admissible A B h)

/-- 概要：残りの対象の重みは指定した差。
方針：対象を作る構成の重みの法則を使う。
規約：同じ実対象。使われ方：Riehl–Verity Proposition 3.1.10 の合成の照合。 -/
lemma walkingAdjunctionResidualObject_weight {X M N : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B) :
    walkingAdjunctionWeight M N (walkingAdjunctionResidualObject A B h) =
      walkingAdjunctionWeight X N B - walkingAdjunctionWeight X M A :=
  walkingAdjunctionObjectOfWeight_weight _ _ _ _

/-- 概要：短い左因子と実際に作った残りの合成は長い左因子に一致する。
方針：重みの単射性と全合成の加法則を使う。
規約：対象の等式。使われ方：Riehl–Verity Proposition 3.1.10 の実分解の回収。 -/
lemma walkingAdjunctionResidualObject_prefix {X M N : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B) :
    (walkingAdjunctionHorizontal X M N).obj (A, walkingAdjunctionResidualObject A B h) = B := by
  apply walkingAdjunctionWeight_injective X N
  rw [walkingAdjunctionHorizontal_weight, walkingAdjunctionResidualObject_weight]
  have hw := walkingAdjunctionPrefix_weight_le A B h
  omega

/-- 概要：残りの対象と短い右因子の合成は長い右因子に一致する。
方針：元の二つの全分解の重みと、残りの重みを比較する。
規約：同じ合成の対象の等式を使う。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionResidualObject_suffix {X M N Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom X N)
    (C : walkingAdjunctionHom M Y) (D : walkingAdjunctionHom N Y)
    (h : walkingAdjunctionVertexLength X M A ≤ walkingAdjunctionVertexLength X N B)
    (hc : (walkingAdjunctionHorizontal X M Y).obj (A, C) =
      (walkingAdjunctionHorizontal X N Y).obj (B, D)) :
    (walkingAdjunctionHorizontal M N Y).obj (walkingAdjunctionResidualObject A B h, D) = C := by
  apply walkingAdjunctionWeight_injective M Y
  rw [walkingAdjunctionHorizontal_weight, walkingAdjunctionResidualObject_weight]
  have hw := congrArg (walkingAdjunctionWeight X Y) hc
  simp only [walkingAdjunctionHorizontal_weight] at hw
  have hab := walkingAdjunctionPrefix_weight_le A B h
  omega

end SerrePositivity.InfinityCategories.HA.Monads
