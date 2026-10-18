module

public import SerrePositivity.KST.Descent.RestrictionBaseChange
public import SerrePositivity.KST.Descent.ClosedImmersionSquare
public import SerrePositivity.KST.Descent.FiniteTypeLimits
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# 抽象 blowup 正方形の実際の底変換

## 概要
任意の抽象 blowup 正方形を、元の有限型の圏内の射へ底変換する。

## 方針
固有射と閉中心を別々に引き戻し、同じ中心の逆像補集合上の同型性を検査する。

## 規約
中心の被約性は要求せず、実際の底変換の厚みを保持する。

## 使われ方
論文 補題 3.3 の平坦化正方形を Čech 各段へ移し、同じ前層の抽象 blowup 降下を適用する。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent.AbstractBlowupSquare

/-- 概要：抽象 blowup 正方形は元の有限型の圏内でも Cartesian（補題 3.3）。
方針：スキームの Cartesian 性を Over と充満部分圏の忘却で反映する。
規約：元の四頂点と四辺を変更しない。
使われ方：底変換の比較立方体の左上の射を一意に構成する。 -/
theorem isPullback {S : Scheme.{u}} (Q : AbstractBlowupSquare S) :
    IsPullback Q.square.f₁₂ Q.square.f₁₃ Q.square.f₂₄ Q.square.f₃₄ := by
  let F := ObjectProperty.ι
    (fun X : Over S ↦ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom) ⋙ Over.forget S
  exact Q.cartesian.of_map F Q.square.fac

variable {S : Scheme.{u}} [IsNoetherian S] (Q : AbstractBlowupSquare S)
  {T : FiniteTypeSchemes S} (h : T ⟶ Q.square.X₄)

/-- 概要：元の有限型の圏内で任意の射への抽象 blowup の底変換を構成（補題 3.3）。
方針：固有射と閉中心の底変換を使い、逆像の補開集合上の実際の同型性を証明する。
規約：閉中心を被約化せず、元の中心のスキーム論的な底変換を保持する。
使われ方：実際の Čech 各段への抽象 blowup の降下の供給。 -/
noncomputable def baseChange : AbstractBlowupSquare S := by
  have : IsProper Q.square.f₂₄.hom.left := Q.proper
  have : IsClosedImmersion Q.square.f₃₄.hom.left := Q.closed
  let p := finiteTypePullbackSnd Q.square.f₂₄ h
  let i := finiteTypePullbackSnd Q.square.f₃₄ h
  have : IsProper p.hom.left := inferInstanceAs
    (IsProper (pullback.snd Q.square.f₂₄.hom.left h.hom.left))
  have : IsClosedImmersion i.hom.left := inferInstanceAs
    (IsClosedImmersion (pullback.snd Q.square.f₃₄.hom.left h.hom.left))
  let U := h.hom.left ⁻¹ᵁ Q.complement
  have hcompl : (U : Set T.obj.left) = (Set.range i.hom.left)ᶜ := by
    change h.hom.left ⁻¹' (Q.complement : Set Q.square.X₄.obj.left) =
      (Set.range (pullback.snd Q.square.f₃₄.hom.left h.hom.left))ᶜ
    rw [Scheme.Pullback.range_snd, ← Set.preimage_compl, ← Q.complement_eq]
  have : IsIso (Q.square.f₂₄.hom.left ∣_ Q.complement) := Q.iso_on_complement
  have hiso : IsIso (p.hom.left ∣_ U) :=
    pullback_snd_iso_over_open Q.square.f₂₄.hom.left h.hom.left Q.complement
  exact abstractBlowupOfClosedImmersion p i U hcompl hiso

/-- 概要：底変換した右辺は元の固有射の指定底変換（補題 3.3）。
方針：構成の定義を使う。
規約：同型な代用品へ交換しない。使われ方：Čech 各段の右辺を固定する。 -/
@[simp] theorem baseChange_modification :
    (Q.baseChange h).square.f₂₄ = finiteTypePullbackSnd Q.square.f₂₄ h := rfl

/-- 概要：底変換した閉中心は元の中心の指定底変換（補題 3.3）。
方針：構成の定義を使う。
規約：被約化しない。使われ方：Čech 各段の中心を固定する。 -/
@[simp] theorem baseChange_center :
    (Q.baseChange h).square.f₃₄ = finiteTypePullbackSnd Q.square.f₃₄ h := rfl

/-- 概要：底変換した正方形の補開集合は同じ中心補集合の逆像（補題 3.3）。
方針：構成の定義を使う。
規約：単なる稠密開部分への置換ではない。使われ方：実際の中心外同型の適用範囲。 -/
@[simp] theorem baseChange_complement :
    (Q.baseChange h).complement = h.hom.left ⁻¹ᵁ Q.complement := rfl

end SerrePositivity.KST.Descent.AbstractBlowupSquare
