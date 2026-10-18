module

public import SerrePositivity.KST.Descent.BlowupBaseChange

/-!
# 抽象 blowup の底変換の比較立方体と全ての面の Cartesian 性

## 概要
底変換した抽象 blowup から元の正方形への実際の比較立方体を構成する。

## 方針
左上への射は元の Cartesian 正方形の普遍性で作り、各面の Cartesian 性を貼り合わせで検査する。

## 規約
元の中心も例外部分も被約化せず、指定された射を保持する。

## 使われ方
論文 補題 3.3 の Čech 各段における同じ前層の自然な抽象 blowup 列の比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent.AbstractBlowupSquare

variable {S : Scheme.{u}} [IsNoetherian S] (Q : AbstractBlowupSquare S)
  {T : FiniteTypeSchemes S} (h : T ⟶ Q.square.X₄)

/-- 概要：底変換した例外部分の二つの射は元の基底上で可換（補題 3.3）。
方針：二つの指定引き戻しの可換式と新しい正方形の可換式を合成する。
規約：元の左上への普遍性に渡す実際の等式。
使われ方：比較立方体の左上の射の構成。 -/
theorem baseChange_cube_fac :
    ((Q.baseChange h).square.f₁₂ ≫ finiteTypePullbackFst Q.square.f₂₄ h) ≫ Q.square.f₂₄ =
      ((Q.baseChange h).square.f₁₃ ≫ finiteTypePullbackFst Q.square.f₃₄ h) ≫ Q.square.f₃₄ := by
  calc
    _ = ((Q.baseChange h).square.f₁₂ ≫ finiteTypePullbackSnd Q.square.f₂₄ h) ≫ h :=
      (Category.assoc _ _ _).trans
        ((congrArg ((Q.baseChange h).square.f₁₂ ≫ ·)
          (finiteTypePullback_comm Q.square.f₂₄ h)).trans (Category.assoc _ _ _).symm)
    _ = ((Q.baseChange h).square.f₁₃ ≫ finiteTypePullbackSnd Q.square.f₃₄ h) ≫ h :=
      congrArg (· ≫ h) (Q.baseChange h).square.fac
    _ = ((Q.baseChange h).square.f₁₃ ≫ finiteTypePullbackFst Q.square.f₃₄ h) ≫ Q.square.f₃₄ :=
      (Category.assoc _ _ _).trans
        ((congrArg ((Q.baseChange h).square.f₁₃ ≫ ·)
          (finiteTypePullback_comm Q.square.f₃₄ h).symm).trans (Category.assoc _ _ _).symm)

/-- 概要：底変換した抽象 blowup から元の正方形への指定比較立方体（補題 3.3）。
方針：三頂点では底変換の射影を使い、例外部分では元の Cartesian 正方形へ持ち上げる。
規約：四つの側面の可換性を射の等式で保持する。
使われ方：自然な blowup 列を引き戻しで比較する幾何入力。 -/
noncomputable def baseChangeCube : (Q.baseChange h).square ⟶ Q.square where
  τ₁ := Q.isPullback.lift
    ((Q.baseChange h).square.f₁₂ ≫ finiteTypePullbackFst Q.square.f₂₄ h)
    ((Q.baseChange h).square.f₁₃ ≫ finiteTypePullbackFst Q.square.f₃₄ h)
    (Q.baseChange_cube_fac h)
  τ₂ := finiteTypePullbackFst Q.square.f₂₄ h
  τ₃ := finiteTypePullbackFst Q.square.f₃₄ h
  τ₄ := h
  comm₁₂ := (Q.isPullback.lift_fst _ _ _).symm
  comm₁₃ := (Q.isPullback.lift_snd _ _ _).symm
  comm₂₄ := (finiteTypePullback_comm Q.square.f₂₄ h).symm
  comm₃₄ := (finiteTypePullback_comm Q.square.f₃₄ h).symm

/-- 概要：比較立方体の固有射の面は元の有限型の圏で Cartesian（補題 3.3）。
方針：構成に使った指定引き戻しの普遍性を使う。
規約：実際の τ₂ と新しい右辺。使われ方：各 Čech 段の右上を元の底変換として扱う。 -/
theorem baseChangeCube_cartesian₂₄ :
    IsPullback (Q.baseChangeCube h).τ₂ (Q.baseChange h).square.f₂₄ Q.square.f₂₄ h :=
  finiteTypePullback_isPullback Q.square.f₂₄ h

/-- 概要：比較立方体の閉中心の面は元の有限型の圏で Cartesian（補題 3.3）。
方針：構成に使った指定引き戻しの普遍性を使う。
規約：実際の τ₃ と新しい中心。使われ方：中心のスキーム論的底変換を保持する。 -/
theorem baseChangeCube_cartesian₃₄ :
    IsPullback (Q.baseChangeCube h).τ₃ (Q.baseChange h).square.f₃₄ Q.square.f₃₄ h :=
  finiteTypePullback_isPullback Q.square.f₃₄ h

set_option backward.isDefEq.respectTransparency false in
/-- 概要：比較立方体の例外部分から中心への面も Cartesian（補題 3.3）。
方針：新しい正方形と右側の底変換を貼り、元の Cartesian 正方形を右から消去する。
規約：例外部分の被約性は不要。
使われ方：例外部分の中心への底変換と自然な列の整合性。 -/
theorem baseChangeCube_cartesian₁₃ :
    IsPullback (Q.baseChangeCube h).τ₁ (Q.baseChange h).square.f₁₃
      Q.square.f₁₃ (Q.baseChangeCube h).τ₃ := by
  have H := (Q.baseChange h).isPullback.paste_horiz (Q.baseChangeCube_cartesian₂₄ h)
  have H' : IsPullback ((Q.baseChangeCube h).τ₁ ≫ Q.square.f₁₂)
      (Q.baseChange h).square.f₁₃ Q.square.f₂₄
      ((Q.baseChangeCube h).τ₃ ≫ Q.square.f₃₄) :=
    Eq.mp (congrArg₂ (fun a b ↦ IsPullback a (Q.baseChange h).square.f₁₃ Q.square.f₂₄ b)
      (Q.baseChangeCube h).comm₁₂ (Q.baseChangeCube h).comm₃₄) H
  exact H'.of_right (Q.baseChangeCube h).comm₁₃.symm Q.isPullback

set_option backward.isDefEq.respectTransparency false in
/-- 概要：比較立方体の例外部分から変形先への面も Cartesian（補題 3.3）。
方針：反転した新しい正方形と中心の底変換を貼り、元の反転正方形を右から消去する。
規約：実際の τ₁ と新しい上辺。使われ方：例外部分の底変換の両射影を保持する。 -/
theorem baseChangeCube_cartesian₁₂ :
    IsPullback (Q.baseChangeCube h).τ₁ (Q.baseChange h).square.f₁₂
      Q.square.f₁₂ (Q.baseChangeCube h).τ₂ := by
  have H := (Q.baseChange h).isPullback.flip.paste_horiz (Q.baseChangeCube_cartesian₃₄ h)
  have H' : IsPullback ((Q.baseChangeCube h).τ₁ ≫ Q.square.f₁₃)
      (Q.baseChange h).square.f₁₂ Q.square.f₃₄
      ((Q.baseChangeCube h).τ₂ ≫ Q.square.f₂₄) :=
    Eq.mp (congrArg₂ (fun a b ↦ IsPullback a (Q.baseChange h).square.f₁₂ Q.square.f₃₄ b)
      (Q.baseChangeCube h).comm₁₃ (Q.baseChangeCube h).comm₂₄) H
  exact H'.of_right (Q.baseChangeCube h).comm₁₂.symm Q.isPullback.flip

/-- 概要：新しい例外部分そのものも元の例外部分の実際の基底変更（補題 3.3）。
方針：例外部分から中心への Cartesian 面と閉中心の Cartesian 面を縦に貼る。
規約：元の有限型の圏内での指定構造射の Cartesian 性。
使われ方：四頂点すべてを同じ Čech 段への底変換として扱う。 -/
theorem baseChangeCube_cartesian₁₄ :
    IsPullback (Q.baseChangeCube h).τ₁
      ((Q.baseChange h).square.f₁₃ ≫ (Q.baseChange h).square.f₃₄)
      (Q.square.f₁₃ ≫ Q.square.f₃₄) h :=
  (Q.baseChangeCube_cartesian₁₃ h).paste_vert (Q.baseChangeCube_cartesian₃₄ h)

/-- 概要：新しい例外部分と元の例外部分の指定底変換との標準同型（補題 3.3）。
方針：同じ基底変更を表す二つの Cartesian 正方形の標準同型を合成する。
規約：元の有限型の圏と指定引き戻しを使う。
使われ方：例外部分の Čech 図式の自然な底変換への接続。 -/
noncomputable def baseChangeExceptionalIso :
    (Q.baseChange h).square.X₁ ≅ finiteTypePullback (Q.square.f₁₃ ≫ Q.square.f₃₄) h :=
  (Q.baseChangeCube_cartesian₁₄ h).isoPullback ≪≫
    (finiteTypePullback_isPullback (Q.square.f₁₃ ≫ Q.square.f₃₄) h).isoPullback.symm

/-- 概要：例外部分の標準同型は元の例外部分への射を保つ（補題 3.3）。
方針：二つの標準同型の第一射影公式を合成する。
規約：同じ比較立方体の τ₁。使われ方：元の前層の指定比較との整合性。 -/
theorem baseChangeExceptionalIso_hom_fst :
    (Q.baseChangeExceptionalIso h).hom ≫
      finiteTypePullbackFst (Q.square.f₁₃ ≫ Q.square.f₃₄) h = (Q.baseChangeCube h).τ₁ :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (finiteTypePullback_isPullback
      (Q.square.f₁₃ ≫ Q.square.f₃₄) h).isoPullback_inv_fst).trans
        (Q.baseChangeCube_cartesian₁₄ h).isoPullback_hom_fst)

/-- 概要：例外部分の標準同型は新しい基底への構造射を保つ（補題 3.3）。
方針：二つの標準同型の第二射影公式を合成する。
規約：中心への射と中心包含の実際の合成。使われ方：同じ基底上の Čech の射の整合性。 -/
theorem baseChangeExceptionalIso_hom_snd :
    (Q.baseChangeExceptionalIso h).hom ≫
      finiteTypePullbackSnd (Q.square.f₁₃ ≫ Q.square.f₃₄) h =
        (Q.baseChange h).square.f₁₃ ≫ (Q.baseChange h).square.f₃₄ :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (finiteTypePullback_isPullback
      (Q.square.f₁₃ ≫ Q.square.f₃₄) h).isoPullback_inv_snd).trans
        (Q.baseChangeCube_cartesian₁₄ h).isoPullback_hom_snd)

end SerrePositivity.KST.Descent.AbstractBlowupSquare
