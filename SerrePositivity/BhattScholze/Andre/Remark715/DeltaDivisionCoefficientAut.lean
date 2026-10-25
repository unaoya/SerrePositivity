module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaAdjoinDivisionSum

/-!
# André E1・E2：係数 δ 自己同型による raw 除算包の比較

## 概要

係数環の δ 自己同型 e は、raw δ 除算包 A{a/d} と A{e(a)/e(d)} の環同型を誘導する。
BS Rem 7.15（著者版 p.62）、Cor 2.39（p.25）の Frobenius による係数変更への準備。

## 方針

除算解を同じ添字の初期変数へ送り、普遍性で順射と逆射を作る。
逆合成は係数と初期除算変数上の外延性で確認する。

## 規約

完備化・ねじれ除去・pd 包との同定は含めない。係数自己同型の向きを明示する。

## 使われ方

完全な無限根 δ 入力環の Frobenius 同型を代入して raw 包の係数変更を具体化する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (e : A ≃+* A) (he : D.IsDeltaHom D e.toRingHom)
variable (d : A) (a : σ → A)
local notation "L" => DeltaAdjoinDivision D d a
local notation "M" => DeltaAdjoinDivision D (e d) (fun s => e (a s))
local notation "DL" => deltaAdjoinDivisionStructure D d a
local notation "DM" => deltaAdjoinDivisionStructure D (e d) (fun s => e (a s))
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "jM" => deltaAdjoinDivisionMap D (e d) (fun s => e (a s))
local notation "vL" => deltaAdjoinDivisionVariable D d a
local notation "vM" => deltaAdjoinDivisionVariable D (e d) (fun s => e (a s))

/-- 概要：係数自己同型と同じ除算変数を延長する順射。
方針：δ 除算の普遍性に標準関係式を供給する。
規約：分母も入力族も e で送る。
使われ方：BS Rem 7.15（著者版 p.62）の raw Frobenius 係数変更。 -/
def deltaDivisionCoefficientAutMap : L →+* M :=
  (existsUnique_deltaAdjoinDivisionHom D DM d a ((jM).comp e.toRingHom)
    ((deltaAdjoinDivisionMap_isDeltaHom D (e d) (fun s => e (a s))).comp he) vM
    (fun s => deltaAdjoinDivision_relation D (e d) (fun t => e (a t)) s)).choose

/-- 概要：順射は δ、係数射、全初期除算変数と両立する。
方針：普遍性の選択した射の仕様を使う。
規約：係数射の合成に e を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の係数作用と逆合成の照合。 -/
theorem deltaDivisionCoefficientAutMap_spec :
    (DL).IsDeltaHom DM (deltaDivisionCoefficientAutMap D e he d a) ∧
    (deltaDivisionCoefficientAutMap D e he d a).comp jL = (jM).comp e.toRingHom ∧
    ∀ s, deltaDivisionCoefficientAutMap D e he d a (vL s) = vM s :=
  (existsUnique_deltaAdjoinDivisionHom D DM d a ((jM).comp e.toRingHom)
    ((deltaAdjoinDivisionMap_isDeltaHom D (e d) (fun s => e (a s))).comp he) vM
    (fun s => deltaAdjoinDivision_relation D (e d) (fun t => e (a t)) s)).choose_spec.1

/-- 概要：逆係数自己同型と同じ除算変数を延長する逆射。
方針：元の標準関係式を e の逆合成で書き直して普遍性を使う。
規約：始域は e で送った関係族の包。
使われ方：BS Rem 7.15（著者版 p.62）の raw 係数変更の可逆性。 -/
def deltaDivisionCoefficientAutInverse : M →+* L :=
  (existsUnique_deltaAdjoinDivisionHom D DL (e d) (fun s => e (a s))
    ((jL).comp e.symm.toRingHom) ((deltaAdjoinDivisionMap_isDeltaHom D d a).comp he.symm)
    vL (fun s => by simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply] using deltaAdjoinDivision_relation D d a s)).choose

/-- 概要：逆射は δ、逆係数射、全初期除算変数と両立する。
方針：逆射を選んだ普遍性の仕様を使う。
規約：係数には e⁻¹ を適用する。
使われ方：BS Rem 7.15（著者版 p.62）の逆合成の計算。 -/
theorem deltaDivisionCoefficientAutInverse_spec :
    (DM).IsDeltaHom DL (deltaDivisionCoefficientAutInverse D e he d a) ∧
    (deltaDivisionCoefficientAutInverse D e he d a).comp jM = (jL).comp e.symm.toRingHom ∧
    ∀ s, deltaDivisionCoefficientAutInverse D e he d a (vM s) = vL s :=
  (existsUnique_deltaAdjoinDivisionHom D DL (e d) (fun s => e (a s))
    ((jL).comp e.symm.toRingHom) ((deltaAdjoinDivisionMap_isDeltaHom D d a).comp he.symm)
    vL (fun s => by simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply] using deltaAdjoinDivision_relation D d a s)).choose_spec.1

/-- 概要：係数 δ 自己同型は raw δ 除算包の環同型を誘導する。
方針：順射と逆射の合成を係数・初期変数で検証する。
規約：d の正則性は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の raw Frobenius 引戻し比較の代数的入力。 -/
def deltaDivisionCoefficientAutEquiv : L ≃+* M := by
  have hF := deltaDivisionCoefficientAutMap_spec D e he d a
  have hG := deltaDivisionCoefficientAutInverse_spec D e he d a
  apply RingEquiv.ofRingHom (deltaDivisionCoefficientAutMap D e he d a)
    (deltaDivisionCoefficientAutInverse D e he d a)
  · apply deltaAdjoinDivisionHom_ext D DM (e d) (fun s => e (a s))
      _ _ (hF.1.comp hG.1) (DM).isDeltaHom_id
    · rw [RingHom.comp_assoc, hG.2.1, ← RingHom.comp_assoc, hF.2.1]
      ext b
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply,
        RingHom.id_apply]
    · intro s
      rw [RingHom.comp_apply, hG.2.2, hF.2.2]
      rfl
  · apply deltaAdjoinDivisionHom_ext D DL d a _ _ (hG.1.comp hF.1) (DL).isDeltaHom_id
    · rw [RingHom.comp_assoc, hF.2.1, ← RingHom.comp_assoc, hG.2.1]
      ext b
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply,
        RingHom.id_apply]
    · intro s
      rw [RingHom.comp_apply, hF.2.2, hG.2.2]
      rfl

/-- 概要：raw 包の比較同型は元の係数を e で送る。
方針：順射の係数合成の等式を各元で評価する。
規約：同型は係数に関して e 半線形。
使われ方：BS Rem 7.15（著者版 p.62）の係数作用の記録。 -/
theorem deltaDivisionCoefficientAutEquiv_coeff (b : A) :
    deltaDivisionCoefficientAutEquiv D e he d a (jL b) = jM (e b) :=
  DFunLike.congr_fun (deltaDivisionCoefficientAutMap_spec D e he d a).2.1 b

/-- 概要：raw 包の比較同型は全初期除算変数の添字を保つ。
方針：順射の標準変数公式を使う。
規約：δ 反復前の初期変数について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の根方程式の比較。 -/
theorem deltaDivisionCoefficientAutEquiv_variable (s : σ) :
    deltaDivisionCoefficientAutEquiv D e he d a (vL s) = vM s :=
  (deltaDivisionCoefficientAutMap_spec D e he d a).2.2 s

/-- 概要：raw 包の比較同型は実 δ 射。
方針：順射の δ 互換性を使う。
規約：両側の既存の商 δ 構造を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の δ 完備化に進む入力。 -/
theorem deltaDivisionCoefficientAutEquiv_isDeltaHom :
    (DL).IsDeltaHom DM (deltaDivisionCoefficientAutEquiv D e he d a).toRingHom :=
  (deltaDivisionCoefficientAutMap_spec D e he d a).1

end SerrePositivity.BhattScholze.Andre
