module

public import SerrePositivity.KST.Descent.RationalLift
public import SerrePositivity.KST.Descent.Axioms

/-!
# 指定された全次数降下から整数版へ移す比較データ

## 概要
有理化した整数群と前層の指定次数の自然な比較を保持し、PiDescent から正の整数倍の持ち上げを得る。

## 方針
不変な有理類を指定比較で持ち上げ、自然性と同型で元の群の射へ戻して分母とねじれを消す。

## 規約
比較データの存在や (3.6) の同定を証明したとは主張しない。K0・T2 の供給する同定の接続先。

## 使われ方
論文 定理 3.1、(3.6)–(3.7) の比較を通す theorem_3_1_K0 と §4 の整数形。
-/

@[expose] public section

universe u v w t uA uB

open CategoryTheory Opposite
open scoped TensorProduct

namespace SerrePositivity.KST.Descent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] {Coefficient : Type w}
  (L : GradedPresheaf.{u, v, w, t} C Coefficient) (H : Coefficient) (n : ℤ)
  {X Y : C} (p : X ⟶ Y)
  {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)

/-- 概要：整数群の有理化と指定引き戻しを結ぶ自然な比較データ（定理 3.1、(3.6)）。
方針：両端の線形同型と指定した整数写像・前層の引き戻しの可換性を保持する。
規約：K0・T2 の同定を後で供給する引数の型であり、その存在の定理ではない。
使われ方：実際の有理降下が得られた後で整数版へ移す一般的な比較補題。 -/
structure IntegralPullbackComparison where
  /-- 概要：基底側の有理群との同定（論文 (3.6)）。方針：整数線形同型を保持する。
  規約：同定の存在は外部の K0・T2 の証明から供給する。使われ方：基底の有理類の移送。 -/
  source : ℚ ⊗[ℤ] A ≃ₗ[ℤ] (L H n).obj (op Y)
  /-- 概要：始域側の有理群との同定（論文 (3.6)）。方針：整数線形同型を保持する。
  規約：基底側と独立な任意の同型ではなく、次の自然性を要求する。使われ方：始域の類の移送。 -/
  target : ℚ ⊗[ℤ] B ≃ₗ[ℤ] (L H n).obj (op X)
  /-- 概要：指定写像との自然性（論文 (3.6)–(3.7)）。方針：両端の同定での可換式を保持する。
  規約：抽象的な群の同型の存在だけに弱めない。使われ方：同じ整数写像の持ち上げへ戻す。 -/
  naturality : ∀ x : ℚ ⊗[ℤ] A,
    target (rationalScalarExtensionMap f x) = L.pullback H n p (source x)

namespace IntegralPullbackComparison

variable {L H n p f}
  (data : IntegralPullbackComparison L H n p f)
  {G : Type*} [Group G] (action : G →* Aut X)
  (over_base : ∀ g, (action g).asIso.hom ≫ p = p)

/-- 概要：指定 PiDescent と自然な比較データから整数倍の持ち上げを得る（定理 3.1）。
方針：不変部分への指定全射性で有理類を持ち上げ、比較の自然性で元の写像へ移す。
規約：PiDescent と比較データの存在は別途必要。主定理や (3.6) の完成とは区別する。
使われ方：実際の K0・T2 の同定を接続した後の二つの K0 の整数形への最後の移行。 -/
theorem positive_multiple_of_piDescent (descent : L.PiDescent p action over_base)
    (b : B) (hb : data.target (1 ⊗ₜ[ℤ] b) ∈ L.invariantSubmodule H n action) :
    ∃ (k : ℕ) (a : A), 0 < k ∧ k • b = f a := by
  obtain ⟨x, hx⟩ := (descent H n).2 ⟨data.target (1 ⊗ₜ[ℤ] b), hb⟩
  have hpx : L.pullback H n p x = data.target (1 ⊗ₜ[ℤ] b) := congrArg Subtype.val hx
  apply positive_multiple_of_rational_tensor_lift f b (data.source.symm x)
  apply data.target.injective
  exact (data.naturality (data.source.symm x)).trans
    ((congrArg (L.pullback H n p) (data.source.apply_symm_apply x)).trans hpx)

/-- 概要：整数群の G 不変な元は作用と両立する比較で正の整数倍が降下する（定理 3.1）。
方針：整数群の不変性を前層の不変部分へ移し、指定 PiDescent による整数化を使う。
規約：前層の左作用は逆元の引き戻しなので、作用の比較にも逆元を明示する。
使われ方：K0 の g・[P] の規約を保持した theorem_3_1_K0 と §4 の整数形。 -/
theorem positive_multiple_of_invariant [DistribMulAction G B]
    (descent : L.PiDescent p action over_base)
    (equivariance : ∀ (g : G) (b : B),
      data.target (1 ⊗ₜ[ℤ] (g • b)) =
        L.pullback H n (action g⁻¹).asIso.hom (data.target (1 ⊗ₜ[ℤ] b)))
    (b : B) (hb : ∀ g : G, g • b = b) :
    ∃ (k : ℕ) (a : A), 0 < k ∧ k • b = f a := by
  apply data.positive_multiple_of_piDescent action over_base descent b
  intro g
  have he : data.target (1 ⊗ₜ[ℤ] (g⁻¹ • b)) =
      L.pullback H n (action g).asIso.hom (data.target (1 ⊗ₜ[ℤ] b)) := by
    simpa only [inv_inv] using equivariance g⁻¹ b
  exact he.symm.trans (congrArg (fun x : B ↦ data.target (1 ⊗ₜ[ℤ] x)) (hb g⁻¹))

end IntegralPullbackComparison

end SerrePositivity.KST.Descent
