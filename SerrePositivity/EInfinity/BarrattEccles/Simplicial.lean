module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Barratt–Eccles の単体集合と右作用

概要：Berger–Fresse §1.1 の EΣₙ を置換群の codiscrete 圏の nerve として構成する。
方針：q 単体と q+1 個の置換の列との同値で、同時右乗法を計算する。
規約：群の積は Mathlib の置換の積、作用は右作用とする。
使われ方：正規化鎖の基底と Σₙ 上の自由性の入力になる。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：EΣₙ の単体集合（Berger–Fresse §1.1）。
方針：任意の二対象間に一意な射を持つ置換の圏の nerve を取る。
規約：対象は Fin n の置換であり、群を一対象圏としては扱わない。
使われ方：Barratt–Eccles の正規化鎖の単体集合となる。 -/
def simplicial (n : ℕ) : SSet := nerve (Codiscrete (Equiv.Perm (Fin n)))

/-- 概要：EΣₙ の q 単体を置換の列で記述する（Berger–Fresse §1.1）。
方針：codiscrete 圏の nerve の頂点列を取り出す。
規約：q 単体は q+1 個の置換を持つ。
使われ方：作用と退化の計算に用いる。 -/
def simplexEquiv (n q : ℕ) :
    (simplicial n) _⦋q⦌ ≃ (Fin (q + 1) → Equiv.Perm (Fin n)) :=
  Codiscrete.equivFun

/-- 概要：置換列への同時右乗法を単体集合の射にする（Berger–Fresse §1.1）。
方針：置換の右乗法を codiscrete 圏の関手にして nerve を取る。
規約：作用する置換を最後の引数とする。
使われ方：正規化鎖上の Σₙ 右作用を誘導する。 -/
def rightAction (n : ℕ) (σ : Equiv.Perm (Fin n)) : simplicial n ⟶ simplicial n :=
  nerveMap (Codiscrete.functorOfFun (fun τ => τ * σ))

/-- 概要：右作用は全ての頂点に同じ置換を右乗する（Berger–Fresse §1.1）。
方針：nerve の射を頂点で評価する。
規約：単体次数 q と頂点 i を明示する。
使われ方：右作用の法則と自由性を証明する。 -/
@[simp] lemma simplexEquiv_rightAction (n q : ℕ) (σ : Equiv.Perm (Fin n))
    (x : (simplicial n) _⦋q⦌) (i : Fin (q + 1)) :
    simplexEquiv n q ((rightAction n σ).app _ x) i = simplexEquiv n q x i * σ := rfl

/-- 概要：単位置換は EΣₙ 上で恒等的に作用する（Berger–Fresse §1.1）。
方針：頂点列の同値を通じて群の単位則を使う。
規約：単体集合の射としての等式。
使われ方：鎖複体上の右作用の単位則となる。 -/
@[simp] lemma rightAction_one (n : ℕ) : rightAction n 1 = 𝟙 (simplicial n) := by
  ext Δ x
  apply (simplexEquiv n Δ.unop.len).injective
  funext i
  exact mul_one _

/-- 概要：置換の積は右作用の順次適用に対応する（Berger–Fresse §1.1）。
方針：頂点ごとに群の結合則を使う。
規約：先に σ、次に τ を作用させる。
使われ方：正規化鎖の右作用の積の法則となる。 -/
lemma rightAction_mul (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    rightAction n (σ * τ) = rightAction n σ ≫ rightAction n τ := by
  ext Δ x
  apply (simplexEquiv n Δ.unop.len).injective
  funext i
  exact (mul_assoc _ _ _).symm

/-- 概要：各単体に対する右作用の軌道写像は単射である（Berger–Fresse §1.1）。
方針：先頭の頂点で評価し、群の左消去則を使う。
規約：次数 0 と arity 0 も含める。
使われ方：正規化鎖の自由な群作用の基礎となる。 -/
lemma rightAction_injective (n q : ℕ) (x : (simplicial n) _⦋q⦌) :
    Function.Injective (fun σ => (rightAction n σ).app _ x) := by
  intro σ τ h
  have h₀ := congrArg (fun y => simplexEquiv n q y 0) h
  simpa only [simplexEquiv_rightAction, mul_left_cancel_iff] using h₀

/-- 概要：単体を固定する置換は単位だけである（Berger–Fresse §1.1）。
方針：軌道写像の単射性と単位作用を用いる。
規約：単体次数によらない自由性の点ごとの記述。
使われ方：Σ-cofibrancy の自由基底の検証に用いる。 -/
lemma rightAction_eq_self_iff (n q : ℕ) (x : (simplicial n) _⦋q⦌)
    (σ : Equiv.Perm (Fin n)) : (rightAction n σ).app _ x = x ↔ σ = 1 := by
  constructor
  · intro h
    apply rightAction_injective n q x
    simpa only [rightAction_one, NatTrans.id_app, types_id_apply] using h
  · rintro rfl
    simp

end SerrePositivity.EInfinity.BarrattEccles
