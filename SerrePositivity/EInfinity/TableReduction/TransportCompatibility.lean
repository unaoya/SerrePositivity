module

public import SerrePositivity.EInfinity.Surjection.Transports
public import SerrePositivity.EInfinity.TableReduction.CompositionAll
public import SerrePositivity.EInfinity.TableReduction.DifferentialPreservation
public import SerrePositivity.EInfinity.BarrattEccles.ArityDegreeTransport

/-!
# TR の添字移送と微分の評価

概要：Berger–Fresse §1.3 の全射 TR を χ の法則の移送に使う評価公式を構成する。
方針：添字等式は消去し、微分の可換性は元で評価する。
規約：全 arity・全次数・任意の可換環。
使われ方：χ の Leibniz 則・単位・結合則を BE の法則から証明する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.TableReduction

variable (A : Type u) [CommRing A]

/-- 概要：TR は次数の等式移送と可換（BF §1.3）。
方針：等式を消去して恒等移送へ帰着する。
規約：追加の基底や切断を選択しない。
使われ方：BE の Leibniz 則と結合則の次数移送を χ へ移す。 -/
@[simp] lemma normalizedMap_degreeTransport (n : ℕ) {p q : ℕ} (h : p = q)
    (x : (BarrattEccles.normalizedChains A n).X p) :
    normalizedMap A n q (BarrattEccles.degreeTransport A n h x) =
      Surjection.degreeTransport A n h (normalizedMap A n p x) := by
  cases h
  rfl

/-- 概要：TR は arity の等式移送と可換（BF §1.3）。
方針：等式を消去し、正規化鎖関手の等式の射の保存を使う。
規約：次数は固定する。
使われ方：BE の単位と結合則の arity 移送を χ へ移す。 -/
@[simp] lemma normalizedMap_arityTransport {m n : ℕ} (h : m = n) (d : ℕ)
    (x : (BarrattEccles.normalizedChains A m).X d) :
    normalizedMap A n d
      ((BarrattEccles.normalizedChainMap A (BarrattEccles.simplicialArityMap h)).f d x) =
      Surjection.arityTransport A h d (normalizedMap A m d x) := by
  cases h
  rw [BarrattEccles.normalizedChainMap_arityMap]
  rfl

/-- 概要：正規化 TR の微分可換性を元で評価する（BF §1.4.4）。
方針：既存の線形写像の可換性を任意の元へ適用する。
規約：微分は鎖次数を一つ下げる。
使われ方：BE の Leibniz 則の各微分項を χ の微分へ戻す。 -/
@[simp] lemma normalizedMap_d (n d : ℕ)
    (x : (BarrattEccles.normalizedChains A n).X (d + 1)) :
    normalizedMap A n d ((BarrattEccles.normalizedChains A n).d (d + 1) d x) =
      Surjection.differential A n d (normalizedMap A n (d + 1) x) :=
  (LinearMap.congr_fun (normalizedMap_comm A n d) x).symm

end SerrePositivity.EInfinity.TableReduction
