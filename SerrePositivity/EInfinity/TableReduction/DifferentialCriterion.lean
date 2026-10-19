module

public import SerrePositivity.EInfinity.TableReduction.BoundaryExpressions

/-!
# TR の微分保存と頂点境界の恒等式の同値

概要：Berger–Fresse §1.4.4 の組合せ的恒等式が必要十分な条件であることを証明する。
方針：全正規化生成元で検査し、単体と置換列の同値を使う。
規約：一般の恒等式自体は未証明。nullary 分岐だけはここで完了する。
使われ方：行長と削除位置の相殺の証明を実際の線形写像の等式へ渡す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.TableReduction

open Surjection
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：全置換列の境界恒等式から線形な微分保存を得る（BF §1.4.4）。
方針：正規化生成元を基底として両辺を比較する。
規約：恒等式の証明を引数として受け取る条件付きの橋渡し。
使われ方：組合せ的な相殺を証明した後に微分保存を閉じる。 -/
lemma normalizedMap_comm_of_vertexBoundary (n d : ℕ)
    (h : ∀ w : Fin (d + 1 + 1) → Equiv.Perm (Fin n),
      differential A n d (onSequence A w) = vertexBoundary A w) :
    (differential A n d).comp (normalizedMap A n (d + 1)) =
      (normalizedMap A n d).comp ((BarrattEccles.normalizedChains A n).d (d + 1) d).hom := by
  apply (BarrattEccles.normalizedBasis A n (d + 1)).ext
  intro x
  obtain ⟨x⟩ := x
  rw [BarrattEccles.normalizedBasis_apply]
  change differential A n d
      (normalizedMap A n (d + 1) (BarrattEccles.normalizedGenerator A n (d + 1) x.val)) =
    normalizedMap A n d ((BarrattEccles.normalizedChains A n).d (d + 1) d
      (BarrattEccles.normalizedGenerator A n (d + 1) x.val))
  rw [normalizedMap_generator, normalizedMap_d_generator, h]

/-- 概要：微分保存と全置換列の境界恒等式は同値（BF §1.4.4）。
方針：一方は生成元を代入し、他方は基底の検査を使う。
規約：退化する列も恒等式の対象に含む。
使われ方：残る証明内容を明示的な有限和の同一性として固定する。 -/
lemma normalizedMap_comm_iff_vertexBoundary (n d : ℕ) :
    (differential A n d).comp (normalizedMap A n (d + 1)) =
        (normalizedMap A n d).comp ((BarrattEccles.normalizedChains A n).d (d + 1) d).hom ↔
      ∀ w : Fin (d + 1 + 1) → Equiv.Perm (Fin n),
        differential A n d (onSequence A w) = vertexBoundary A w := by
  constructor
  · intro h w
    let x := (BarrattEccles.simplexEquiv n (d + 1)).symm w
    have he := LinearMap.congr_fun h (BarrattEccles.normalizedGenerator A n (d + 1) x)
    change differential A n d
        (normalizedMap A n (d + 1) (BarrattEccles.normalizedGenerator A n (d + 1) x)) =
      normalizedMap A n d ((BarrattEccles.normalizedChains A n).d (d + 1) d
        (BarrattEccles.normalizedGenerator A n (d + 1) x)) at he
    rw [normalizedMap_generator, normalizedMap_d_generator] at he
    simpa only [x, Equiv.apply_symm_apply] using he
  · exact normalizedMap_comm_of_vertexBoundary A n d

/-- 概要：nullary 頂点境界は全次数で零（BF §1.4.4）。
方針：正次数の TR は零で、次数零は二つの空語が逆符号で相殺する。
規約：係数環の標数の仮定なし。
使われ方：微分保存の零入力の境界分岐を閉じる。 -/
lemma vertexBoundary_nullary (d : ℕ) (w : Fin (d + 1 + 1) → Equiv.Perm (Fin 0)) :
    vertexBoundary A w = 0 := by
  cases d with
  | zero => simp [vertexBoundary, onSequence, Fin.sum_univ_two]
  | succ d => simp [vertexBoundary, onSequence]

/-- 概要：nullary 成分での境界恒等式（BF §1.4.4）。
方針：正次数の TR と頂点境界の両方を零にする。
規約：一般の正の arity の相殺は未使用。
使われ方：全 arity の微分保存を構成する際の零入力の分岐。 -/
lemma differential_onSequence_nullary (d : ℕ)
    (w : Fin (d + 1 + 1) → Equiv.Perm (Fin 0)) :
    differential A 0 d (onSequence A w) = vertexBoundary A w := by
  rw [vertexBoundary_nullary]
  simp [onSequence]

end SerrePositivity.EInfinity.TableReduction
