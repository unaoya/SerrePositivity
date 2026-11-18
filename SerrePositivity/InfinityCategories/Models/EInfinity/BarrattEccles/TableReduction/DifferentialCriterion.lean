module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.BoundaryExpressions

/-!
模型。文献の定義との比較は後で
# TR の微分保存と頂点境界の恒等式の同値

概要：Berger–Fresse §1.4.4 の組合せ的恒等式が必要十分な条件であることを証明する。
方針：全正規化生成元で検査し、単体と置換列の同値を使う。
規約：一般の恒等式の相殺は DifferentialPreservation で証明し、この界面へ渡す。
使われ方：行長と削除位置の相殺の証明を実際の線形写像の等式へ渡す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：全置換列の境界恒等式から線形な微分保存を得る（BF §1.4.4）。
方針：正規化生成元を基底として両辺を比較する。
規約：恒等式の証明を引数として受け取る条件付きの橋渡し。
使われ方：組合せ的な相殺を証明した後に微分保存を閉じる。 -/
lemma normalizedMap_comm_of_vertexBoundary (n d : ℕ)
    (h : ∀ w : Fin (d + 1 + 1) → Equiv.Perm (Fin n),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A w) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n (d + 1)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d).comp ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d (d + 1) d).hom := by
  apply (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedBasis A n (d + 1)).ext
  intro x
  obtain ⟨x⟩ := x
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedBasis_apply]
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n (d + 1) (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A n (d + 1) x.val)) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d (d + 1) d
      (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A n (d + 1) x.val))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_generator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_d_generator, h]

/-- 概要：微分保存と全置換列の境界恒等式は同値（BF §1.4.4）。
方針：一方は生成元を代入し、他方は基底の検査を使う。
規約：退化する列も恒等式の対象に含む。
使われ方：残る証明内容を明示的な有限和の同一性として固定する。 -/
lemma normalizedMap_comm_iff_vertexBoundary (n d : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n (d + 1)) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d).comp ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d (d + 1) d).hom ↔
      ∀ w : Fin (d + 1 + 1) → Equiv.Perm (Fin n),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A w := by
  constructor
  · intro h w
    let x := (_root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv n (d + 1)).symm w
    have he := LinearMap.congr_fun h (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A n (d + 1) x)
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n (d + 1) (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A n (d + 1) x)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A n d ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A n).d (d + 1) d
        (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedGenerator A n (d + 1) x)) at he
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_generator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_d_generator] at he
    simpa only [x, Equiv.apply_symm_apply] using he
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_comm_of_vertexBoundary A n d

/-- 概要：nullary 頂点境界は全次数で零（BF §1.4.4）。
方針：正次数の TR は零で、次数零は二つの空語が逆符号で相殺する。
規約：係数環の標数の仮定なし。
使われ方：微分保存の零入力の境界分岐を閉じる。 -/
lemma vertexBoundary_nullary (d : ℕ) (w : Fin (d + 1 + 1) → Equiv.Perm (Fin 0)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A w = 0 := by
  cases d with
  | zero => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence, Fin.sum_univ_two]
  | succ d => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence]

/-- 概要：nullary 成分での境界恒等式（BF §1.4.4）。
方針：正次数の TR と頂点境界の両方を零にする。
規約：一般の正の arity の相殺は未使用。
使われ方：全 arity の微分保存を構成する際の零入力の分岐。 -/
lemma differential_onSequence_nullary (d : ℕ)
    (w : Fin (d + 1 + 1) → Equiv.Perm (Fin 0)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A 0 d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary A w := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexBoundary_nullary]
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
