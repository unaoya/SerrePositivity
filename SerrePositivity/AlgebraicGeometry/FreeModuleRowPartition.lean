module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Logic.Equiv.Set

/-!
概要：KST §5、Stacks 080Z, Lemma 15.8.9 の選んだ行と残りの行への自由加群の分解。
方針：単射の像と補集合への集合の分解を関数加群の線形同型へ移す。
規約：選んだ行を別の同じ対象と定義し直さず、実際の同型として比較する。
使われ方：任意のピボット行を上成分に移して随伴行列の生成元消去を適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {m ι : Type*} (r : ι → m) (hr : Function.Injective r)

/--
概要：単射で選んだ添字と残りの添字の直和から全添字への実際の同型。
方針：単射とその像の同型、および集合と補集合の分解を合成する。
規約：KST §5、Stacks 080Z, Lemma 15.8.9、添字集合の有限性は不要。
使われ方：ピボット行の置換を明示的に構成する。
-/
def rowPartitionEquiv : ι ⊕ {i : m // i ∉ Set.range r} ≃ m := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range r))

/--
概要：行分解のピボット側の値は元の行写像。
方針：同型の順方向を展開する。
規約：KST §5、Stacks 080Z, Lemma 15.8.9。
使われ方：選んだ小行列の係数を保存する。
-/
theorem rowPartitionEquiv_inl (i : ι) : rowPartitionEquiv r hr (Sum.inl i) = r i := rfl

/--
概要：行分解の残りの側の値は補集合の包含。
方針：同型の順方向を展開する。
規約：KST §5、Stacks 080Z, Lemma 15.8.9。
使われ方：残る生成元を元の自由加群に対応させる。
-/
theorem rowPartitionEquiv_inr (i : {i : m // i ∉ Set.range r}) :
    rowPartitionEquiv r hr (Sum.inr i) = i.val := rfl

variable (R : Type*) [CommRing R]

/--
概要：自由な関数加群をピボット側と残りの側の直積に分解する実際の線形同型。
方針：添字の同型による変数変換と直和添字の関数の直積分解を合成する。
規約：KST §5、Stacks 080Z, Lemma 15.8.9、基礎環は固定する。
使われ方：ピボットの選択と随伴行列の消去を接続する。
-/
def rowPartitionLinearEquiv :
    (m → R) ≃ₗ[R] (ι → R) × ({i : m // i ∉ Set.range r} → R) :=
  (LinearEquiv.funCongrLeft R R (rowPartitionEquiv r hr)).trans
    (LinearEquiv.sumArrowLequivProdArrow ι {i : m // i ∉ Set.range r} R R)

/--
概要：行分解と行列の線形写像の合成は、選んだ行と残りの行の二つの行列の積写像。
方針：二つの成分の各係数を計算する。
規約：KST §5、Stacks 080Z, Lemma 15.8.9、行列の列の添字は有限。
使われ方：任意のピボット行を最初の直和因子に移す。
-/
theorem rowPartitionLinearEquiv_comp_mulVecLin {n : Type*} [Fintype n]
    (A : Matrix m n R) :
    (rowPartitionLinearEquiv r hr R).toLinearMap.comp A.mulVecLin =
      (A.submatrix r id).mulVecLin.prod
        (A.submatrix (fun i : {i : m // i ∉ Set.range r} => i.val) id).mulVecLin := by
  apply LinearMap.ext
  intro x
  apply Prod.ext <;> funext i
  · change ∑ j, A (r i) j * x j = ∑ j, A (r i) (id j) * x j
    rfl
  · change ∑ j, A i.val j * x j = ∑ j, A i.val (id j) * x j
    rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
