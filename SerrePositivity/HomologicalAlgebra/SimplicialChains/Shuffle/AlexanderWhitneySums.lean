module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.AlexanderWhitneyTerms
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.PathCutSums
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.ChainDiagonal

/-!
# AW 対角に適用した shuffle 和の分割

概要：Berger–Fresse §1.1.4 の経路分割によって AW 対角の shuffle 和を展開する。
方針：全 AW 成分を経路の切断頂点で添字付け、符号付き分割和へ移す。
規約：値は実際の正規化鎖のテンソル複体の全次数 p+q に入る。
使われ方：shuffle の AW 余代数射性の両辺を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial _root_.TensorProduct

variable (A : Type u) [CommRing A]

local instance _root_.SerrePositivity.SimplicialChains.Shuffle.instFiniteSubtypeProdNatEqHAddFstSnd_serrePositivity (n : ℕ) : Finite {i : ℕ × ℕ // i.1 + i.2 = n} :=
  inferInstanceAs (Finite ((fun i : ℕ × ℕ => i.1 + i.2) ⁻¹' {n}))

local instance _root_.SerrePositivity.SimplicialChains.Shuffle.instFintypeSubtypeProdNatEqHAddFstSnd_serrePositivity (n : ℕ) : Fintype {i : ℕ × ℕ // i.1 + i.2 = n} := Fintype.ofFinite _

private def pathDegreeEquiv {p q : ℕ} (s : ShufflePath p q) :
    Fin (p + q + 1) ≃ {i : ℕ × ℕ // i.1 + i.2 = p + q} where
  toFun k := ⟨((s.horizontal k).val + (s.vertical k).val,
    (p - (s.horizontal k).val) + (q - (s.vertical k).val)), by omega⟩
  invFun i := ⟨i.val.1, by have hi := i.property; omega⟩
  left_inv k := Fin.ext (s.coordinate_sum k)
  right_inv i := by
    apply Subtype.ext
    apply Prod.ext
    · exact s.coordinate_sum ⟨i.val.1, by have hi := i.property; omega⟩
    · have hc := s.coordinate_sum ⟨i.val.1, by have hi := i.property; omega⟩
      have hi := i.property
      dsimp at hc ⊢
      omega

/-- 概要：分割データの前後の shuffle 単体のテンソル項（BF §1.1.4）。
方針：入力を各切断座標で制限し、前後の shuffle を全テンソル次数へ含める。
規約：前半・後半の次数和は元の p+q。
使われ方：AW 対角の shuffle 和の分割表示。 -/
def cutTensorTerm (X Y : SSet.{0}) {p q : ℕ} (d : _root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData p q)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (HomologicalComplex.tensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y))
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y))).X (p + q) :=
  ιTensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y))
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)) (d.1.val + d.2.1.val)
    ((p - d.1.val) + (q - d.2.1.val)) (p + q) (by omega)
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (d.1.val + d.2.1.val)
        (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y d.2.2.1
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 d.1.val (by omega))
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut Y y 0 d.2.1.val (by omega))) ⊗ₜ[A]
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) ((p - d.1.val) + (q - d.2.1.val))
        (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y d.2.2.2
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x d.1.val (p - d.1.val) (by omega))
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut Y y d.2.1.val (q - d.2.1.val) (by omega))))

/-- 概要：一経路の AW 対角は全切断点のテンソル項の和（BF §1.1.4）。
方針：次数分割の有限和を切断頂点で添字付け直し、項別 AW 公式を使う。
規約：出力はテンソル複体の全次数 p+q。
使われ方：正規化 shuffle 和全体の対角を計算する。 -/
lemma diagonal_simplex_sum (X Y : SSet.{0}) {p q : ℕ} (s : ShufflePath p q)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A (X ⊗ Y)).f (p + q)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (X ⊗ Y) (p + q) (_root_.SerrePositivity.SimplicialChains.Shuffle.simplex X Y s x y)) =
      ∑ k : Fin (p + q + 1), _root_.SerrePositivity.SimplicialChains.Shuffle.cutTensorTerm A X Y (_root_.SerrePositivity.SimplicialChains.Shuffle.splitPath s k) x y := by
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree A (X ⊗ Y) (p + q) _ = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonalDegree_eq_sum]
  change (∑ i : {i : ℕ × ℕ // i.1 + i.2 = p + q},
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A (X ⊗ Y) (p + q) i.val.1 i.val.2 i.property ≫
      ιTensorObj _ _ i.val.1 i.val.2 (p + q) i.property) _ = _
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.comp_apply]
  symm
  apply Fintype.sum_equiv (_root_.SerrePositivity.SimplicialChains.Shuffle.pathDegreeEquiv s)
  intro k
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.pathDegreeEquiv, Equiv.coe_fn_mk]
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.aw_component_simplex]
  rfl

/-- 概要：shuffle 和の AW 対角を分割データの符号付き和で表す（BF §1.1.4）。
方針：対角を有限和に分配し、切断付き経路の符号付き添字替えを使う。
規約：一般の小さい単体集合と任意の可換係数環を使う。
使われ方：前半・後半の shuffle 和のテンソルへの集約。 -/
lemma diagonal_value_split_sum (X Y : SSet.{0}) (p q : ℕ)
    (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A (X ⊗ Y)).f (p + q) (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x y) =
      ∑ d : _root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData p q,
        ((-1 : ℤ) ^ (d.2.1.val * (p - d.1.val)) *
          (d.2.2.1.sign : ℤ) * (d.2.2.2.sign : ℤ)) • _root_.SerrePositivity.SimplicialChains.Shuffle.cutTensorTerm A X Y d x y := by
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.value, map_sum, map_zsmul, _root_.SerrePositivity.SimplicialChains.Shuffle.diagonal_simplex_sum, Finset.smul_sum]
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.signed_sum_pathCut]
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.splitPath_joinPath]

/-- 概要：shuffle 和の AW 対角は前後の shuffle 和のテンソルである（BF §1.1.4）。
方針：分割データの和を切断座標と二経路の和へ分解し、テンソルの双線形性でまとめる。
規約：交差符号は前半垂直次数と後半水平次数の積である。
使われ方：一般 shuffle の AW 余代数射性の次数ごとの生成元公式。 -/
lemma diagonal_value (X Y : SSet.{0}) (p q : ℕ) (x : X _⦋p⦌) (y : Y _⦋q⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A (X ⊗ Y)).f (p + q) (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y p q x y) =
      ∑ r : Fin (p + 1), ∑ t : Fin (q + 1),
        (-1 : ℤ) ^ (t.val * (p - r.val)) •
          ιTensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y))
            (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)) (r.val + t.val)
            ((p - r.val) + (q - t.val)) (p + q) (by omega)
            (_root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y r.val t.val
                (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x 0 r.val (by omega))
                (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut Y y 0 t.val (by omega)) ⊗ₜ[A]
              _root_.SerrePositivity.SimplicialChains.Shuffle.value A X Y (p - r.val) (q - t.val)
                (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut X x r.val (p - r.val) (by omega))
                (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut Y y t.val (q - t.val) (by omega))) := by
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.diagonal_value_split_sum]
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData, Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.cutTensorTerm, _root_.SerrePositivity.SimplicialChains.Shuffle.value, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_sum, map_zsmul,
    Finset.smul_sum, smul_smul, mul_assoc]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  ring

end SerrePositivity.SimplicialChains.Shuffle
