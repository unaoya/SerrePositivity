module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainDiagonal
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.FiniteCuts
public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Associativity

/-!
# 整数 AW 対角の頂点での値

概要：Berger–Fresse §1.1.4 の対角は零単体をその自己テンソルへ送る。
方針：鎖 AW の切断和を次数零で評価して整数模型へ移す。
規約：テンソル複体への零・零次数の包含を明示する。
使われ方：Barratt–Eccles の Hopf 対角の単位保存則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped _root_.Simplicial _root_.TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：整数 AW 対角は頂点を群状元へ送る（Berger–Fresse §1.1.4）。
方針：次数零の切断は一つであり両側が元の頂点になることを使う。
規約：自然数模型からの標準同型で頂点を指定する。
使われ方：単位演算の対角を計算する。 -/
lemma cochainDiagonal_vertex (X : SSet.{0}) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X).f 0
      ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) 0).inv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x)) =
    ιTensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X) 0 0 0 (by omega)
      ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) 0).inv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x) ⊗ₜ[A]
        (_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) 0).inv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x)) := by
  have hd := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_f_neg A X 0
  have hv := congrArg (fun f => f
    ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) 0).inv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x))) hd
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X).f 0
    ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) 0).inv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x)) =
    _root_.SerrePositivity.NegativeTensor.degreeMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) 0
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X).f 0 ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) 0).hom
        ((_root_.SerrePositivity.NegativeTensor.xIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) 0).inv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x)))) at hv
  rw [Iso.inv_hom_id_apply] at hv
  rw [hv]
  have hz : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X).f 0 (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x) =
      ιTensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) 0 0 0 (by omega)
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x ⊗ₜ[A] _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A X 0 x) := by
    have he : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X).f 0 = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X 0 0 0 (by omega) ≫
        ιTensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) 0 0 0 (by omega) := by
      rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_f_eq_sum_cuts]
      exact Finset.sum_eq_single 0
        (fun b _ hb => (hb (by
          apply Fin.ext
          have := b.isLt
          omega)).elim)
        (fun h => (h (Finset.mem_univ 0)).elim)
    rw [he]
    simp only [ModuleCat.comp_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cut_zero]
  rw [hz, _root_.SerrePositivity.NegativeTensor.degreeMap_ι_tmul]
  rfl

end SerrePositivity.SimplicialChains.AlexanderWhitney
