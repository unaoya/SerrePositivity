module

public import SerrePositivity.EInfinity.AlexanderWhitney.CochainDiagonal
public import SerrePositivity.EInfinity.AlexanderWhitney.FiniteCuts
public import SerrePositivity.EInfinity.NegativeTensor.Associativity

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

namespace SerrePositivity.EInfinity.AlexanderWhitney

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped Simplicial TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：整数 AW 対角は頂点を群状元へ送る（Berger–Fresse §1.1.4）。
方針：次数零の切断は一つであり両側が元の頂点になることを使う。
規約：自然数模型からの標準同型で頂点を指定する。
使われ方：単位演算の対角を計算する。 -/
lemma cochainDiagonal_vertex (X : SSet.{0}) (x : X _⦋0⦌) :
    (cochainDiagonal A X).f 0
      ((NegativeTensor.xIso (chains A X) 0).inv (generator A X 0 x)) =
    ιTensorObj (cochains A X) (cochains A X) 0 0 0 (by omega)
      ((NegativeTensor.xIso (chains A X) 0).inv (generator A X 0 x) ⊗ₜ[A]
        (NegativeTensor.xIso (chains A X) 0).inv (generator A X 0 x)) := by
  have hd := cochainDiagonal_f_neg A X 0
  have hv := congrArg (fun f => f
    ((NegativeTensor.xIso (chains A X) 0).inv (generator A X 0 x))) hd
  change (cochainDiagonal A X).f 0
    ((NegativeTensor.xIso (chains A X) 0).inv (generator A X 0 x)) =
    NegativeTensor.degreeMap (chains A X) (chains A X) 0
      ((diagonal A X).f 0 ((NegativeTensor.xIso (chains A X) 0).hom
        ((NegativeTensor.xIso (chains A X) 0).inv (generator A X 0 x)))) at hv
  rw [Iso.inv_hom_id_apply] at hv
  rw [hv]
  have hz : (diagonal A X).f 0 (generator A X 0 x) =
      ιTensorObj (chains A X) (chains A X) 0 0 0 (by omega)
        (generator A X 0 x ⊗ₜ[A] generator A X 0 x) := by
    have he : (diagonal A X).f 0 = component A X 0 0 0 (by omega) ≫
        ιTensorObj (chains A X) (chains A X) 0 0 0 (by omega) := by
      rw [diagonal_f_eq_sum_cuts]
      exact Finset.sum_eq_single 0
        (fun b _ hb => (hb (by
          apply Fin.ext
          have := b.isLt
          omega)).elim)
        (fun h => (h (Finset.mem_univ 0)).elim)
    rw [he]
    simp only [ModuleCat.comp_apply, component_generator, cut_zero]
  rw [hz, NegativeTensor.degreeMap_ι_tmul]
  rfl

end SerrePositivity.EInfinity.AlexanderWhitney
