module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.IteratedEdgeCutSums

/-!
模型。文献の定義との比較は後で
# 二段切断で添字付けた実際の二段余作用

概要：Berger–Fresse §2.2.6・§3.1 の実際の全右辺を二段切断上の整数係数和で表す。
方針：反復和を有限同値で移し、二つの Koszul 符号を自然数指数にまとめる。
規約：内側 arity 零も含み、合成側との係数一致はここでは仮定しない。
使われ方：合成側と同じ全出力族・有限添字で一般の符号等式を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

namespace NestedEdgeCut

/-- 概要：二段切断の全出力次数は全 arity で内外語次数と一の和（BF §2.2.3）。
方針：外側の全次数と内側による置換の次数差を評価する。
規約：内側 arity の正性を要求しない。
使われ方：実際の右辺の各面テンソルを同じ整数次数で読む。 -/
lemma outputFamily_tupleDegree_all {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d}
    {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {i : Fin (m + 1)} (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (m + n) a.outputFamily = d + e + 1 := by
  rw [a.outputFamily_eq_insertion, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_insertionFamily]
  have := a.innerOutputFamily_tupleDegree
  have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u a.val.1 a.property.1
  have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_family_blocks (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1) i
  omega

/-- 概要：実際の二段作用の切断係数（BF §2.2.6・§3.1）。
方針：内外係数と前方出力の二交換をまとめ、内外の切断符号を掛ける。
規約：係数環へ送る前の整数で、頂点入力の内側符号は一。
使われ方：合成符号と合成切断符号の積に比較する右辺の係数。 -/
def actionCoefficient {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e}
    {i : Fin (m + 1)} (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v i) : ℤ :=
  (-1 : ℤ) ^ (d * e + e * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree (m + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1) i) *
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val a.val.1 * (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.faceCutEquiv u v i a).2.coefficient

/-- 概要：二つの整数次数の交換符号は二段切断係数に一致（BF §3.1）。
方針：負次数の積を自然数の積へ戻し、二つの冪をまとめる。
規約：元の内外切断符号をそのまま保持する。
使われ方：実際の複体射の Koszul 評価と整数切断係数を接続する。 -/
lemma actionCoefficient_eq {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d}
    {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {i : Fin (m + 1)} (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v i) :
    a.actionCoefficient =
      ((-(d : ℤ) * -(e : ℤ)).negOnePow : ℤ) *
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val a.val.1 *
          (((-(e : ℤ) * -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree (m + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u a.val.1) i : ℤ)).negOnePow :
            ℤ) * (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.faceCutEquiv u v i a).2.coefficient)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.actionCoefficient, neg_mul_neg, ← Nat.cast_mul, Int.coe_negOnePow_natCast,
    pow_add]
  ring

end NestedEdgeCut

/-- 概要：辺入力での実際の全二段作用は二段切断の整数係数和（BF §2.2.6・§3.1）。
方針：反復切断和を一重和へ移し、全出力族と交換係数を照合する。
規約：内側 arity 零を含む全 arity と全語次数。
使われ方：部分合成則の左右を同じテンソル和で比較する右辺。 -/
lemma iteratedCochainAction_basis_edge_nested_sum {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (i : Fin (m + 1)) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -1 = z) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.iteratedCochainAction A m n i).f z
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)
        (-(d : ℤ) + -(e : ℤ)) (-1) z hz
        (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (-(d : ℤ)) (-(e : ℤ))
          (-(d : ℤ) + -(e : ℤ)) rfl
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (m + 1) d).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v))) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge)) =
      ∑ a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v i, a.actionCoefficient •
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (m + n) a.outputFamily z (by
          rw [a.outputFamily_tupleDegree_all]; omega) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.iteratedCochainAction_basis_edge_cut_sum]
  simp only [Units.smul_def, Finset.smul_sum, smul_smul]
  let F : (Σ p : {p : Fin (m + 1 + d) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p},
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p.val i)) → (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (m + n)).X z := fun c =>
    (((-(d : ℤ) * -(e : ℤ)).negOnePow : ℤ) * (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val c.1.val *
      (((-(e : ℤ) * -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree (m + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u c.1.val) i : ℤ)).negOnePow : ℤ) *
        c.2.coefficient))) •
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u c.1.val) c.2.output i) z (by
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_insertionFamily]
        have := c.2.output_tupleDegree
        have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u c.1.val c.1.property
        have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_family_blocks (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u c.1.val) i
        omega)
  change (∑ p, ∑ a, F ⟨p, a⟩) = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.sum_faceCuts F]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [F, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.faceCutEquiv, Equiv.coe_fn_mk]
  erw [← a.actionCoefficient_eq]
  congr 1

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
