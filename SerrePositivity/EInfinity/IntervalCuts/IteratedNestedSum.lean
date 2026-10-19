module

public import SerrePositivity.EInfinity.IntervalCuts.IteratedEdgeCutSums

/-!
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

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

namespace NestedEdgeCut

/-- 概要：二段切断の全出力次数は全 arity で内外語次数と一の和（BF §2.2.3）。
方針：外側の全次数と内側による置換の次数差を評価する。
規約：内側 arity の正性を要求しない。
使われ方：実際の右辺の各面テンソルを同じ整数次数で読む。 -/
lemma outputFamily_tupleDegree_all {m n d e : ℕ} {u : BasisWord (m + 1) d}
    {v : BasisWord n e} {i : Fin (m + 1)} (a : NestedEdgeCut u v i) :
    tupleDegree (m + n) a.outputFamily = d + e + 1 := by
  rw [a.outputFamily_eq_insertion, tupleDegree_insertionFamily]
  have := a.innerOutputFamily_tupleDegree
  have := edgeOutput_tupleDegree u a.val.1 a.property.1
  have := tupleDegree_family_blocks (edgeOutput u a.val.1) i
  omega

/-- 概要：実際の二段作用の切断係数（BF §2.2.6・§3.1）。
方針：内外係数と前方出力の二交換をまとめ、内外の切断符号を掛ける。
規約：係数環へ送る前の整数で、頂点入力の内側符号は一。
使われ方：合成符号と合成切断符号の積に比較する右辺の係数。 -/
def actionCoefficient {m n d e : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord n e}
    {i : Fin (m + 1)} (a : NestedEdgeCut u v i) : ℤ :=
  (-1 : ℤ) ^ (d * e + e * prefixDegree (m + 1) (edgeOutput u a.val.1) i) *
    edgeSign u.val a.val.1 * (faceCutEquiv u v i a).2.coefficient

/-- 概要：二つの整数次数の交換符号は二段切断係数に一致（BF §3.1）。
方針：負次数の積を自然数の積へ戻し、二つの冪をまとめる。
規約：元の内外切断符号をそのまま保持する。
使われ方：実際の複体射の Koszul 評価と整数切断係数を接続する。 -/
lemma actionCoefficient_eq {m n d e : ℕ} {u : BasisWord (m + 1) d}
    {v : BasisWord n e} {i : Fin (m + 1)} (a : NestedEdgeCut u v i) :
    a.actionCoefficient =
      ((-(d : ℤ) * -(e : ℤ)).negOnePow : ℤ) *
        (edgeSign u.val a.val.1 *
          (((-(e : ℤ) * -(prefixDegree (m + 1) (edgeOutput u a.val.1) i : ℤ)).negOnePow :
            ℤ) * (faceCutEquiv u v i a).2.coefficient)) := by
  simp only [actionCoefficient, neg_mul_neg, ← Nat.cast_mul, Int.coe_negOnePow_natCast,
    pow_add]
  ring

end NestedEdgeCut

/-- 概要：辺入力での実際の全二段作用は二段切断の整数係数和（BF §2.2.6・§3.1）。
方針：反復切断和を一重和へ移し、全出力族と交換係数を照合する。
規約：内側 arity 零を含む全 arity と全語次数。
使われ方：部分合成則の左右を同じテンソル和で比較する右辺。 -/
lemma iteratedCochainAction_basis_edge_nested_sum {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (i : Fin (m + 1)) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -1 = z) :
    (iteratedCochainAction A m n i).f z
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A)
        (-(d : ℤ) + -(e : ℤ)) (-1) z hz
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(d : ℤ)) (-(e : ℤ))
          (-(d : ℤ) + -(e : ℤ)) rfl
          ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A] faceVector A edge)) =
      ∑ a : NestedEdgeCut u v i, a.actionCoefficient •
        tensorVectorAt A (m + n) a.outputFamily z (by
          rw [a.outputFamily_tupleDegree_all]; omega) := by
  rw [iteratedCochainAction_basis_edge_cut_sum]
  simp only [Units.smul_def, Finset.smul_sum, smul_smul]
  let F : (Σ p : {p : Fin (m + 1 + d) // EdgeNondegenerate u.val p},
      FaceCut v (edgeOutput u p.val i)) → (power (interval A) (m + n)).X z := fun c =>
    (((-(d : ℤ) * -(e : ℤ)).negOnePow : ℤ) * (edgeSign u.val c.1.val *
      (((-(e : ℤ) * -(prefixDegree (m + 1) (edgeOutput u c.1.val) i : ℤ)).negOnePow : ℤ) *
        c.2.coefficient))) •
      tensorVectorAt A (m + n) (insertionFamily (edgeOutput u c.1.val) c.2.output i) z (by
        rw [tupleDegree_insertionFamily]
        have := c.2.output_tupleDegree
        have := edgeOutput_tupleDegree u c.1.val c.1.property
        have := tupleDegree_family_blocks (edgeOutput u c.1.val) i
        omega)
  change (∑ p, ∑ a, F ⟨p, a⟩) = _
  rw [NestedEdgeCut.sum_faceCuts F]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [F, NestedEdgeCut.faceCutEquiv, Equiv.coe_fn_mk]
  erw [← a.actionCoefficient_eq]
  congr 1

end SerrePositivity.EInfinity.IntervalCuts
