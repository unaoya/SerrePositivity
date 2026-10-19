module

public import SerrePositivity.EInfinity.IntervalCuts.CoInsertionActionSums
public import SerrePositivity.EInfinity.IntervalCuts.CochainFaceCutSums

/-!
# 実際の区間余演算を指定出力へ代入した値の有限和

概要：Berger–Fresse §2.2.6・§3.1 の実際の cochainAction を指定出力へ代入する。
方針：実際の全入力面の共通切断和を余代入の有限和評価へ渡す。
規約：全 arity・全語次数・全入力面、nullary の余代入も含む。
使われ方：部分合成則の右辺を二段切断上の有限和へ移す内側評価。
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

/-- 概要：実際の内側余演算の指定出力への代入は全非零面切断の符号付き和（BF §3.1）。
方針：語基底と指定面での実際の複体射の切断和を一般の余代入評価へ代入する。
規約：係数交換の符号は内側語次数と元の前方出力次数で決まる。
使われ方：実際の二段作用の右辺の内側切断和。 -/
lemma tensorCoInsertionAction_cochain_basis_sum {m n e : ℕ} (v : BasisWord n e)
    (i : Fin (m + 1)) (f : Fin (m + 1) → Simplex) (z : ℤ)
    (hz : -(e : ℤ) + (-(tupleDegree i.val (prefixFamily f i) : ℤ) +
      (-(simplexDegree (f i) : ℤ) + -(tupleDegree (m - i.val) (suffixFamily f i) : ℤ))) = z) :
    (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)).f z
      (ιTensorObj (complex A n) (power (interval A) (m + 1)) (-(e : ℤ))
        (-(tupleDegree i.val (prefixFamily f i) : ℤ) +
          (-(simplexDegree (f i) : ℤ) + -(tupleDegree (m - i.val) (suffixFamily f i) : ℤ)))
        z hz ((complexXIso A n e).inv (basis A n e (ULift.up v)) ⊗ₜ[A]
          tensorVectorAt A (m + 1) f _ (by have := tupleDegree_family_blocks f i; omega))) =
      (-(e : ℤ) * -(prefixDegree (m + 1) f i : ℤ)).negOnePow •
        ∑ a : FaceCut v (f i), a.coefficient •
          tensorVectorAt A (m + n) (insertionFamily f a.output i) z (by
            rw [tupleDegree_insertionFamily]; have := a.output_tupleDegree; omega) := by
  have hg (a : FaceCut v (f i)) : -(tupleDegree n a.output : ℤ) =
      -(e : ℤ) + -(simplexDegree (f i) : ℤ) := by
    rw [a.output_tupleDegree]
    omega
  have H := tensorCoInsertionAction_face_sum_apply A (complex A n) m n i (cochainAction A n)
    (-(e : ℤ)) z f (fun a : FaceCut v (f i) => a.output) hz
    ((complexXIso A n e).inv (basis A n e (ULift.up v))) hg
    (fun a => a.coefficient)
    (by exact cochainAction_basis_face_cut_sum A v (f i) _ rfl)
  exact H

end SerrePositivity.EInfinity.IntervalCuts
