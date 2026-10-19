module

public import SerrePositivity.EInfinity.IntervalCuts.IteratedCochainAction
public import SerrePositivity.EInfinity.IntervalCuts.CochainInsertionDegrees

/-!
# 実際の二段区間余作用の辺入力の反復切断和

概要：Berger–Fresse §2.2.6・§3.1 の二段余作用の全右辺を実際の有限和へ展開する。
方針：係数交換を評価し、外側の非零切断和の各項へ内側の面切断作用を施す。
規約：全 arity・全語次数を扱い、内外と前方の交換符号を保持する。
使われ方：合成切断作用と同じ二段切断添字へ移す直前の表示。
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

/-- 概要：語基底と辺での実際の余作用は非零辺切断の有限和（BF §2.2.6）。
方針：全入力面の共通和を辺切断との有限同値で添字変更する。
規約：出力の指定整数次数と元の切断符号を保持する。
使われ方：二段作用の外側作用を有限和へ展開する。 -/
lemma cochainAction_basis_edge_nonzero_sum {n d : ℕ} (u : BasisWord n d) (p : ℤ)
    (hp : -(d : ℤ) + -1 = p) :
    (cochainAction A n).f p
      (ιTensorObj (complex A n) (interval A) (-(d : ℤ)) (-1) p hp
        ((complexXIso A n d).inv (basis A n d (ULift.up u)) ⊗ₜ[A] faceVector A edge)) =
      ∑ q : {q : Fin (n + d) // EdgeNondegenerate u.val q},
        edgeSign u.val q.val • tensorVectorAt A n (edgeOutput u q.val) p
          (by rw [edgeOutput_tupleDegree u q.val q.property]; omega) := by
  have H := cochainAction_basis_face_cut_sum A u edge p (by
    rw [simplexDegree_edge]; exact hp)
  rw [faceCutSum] at H
  have hs := (FaceCut.edgeEquiv u).symm.sum_comp (fun a : FaceCut u edge =>
    a.coefficient • tensorVectorAt A n a.output p (by
      rw [a.output_tupleDegree, simplexDegree_edge]; omega))
  simpa only [simplexDegree_edge, Nat.cast_one] using! H.trans hs.symm

/-- 概要：辺上の実際の二段余作用は外側切断と内側面切断の反復和（BF §3.1）。
方針：外側切断和を線形に展開して、各面テンソルへの実際の内側余代入を評価する。
規約：係数交換と指定出力前方の Koszul 符号を双方とも保持する。
使われ方：部分合成則の全右辺と合成切断和の項ごとの比較。 -/
lemma iteratedCochainAction_basis_edge_cut_sum {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (i : Fin (m + 1)) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -1 = z) :
    (iteratedCochainAction A m n i).f z
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A)
        (-(d : ℤ) + -(e : ℤ)) (-1) z hz
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(d : ℤ)) (-(e : ℤ))
          (-(d : ℤ) + -(e : ℤ)) rfl
          ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A] faceVector A edge)) =
      (-(d : ℤ) * -(e : ℤ)).negOnePow •
        ∑ p : {p : Fin (m + 1 + d) // EdgeNondegenerate u.val p},
          edgeSign u.val p.val •
            ((-(e : ℤ) * -(prefixDegree (m + 1) (edgeOutput u p.val) i : ℤ)).negOnePow •
              ∑ a : FaceCut v (edgeOutput u p.val i), a.coefficient •
                tensorVectorAt A (m + n) (insertionFamily (edgeOutput u p.val) a.output i)
                  z (by
                    rw [tupleDegree_insertionFamily]
                    have := a.output_tupleDegree
                    have := edgeOutput_tupleDegree u p.val p.property
                    have := tupleDegree_family_blocks (edgeOutput u p.val) i
                    omega)) := by
  rw [iteratedCochainAction_apply, cochainAction_basis_edge_nonzero_sum A u _ rfl]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_zsmul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  exact tensorCoInsertionAction_cochain_basis_sum_at A v i (edgeOutput u p.val)
    (-(d : ℤ) + -1) z (by rw [edgeOutput_tupleDegree u p.val p.property]; omega) (by omega)

end SerrePositivity.EInfinity.IntervalCuts
