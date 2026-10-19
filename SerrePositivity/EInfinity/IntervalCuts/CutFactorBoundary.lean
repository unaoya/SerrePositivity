module

public import SerrePositivity.EInfinity.IntervalCuts.CutEndpointValues
public import SerrePositivity.EInfinity.IntervalCuts.CutDeletionSigns

/-!
# 反復色一因子の符号付き境界と二つの削除係数

概要：Berger–Fresse §2.2.7 の反復色の辺の境界を左右の文字削除係数で表す。
方針：各因子の実際の端点公式と、実際の削除語の切断符号の一致を組み合わせる。
規約：切断点を残す非零切断を対象とし、二つの削除後の切断位置を明示する。
使われ方：全反復色の境界和を χ の削除による切断和へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

variable (A : Type u) [CommRing A]

/-- 概要：切断符号付きの反復色の境界は二つの実際の削除係数で重み付けされる（BF §2.2.7）。
方針：因子境界を二端点の差へ展開し、左右の削除符号を各端点係数へ代入する。
規約：両削除後の位置が同じ元の切断点へ戻ることを要求する。
使われ方：反復色の全因子を足した境界和と削除和の比較。 -/
lemma cut_factor_boundary {n d : ℕ} (u : BasisWord n (d + 1))
    (a b : Fin (n + (d + 1))) (qL qR : Fin (n + d))
    (hq : b.succAbove qR = a.succAbove qL)
    (h : EdgeNondegenerate u.val (a.succAbove qL)) (hab : a < b) (hua : u.val a = u.val b) :
    let f := edgeOutput u (a.succAbove qL)
    let hk := edgeOutput_repeat_color u (a.succAbove qL) h a ⟨b, ne_of_gt hab, hua.symm⟩
    edgeSign u.val (a.succAbove qL) • tensorBoundaryTerm A n f (u.val a) =
      (deletionCoefficient u.val a * edgeSign (erase u.val a) qL) •
          endpointTensor A n f (u.val a) hk 1 +
      (deletionCoefficient u.val b * edgeSign (erase u.val b) qR) •
          endpointTensor A n f (u.val a) hk 0 := by
  dsimp only
  have hk := edgeOutput_repeat_color u (a.succAbove qL) h a ⟨b, ne_of_gt hab, hua.symm⟩
  rw [tensorBoundaryTerm_eq_endpoints A n (edgeOutput u (a.succAbove qL)) (u.val a) hk,
    smul_smul, smul_sub, sub_eq_add_neg, ← neg_smul]
  have hL := edgeSign_erase_left_boundary u a qL h ⟨b, hab, hua.symm⟩
  have hR := edgeSign_erase_right_boundary u b a qR (by rw [hq]; exact h) hab hua
  rw [hq] at hR
  change edgeSign u.val (a.succAbove qL) *
    (-1 : ℤ) ^ prefixDegree n (edgeOutput u (a.succAbove qL)) (u.val a) = _ at hL
  change -(edgeSign u.val (a.succAbove qL) *
    (-1 : ℤ) ^ prefixDegree n (edgeOutput u (a.succAbove qL)) (u.val a)) = _ at hR
  apply congrArg₂ (fun x y => x + y)
  · exact congrArg (fun c : ℤ => c • _) hL
  · exact congrArg (fun c : ℤ => c • _) hR

end SerrePositivity.EInfinity.IntervalCuts
