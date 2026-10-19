module

public import SerrePositivity.EInfinity.IntervalCuts.IteratedVertexAction

/-!
# 元の両頂点における部分合成則

概要：Berger–Fresse §2.2.6・§3.1 の実際の部分合成則を元の頂点生成元で証明する。
方針：内外語次数が正なら零、双方零なら一定頂点族として両辺を照合する。
規約：正の内側 arity、全内外語次数、両頂点。
使われ方：辺生成元での部分合成則と合わせ、全複体射へ線形延長する。
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

/-- 概要：語基底と元の両頂点で実際の合成余作用は二段作用に一致（BF §2.2.6・§3.1）。
方針：正の外側次数・正の内側次数・内外次数零を分けて実際の値を比較する。
規約：正の内側 arity、全語次数と両頂点。
使われ方：全整数複体射の部分合成則の頂点生成元での入力。 -/
lemma cochainAction_composition_basis_vertex_eq_iterated {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (i : Fin (m + 1)) (hn : 0 < n)
    (b : Fin 2) :
    ((complexPartialComposition A m n i ▷ interval A) ≫ cochainAction A (m + n)).f
      (-((d + e : ℕ) : ℤ))
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A)
        (-((d + e : ℕ) : ℤ)) 0 (-((d + e : ℕ) : ℤ)) (by omega)
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(d : ℤ)) (-(e : ℤ))
          (-((d + e : ℕ) : ℤ)) (by omega)
          ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A]
          faceVector A (vertex b))) =
    (iteratedCochainAction A m n i).f (-((d + e : ℕ) : ℤ))
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A)
        (-((d + e : ℕ) : ℤ)) 0 (-((d + e : ℕ) : ℤ)) (by omega)
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(d : ℤ)) (-(e : ℤ))
          (-((d + e : ℕ) : ℤ)) (by omega)
          ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A]
          faceVector A (vertex b))) := by
  refine (cochainAction_composition_basis_vertex A u v i b).trans ?_
  by_cases hd : d = 0
  · subst d
    by_cases he : e = 0
    · subst e
      exact (vertexComponent_composition_zero A u v i hn b).trans
        (iteratedCochainAction_basis_vertex_zero A u v i b).symm
    · have hL : vertexComponent A (m + n) (0 + e) b (compositionOnWords A u v i) = 0 := by
        rw [vertexComponent_eq_zero_of_positive A (m + n) (0 + e) b (by omega),
          LinearMap.zero_apply]
      calc
        _ = 0 := hL
        _ = _ := (iteratedCochainAction_basis_vertex_inner_positive A u v i b (by omega)
          (-((0 + e : ℕ) : ℤ)) (by omega)).symm
  · have hL : vertexComponent A (m + n) (d + e) b (compositionOnWords A u v i) = 0 := by
      rw [vertexComponent_eq_zero_of_positive A (m + n) (d + e) b (by omega),
        LinearMap.zero_apply]
    exact hL.trans (iteratedCochainAction_basis_vertex_outer_positive A u v i b (by omega)).symm

end SerrePositivity.EInfinity.IntervalCuts
