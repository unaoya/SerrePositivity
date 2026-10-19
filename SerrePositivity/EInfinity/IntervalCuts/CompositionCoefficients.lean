module

public import SerrePositivity.EInfinity.IntervalCuts.NonpivotCompositionSigns
public import SerrePositivity.EInfinity.IntervalCuts.VertexCompositionSigns
public import SerrePositivity.EInfinity.IntervalCuts.CompositeCochainAction

/-!
# 全二段切断の係数一致と実際の辺入力の部分合成則

概要：Berger–Fresse §2.2.6・§3.1 の三分岐の係数を束ね、実際の左右辺を比較する。
方針：共通有限添字の各係数を同定し、両辺の実際の辺入力評価を連結する。
規約：正の内側 arity、任意の可換環と全内外語次数。
使われ方：全整数複体射の部分合成則の辺生成元での入力。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

namespace NestedEdgeCut

/-- 概要：全二段切断で合成側と二段作用の一般係数が一致（BF §2.2.6・§3.1）。
方針：内側頂点・切断点色の辺・二出現色の辺の三分岐を合わせる。
規約：正の内側 arity、全内外語次数。
使われ方：実際の合成辺成分の全有限和の係数を置き換える。 -/
lemma compositionCoefficient {m n d e : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord n e}
    {k : Fin (m + 1)} (a : NestedEdgeCut u v k) (hn : 0 < n) :
    compositionSign u v k a.partition *
      edgeSign (compositeBasisWord u v k a.partition hn).val a.compositePosition =
        a.actionCoefficient := by
  cases ha : a.val.2 with
  | none => exact a.compositionCoefficient_vertex hn ha
  | some q =>
    by_cases hp : u.val a.val.1 = k
    · exact a.compositionCoefficient_pivot hn q ha hp
    · exact a.compositionCoefficient_nonpivot hn q ha hp

end NestedEdgeCut

variable (A : Type u) [CommRing A]

/-- 概要：実際の合成辺成分は二段作用の係数を持つ全出力テンソル和（BF §2.2.6）。
方針：既存の同じ有限添字・全出力族の和で各係数を一般等式により置き換える。
規約：正の内側 arity、任意の可換環。
使われ方：部分合成則の実際の左辺と右辺の同じ有限和。 -/
lemma edgeComponent_composition_action_sum {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (i : Fin (m + 1)) (hn : 0 < n) :
    edgeComponent A (m + n) (d + e) (compositionOnWords A u v i) =
      ∑ a : NestedEdgeCut u v i, a.actionCoefficient •
        tensorVectorOfDegree A (m + n) (d + e + 1) a.outputFamily
          a.outputFamily_tupleDegree_all := by
  rw [edgeComponent_composition_nested_output_sum A u v i hn]
  apply Finset.sum_congr rfl
  intro a _
  rw [a.compositionCoefficient hn]

/-- 概要：語基底と辺で実際の部分合成余作用は実際の二段作用に一致（BF §2.2.6・§3.1）。
方針：両辺を同じ係数・全出力族の二段切断和へ移し、中間次数の表示を合わせる。
規約：正の内側 arity、全内外語次数、実際の整数複体射の評価。
使われ方：辺生成元と語基底から線形延長する部分合成則。 -/
lemma cochainAction_composition_basis_edge_eq_iterated {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (i : Fin (m + 1)) (hn : 0 < n) :
    ((complexPartialComposition A m n i ▷ interval A) ≫ cochainAction A (m + n)).f
      (-((d + e + 1 : ℕ) : ℤ))
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A)
        (-((d + e : ℕ) : ℤ)) (-1) (-((d + e + 1 : ℕ) : ℤ)) (by omega)
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(d : ℤ)) (-(e : ℤ))
          (-((d + e : ℕ) : ℤ)) (by omega)
          ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A] faceVector A edge)) =
    (iteratedCochainAction A m n i).f (-((d + e + 1 : ℕ) : ℤ))
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A)
        (-((d + e : ℕ) : ℤ)) (-1) (-((d + e + 1 : ℕ) : ℤ)) (by omega)
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(d : ℤ)) (-(e : ℤ))
          (-((d + e : ℕ) : ℤ)) (by omega)
          ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A] faceVector A edge)) := by
  rw [cochainAction_composition_basis_edge, edgeComponent_composition_action_sum A u v i hn]
  have H := iteratedCochainAction_basis_edge_nested_sum A u v i
    (-((d + e + 1 : ℕ) : ℤ)) (by omega)
  have hx := SerrePositivity.DifferentialGraded.nested_left_apply
    (complex A (m + 1)) (complex A n) (interval A) (-(d : ℤ)) (-(e : ℤ)) (-1)
    (-((d + e : ℕ) : ℤ)) (-((d + e + 1 : ℕ) : ℤ)) (by omega) (by omega)
    ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)))
    ((complexXIso A n e).inv (basis A n e (ULift.up v))) (faceVector A edge)
  have H' := congrArg (fun x => (iteratedCochainAction A m n i).f
    (-((d + e + 1 : ℕ) : ℤ)) x) hx
  exact H.symm.trans H'.symm

end SerrePositivity.EInfinity.IntervalCuts
