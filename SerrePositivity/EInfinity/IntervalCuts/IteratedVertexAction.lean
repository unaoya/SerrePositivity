module

public import SerrePositivity.EInfinity.IntervalCuts.VertexBasisEvaluation
public import SerrePositivity.EInfinity.IntervalCuts.InsertionVertexValues
public import SerrePositivity.EInfinity.IntervalCuts.IteratedCochainAction

/-!
# 元の頂点入力での実際の二段余作用

概要：Berger–Fresse §2.2.6・§3.1 の二段作用を元の頂点入力で評価する。
方針：外側頂点成分を評価してから一定頂点族への内側余代入を使う。
規約：内側 arity 零も含む全 arity と両頂点。
使われ方：実際の部分合成則の元の頂点入力における右辺。
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

/-- 概要：実際の二段作用を指定した二つの中間整数次数で評価する（BF §3.1）。
方針：中間次数の等式を消去して既存の三重斉次評価を使う。
規約：各中間次数は対応する二入力次数の和。
使われ方：頂点入力で r+0 を初めから r の表示で扱う。 -/
lemma iteratedCochainAction_apply_of_sums (m n : ℕ) (i : Fin (m + 1)) (r s t l p z : ℤ)
    (hl : r + s = l) (hp : r + t = p) (hz : l + t = z)
    (x : (complex A (m + 1)).X r) (y : (complex A n).X s) (w : (interval A).X t) :
    (iteratedCochainAction A m n i).f z
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A) l t z hz
        (ιTensorObj (complex A (m + 1)) (complex A n) r s l hl (x ⊗ₜ[A] y) ⊗ₜ[A] w)) =
      (r * s).negOnePow •
        (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)).f z
          (ιTensorObj (complex A n) (power (interval A) (m + 1)) s p z (by omega)
            (y ⊗ₜ[A] (cochainAction A (m + 1)).f p
              (ιTensorObj (complex A (m + 1)) (interval A) r t p hp (x ⊗ₜ[A] w)))) := by
  subst l
  subst p
  exact iteratedCochainAction_apply A m n i r s t z hz x y w

/-- 概要：二段作用の頂点入力では外側作用が既存の頂点基底値となる（BF §3.1）。
方針：実際の係数交換・外側評価の式へ面表示の頂点評価を渡す。
規約：全語次数と全 arity。
使われ方：外側正次数なら零、外側次数零なら一定頂点族へ帰着する。 -/
lemma iteratedCochainAction_basis_vertex_component {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (i : Fin (m + 1)) (b : Fin 2) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) = z) :
    (iteratedCochainAction A m n i).f z
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A)
        z 0 z (by omega)
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(d : ℤ)) (-(e : ℤ))
          z hz
          ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A]
          faceVector A (vertex b))) =
      (-(d : ℤ) * -(e : ℤ)).negOnePow •
        (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)).f
          z
          (ιTensorObj (complex A n) (power (interval A) (m + 1)) (-(e : ℤ)) (-(d : ℤ))
            z (by omega)
            ((complexXIso A n e).inv (basis A n e (ULift.up v)) ⊗ₜ[A]
              vertexComponentOnWord A u b)) := by
  have H := iteratedCochainAction_apply_of_sums A m n i (-(d : ℤ)) (-(e : ℤ)) 0
    z (-(d : ℤ)) z hz (by omega) (by omega)
    ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)))
    ((complexXIso A n e).inv (basis A n e (ULift.up v))) (faceVector A (vertex b))
  have HV := congrArg (fun w : (power (interval A) (m + 1)).X (-(d : ℤ)) =>
    (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)).f
      z
      (ιTensorObj (complex A n) (power (interval A) (m + 1)) (-(e : ℤ)) (-(d : ℤ))
        z (by omega)
        ((complexXIso A n e).inv (basis A n e (ULift.up v)) ⊗ₜ[A] w)))
    (cochainAction_basis_vertex_component A u b)
  exact H.trans (congrArg (fun w => (-(d : ℤ) * -(e : ℤ)).negOnePow • w) HV)

/-- 概要：正の外側語次数の二段頂点作用は零（BF §2.2.6・§3.1）。
方針：外側の頂点基底値の零性を二段作用の評価へ渡す。
規約：内側語次数は任意。
使われ方：元の頂点入力の正次数分岐を消す。 -/
lemma iteratedCochainAction_basis_vertex_outer_positive {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (i : Fin (m + 1)) (b : Fin 2)
    (hd : 0 < d) :
    (iteratedCochainAction A m n i).f (-((d + e : ℕ) : ℤ))
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A)
        (-((d + e : ℕ) : ℤ)) 0 (-((d + e : ℕ) : ℤ)) (by omega)
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(d : ℤ)) (-(e : ℤ))
          (-((d + e : ℕ) : ℤ)) (by omega)
          ((complexXIso A (m + 1) d).inv (basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A]
          faceVector A (vertex b))) = 0 := by
  rw [iteratedCochainAction_basis_vertex_component,
    vertexComponentOnWord_eq_zero_of_positive A u hd b]
  simp only [TensorProduct.tmul_zero, map_zero, smul_zero]

/-- 概要：外側次数零の二段頂点作用は一定頂点族への内側余代入（BF §3.1）。
方針：初めから外側出力次数零を指定し、頂点基底値を一定族へ同定する。
規約：内側語次数と arity は任意。
使われ方：内側正次数の零値と次数零の一定値を同じ形で導く。 -/
lemma iteratedCochainAction_basis_vertex_zero_outer {m n e : ℕ}
    (u : BasisWord (m + 1) 0) (v : BasisWord n e) (i : Fin (m + 1)) (b : Fin 2) :
    (iteratedCochainAction A m n i).f (-(e : ℤ))
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A) (-(e : ℤ)) 0 (-(e : ℤ))
        (by omega) (ιTensorObj (complex A (m + 1)) (complex A n) 0 (-(e : ℤ))
          (-(e : ℤ)) (by omega)
          ((complexXIso A (m + 1) 0).inv (basis A (m + 1) 0 (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A]
          faceVector A (vertex b))) =
    (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)).f (-(e : ℤ))
      (ιTensorObj (complex A n) (power (interval A) (m + 1)) (-(e : ℤ)) 0 (-(e : ℤ))
        (by omega) ((complexXIso A n e).inv (basis A n e (ULift.up v)) ⊗ₜ[A]
          tensorVectorAt A (m + 1) (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl))) := by
  have H := iteratedCochainAction_apply_of_sums A m n i 0 (-(e : ℤ)) 0 (-(e : ℤ)) 0
    (-(e : ℤ)) (by omega) rfl (by omega)
    ((complexXIso A (m + 1) 0).inv (basis A (m + 1) 0 (ULift.up u)))
    ((complexXIso A n e).inv (basis A n e (ULift.up v))) (faceVector A (vertex b))
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at H
  have hv : (cochainAction A (m + 1)).f 0
      (ιTensorObj (complex A (m + 1)) (interval A) 0 0 0 rfl
        ((complexXIso A (m + 1) 0).inv (basis A (m + 1) 0 (ULift.up u)) ⊗ₜ[A]
          faceVector A (vertex b))) =
      tensorVectorAt A (m + 1) (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl) :=
    (cochainAction_basis_vertex_component A u b).trans (by rfl)
  exact H.trans (congrArg (fun w : (power (interval A) (m + 1)).X 0 =>
    (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)).f (-(e : ℤ))
      (ιTensorObj (complex A n) (power (interval A) (m + 1)) (-(e : ℤ)) 0 (-(e : ℤ))
        (by omega) ((complexXIso A n e).inv (basis A n e (ULift.up v)) ⊗ₜ[A] w))) hv)

/-- 概要：外側次数零・内側正次数の二段頂点作用は零（BF §2.2.6・§3.1）。
方針：外側の一定頂点族へ正次数の内側作用を代入する。
規約：内側 arity 零を含む。
使われ方：外側頂点値が非零でも全次数が正なら作用は零となる。 -/
lemma iteratedCochainAction_basis_vertex_inner_positive {m n e : ℕ}
    (u : BasisWord (m + 1) 0) (v : BasisWord n e) (i : Fin (m + 1)) (b : Fin 2)
    (he : 0 < e) (z : ℤ) (hz : -(e : ℤ) = z) :
    (iteratedCochainAction A m n i).f z
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A) z 0 z
        (by omega) (ιTensorObj (complex A (m + 1)) (complex A n) 0 (-(e : ℤ))
          z (by omega)
          ((complexXIso A (m + 1) 0).inv (basis A (m + 1) 0 (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n e).inv (basis A n e (ULift.up v))) ⊗ₜ[A]
          faceVector A (vertex b))) = 0 := by
  subst z
  exact (iteratedCochainAction_basis_vertex_zero_outer A u v i b).trans
    (tensorCoInsertionAction_basis_vertex_zero A v he i b)

/-- 概要：内外次数零の二段頂点作用は同じ一定頂点族（BF §2.2.6・§3.1）。
方針：外側の一定頂点族と内側の次数零余代入を評価する。
規約：全 arity と両頂点。
使われ方：元の頂点入力の次数零分岐を閉じる。 -/
lemma iteratedCochainAction_basis_vertex_zero {m n : ℕ}
    (u : BasisWord (m + 1) 0) (v : BasisWord n 0) (i : Fin (m + 1)) (b : Fin 2) :
    (iteratedCochainAction A m n i).f 0
      (ιTensorObj (complex A (m + 1) ⊗ complex A n) (interval A) 0 0 0 rfl
        (ιTensorObj (complex A (m + 1)) (complex A n) 0 0 0 rfl
          ((complexXIso A (m + 1) 0).inv (basis A (m + 1) 0 (ULift.up u)) ⊗ₜ[A]
            (complexXIso A n 0).inv (basis A n 0 (ULift.up v))) ⊗ₜ[A]
          faceVector A (vertex b))) =
      tensorVectorAt A (m + n) (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl) := by
  exact (iteratedCochainAction_basis_vertex_zero_outer A u v i b).trans
    (tensorCoInsertionAction_basis_vertex_zero_degree A v i b)

end SerrePositivity.EInfinity.IntervalCuts
