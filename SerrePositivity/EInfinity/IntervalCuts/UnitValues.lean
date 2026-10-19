module

public import SerrePositivity.EInfinity.IntervalCuts.CochainAction
public import SerrePositivity.EInfinity.IntervalCuts.TensorDegreeTransport
public import SerrePositivity.EInfinity.Surjection.ComplexUnit
public import SerrePositivity.EInfinity.BarrattEccles.Unitors

/-!
# 一文字単位の区間切断値

概要：Berger–Fresse §2.2.6 の一文字語の余演算を区間の恒等演算へ比較する。
方針：唯一の切断を評価し、一次テンソル冪の右単位子の逆へ同定する。
規約：実際の整数区間と全ての可換係数環を扱う。
使われ方：χ の区間余演算の単位則。
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

/-- 概要：一因子の指定次数テンソルは右単位子の逆による面生成元（BF §2.2.6）。
方針：テンソル生成元の再帰式と複体の右単位子の公式を使う。
規約：指定次数は面の鎖次数。
使われ方：単位語の出力を元の区間へ戻す。 -/
lemma tensorVectorOfDegree_one (s : Simplex) :
    tensorVectorOfDegree A 1 (simplexDegree s) (fun _ => s)
      (by simp [tupleDegree]) =
      (oneIso (interval A)).inv.f (-(simplexDegree s : ℤ)) (faceVector A s) := by
  change tensorVectorAt A 1 (fun _ => s) (-(simplexDegree s : ℤ))
    (by simp [tupleDegree]) = _
  rw [tensorVectorAt_succ A 0 _ _ 0 _ rfl (by rfl) (add_zero _)]
  simp only [eqToHom_refl, ModuleCat.id_apply]
  exact (BarrattEccles.cochain_rightUnitor_inv_apply A (interval A)
    (-(simplexDegree s : ℤ)) (faceVector A s)).symm

/-- 概要：一文字単位語の唯一の辺切断は非退化（BF §2.2.1）。
方針：二つの展開頂点の色と値を有限に判定する。
規約：単位語は恒等置換の一文字語。
使われ方：辺の切断和の唯一の項。 -/
lemma unitWord_edgeNondegenerate :
    EdgeNondegenerate (permutationWord (1 : Equiv.Perm (Fin 1))).val 0 := by decide

/-- 概要：一文字単位語の辺切断の出力は元の辺（BF §2.2.1）。
方針：唯一の色の出力頂点集合を計算する。
規約：全出力族は一因子。
使われ方：単位の辺成分の値を同定する。 -/
lemma unitWord_edgeOutput :
    edgeOutput (permutationWord (1 : Equiv.Perm (Fin 1))) 0 = (fun _ => edge) := by
  funext k
  fin_cases k
  apply Subtype.ext
  decide

/-- 概要：一文字単位語の辺切断符号は正（BF §2.2.4）。
方針：逆転も内側区間もないことを有限に計算する。
規約：符号は整数。
使われ方：単位の辺成分のスカラーを消す。 -/
lemma unitWord_edgeSign :
    edgeSign (permutationWord (1 : Equiv.Perm (Fin 1))).val 0 = 1 := by decide

/-- 概要：χ の単位元の辺成分は右単位子の逆である（BF §2.2.6）。
方針：一文字基底の唯一の切断を評価する。
規約：区間の次数 −1 成分。
使われ方：辺入力での複体射の単位則。 -/
lemma edgeComponent_unitElement :
    edgeComponent A 1 0 (unitElement A) =
      (oneIso (interval A)).inv.f (-1) ((intervalXIso A 1).inv (edgeChain A)) := by
  rw [unitElement, edgeComponent_basis]
  unfold edgeComponentOnWord
  rw [Fin.sum_univ_one, dite_eq_left unitWord_edgeNondegenerate, unitWord_edgeSign]
  simp only [Int.cast_one, one_smul]
  simp only [unitWord_edgeOutput]
  simpa only [simplexDegree_edge, faceVector, faceChain_edge] using!
    tensorVectorOfDegree_one A edge

/-- 概要：χ の単位元の頂点成分は右単位子の逆である（BF §2.2.6）。
方針：零語次数の頂点成分と一因子テンソル公式を使う。
規約：両端点を同時に扱う。
使われ方：頂点入力での複体射の単位則。 -/
lemma vertexComponent_unitElement (b : Fin 2) :
    vertexComponent A 1 0 b (unitElement A) =
      (oneIso (interval A)).inv.f 0 ((intervalXIso A 0).inv (vertexChain A b)) := by
  rw [unitElement, vertexComponent_basis]
  unfold vertexComponentOnWord
  rw [dite_eq_left rfl]
  simpa only [simplexDegree_vertex, faceVector, faceChain_vertex] using!
    tensorVectorOfDegree_one A (vertex b)

end SerrePositivity.EInfinity.IntervalCuts
