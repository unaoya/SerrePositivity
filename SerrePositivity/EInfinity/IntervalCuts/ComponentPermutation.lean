module

public import SerrePositivity.EInfinity.IntervalCuts.EdgePermutation

/-!
# 区間切断の全線形成分の対称群等変性

概要：Berger–Fresse §2.2.6 の辺・頂点余演算の全射語加群上の等変性を証明する。
方針：頂点テンソルは全次数零なので全置換で固定され、辺の基底等式を線形延長する。
規約：全 arity と全語次数、任意の可換係数環。
使われ方：区間余演算の整数複体射の equivariance を組み立てる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers SerrePositivity.Coxeter

variable (A : Type u) [CommRing A]

/-- 概要：同じ頂点の反復テンソルは全ての出力置換で固定される（BF §2.2.6）。
方針：隣接交換の公式で二面の次数零と符号一を使い、置換生成元で帰納する。
規約：空テンソルも含む。
使われ方：零語次数の頂点余演算の等変性。 -/
lemma vertexTensor_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) (b : Fin 2) :
    (permutationAction (interval A) n σ).asIso.hom.f 0
      (tensorVectorOfDegree A n 0 (fun _ => vertex b) (vertex_tupleDegree n b)) =
        tensorVectorOfDegree A n 0 (fun _ => vertex b) (vertex_tupleDegree n b) := by
  cases n with
  | zero =>
    have hs : σ = 1 := Subsingleton.elim _ _
    subst σ
    simp only [permutationAction_one, HomologicalComplex.id_f, ModuleCat.id_apply]
  | succ n =>
    apply permutation_induction_right σ
    · simp only [permutationAction_one, HomologicalComplex.id_f, ModuleCat.id_apply]
    · intro ρ a hρ
      have ha : (permutationAction (interval A) (n + 1) (adjacentTransposition a)).asIso.hom.f 0
          (tensorVectorOfDegree A (n + 1) 0 (fun _ => vertex b) (vertex_tupleDegree _ b)) =
            tensorVectorOfDegree A (n + 1) 0 (fun _ => vertex b) (vertex_tupleDegree _ b) := by
        rw [permutationAction_adjacent]
        change (adjacentIso (interval A) n a).hom.f 0 _ = _
        have H := adjacentIso_tensorVectorAt A n a (fun _ => vertex b) 0
          (congrArg (fun q : ℕ => -(q : ℤ)) (vertex_tupleDegree (n + 1) b))
        simpa only [simplexDegree_vertex, Nat.cast_zero, neg_zero, mul_zero,
          Int.negOnePow_zero, one_smul, tensorVectorAt_natDegree] using! H
      rw [permutationAction_mul]
      change (permutationAction (interval A) (n + 1) ρ).asIso.hom.f 0
        ((permutationAction (interval A) (n + 1) (adjacentTransposition a)).asIso.hom.f 0 _) = _
      rw [ha]
      exact hρ

/-- 概要：実際の頂点の全切断成分は任意の色置換に対して等変（BF §2.2.6）。
方針：正語次数は零、零次数は同じ頂点テンソルの置換不変性を使う。
規約：両端点と全 arity。
使われ方：語加群全体の頂点成分の等変性。 -/
lemma vertexComponentOnWord_permutation (n d : ℕ) (σ : Equiv.Perm (Fin n))
    (u : BasisWord n d) (b : Fin 2) :
    (permutationAction (interval A) n σ).asIso.hom.f (-(d : ℤ))
      (vertexComponentOnWord A u b) = vertexComponentOnWord A (Word.rename σ u) b := by
  by_cases hd : d = 0
  · subst d
    simp only [vertexComponentOnWord]
    exact vertexTensor_permutation A n σ b
  · rw [vertexComponentOnWord_eq_zero_of_positive A u (by omega),
      vertexComponentOnWord_eq_zero_of_positive A (Word.rename σ u) (by omega), map_zero]

/-- 概要：辺切断の線形成分は語の置換と出力の置換を交換する（BF §2.2.6）。
方針：全射語基底で辺成分の一般置換公式へ帰着する。
規約：線形写像全体の等式。
使われ方：双線形余演算の第一入力の置換を出力へ移す。 -/
lemma edgeComponent_permutation (n d : ℕ) (σ : Equiv.Perm (Fin n)) :
    (edgeComponent A n d).comp (renameLinear A σ) =
      ((permutationAction (interval A) n σ).asIso.hom.f (-((d + 1 : ℕ) : ℤ))).hom.comp
        (edgeComponent A n d) := by
  apply (basis A n d).ext
  rintro ⟨u⟩
  simp only [LinearMap.comp_apply, renameLinear_basis, edgeComponent_basis]
  exact (edgeComponentOnWord_permutation A n d σ u).symm

/-- 概要：頂点切断の線形成分は語の置換と出力の置換を交換する（BF §2.2.6）。
方針：全射語基底で頂点成分の一般置換公式へ帰着する。
規約：両端点の線形写像全体の等式。
使われ方：整数複体の等変性の頂点入力分岐。 -/
lemma vertexComponent_permutation (n d : ℕ) (σ : Equiv.Perm (Fin n)) (b : Fin 2) :
    (vertexComponent A n d b).comp (renameLinear A σ) =
      ((permutationAction (interval A) n σ).asIso.hom.f (-(d : ℤ))).hom.comp
        (vertexComponent A n d b) := by
  apply (basis A n d).ext
  rintro ⟨u⟩
  simp only [LinearMap.comp_apply, renameLinear_basis, vertexComponent_basis]
  exact (vertexComponentOnWord_permutation A n d σ u b).symm

end SerrePositivity.EInfinity.IntervalCuts
