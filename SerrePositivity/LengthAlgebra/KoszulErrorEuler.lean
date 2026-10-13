module

public import SerrePositivity.LengthAlgebra.ConeHomologyLength
public import SerrePositivity.HomologicalAlgebra.KoszulModuleBounds
public import SerrePositivity.HomologicalAlgebra.KoszulIdealAction

/-! # 最後の元がホモロジー上で零作用する Koszul 複体の Euler 評価

全列のホモロジー長の有限性から、前の列の有限性を導いて Euler の相殺を行う。
前の列の有限性・係数加群の有限生成性を追加の仮定にはしない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 最後の元が前の列のホモロジー上で零なら、負次数の全列の有限性だけでEuler評価零。
前の列の有限性・冪ねじれ性と全列の零次数の有限性を、錐の完全列から導く。 -/
theorem lambdaEuler_koszulModule_eq_zero_of_last_homology_action_zero
    {e : ℕ} (z : Fin (e + 1) → R) (M : ModuleCat.{u} R)
    (hz : ∀ q, HomologicalComplex.homologyMap
      (smulId (z (Fin.last e)) ((koszulModuleFunctor (Fin.init z)).obj M)) q = 0)
    (tFull : ∀ q, IsPowTorsion J (((koszulModuleFunctor z).obj M).homology q))
    (lNegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor z).obj M).homology q) ≠ ⊤) :
    lambdaEuler lam ((koszulModuleFunctor z).obj M) = 0 := by
  let P := (koszulModuleFunctor (Fin.init z)).obj M
  let f := smulId (z (Fin.last e)) P
  have tP (q : ℤ) : IsPowTorsion J (P.homology q) :=
    isPowTorsion_of_cone_of_homologyMap_eq_zero f q (hz q) (tFull q)
  have lP (q : ℤ) : lam.len (P.homology q) ≠ ⊤ := by
    by_cases hq : 0 < q
    · let := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X P q
        (koszulModuleFunctor_isZero_X_of_pos (Fin.init z) M q hq))
      rw [lam.len_eq_zero_of_subsingleton]
      exact ENNReal.zero_ne_top
    · exact ne_top_of_le_ne_top (lNegative (q - 1) (by omega))
        (lambdaHomology_le_cone_prev_of_homologyMap_eq_zero lam f q (hz q) (tFull (q - 1)))
  have lFull (q : ℤ) : lam.len ((Cone.cone f).homology q) ≠ ⊤ := by
    rw [(lambdaHomology_cone_of_homologyMap_eq_zero lam f hz q (tP q) (tP (q + 1))).2]
    exact ENNReal.add_ne_top.mpr ⟨lP q, lP (q + 1)⟩
  exact lambdaEuler_self_cone_eq_zero_of_homologyMap_eq_zero lam f hz
    (koszulModuleFunctor_bounded (Fin.init z) M) (koszulModuleFunctor_bounded z M)
    tP tFull lFull

/-- 最後の元が前の列と係数の零化元の生成イデアルに属すれば、Euler評価は零。
ホモロジー上の零作用は所属条件から証明し、未知の条件として渡さない。 -/
theorem lambdaEuler_koszulModule_eq_zero_of_last_mem_span_sup
    {e : ℕ} (z : Fin (e + 1) → R) (M : ModuleCat.{u} R) (a : R)
    (ha : ∀ m : M, a • m = 0)
    (hz : z (Fin.last e) ∈ Ideal.span (Set.range (Fin.init z)) ⊔ Ideal.span {a})
    (tFull : ∀ q, IsPowTorsion J (((koszulModuleFunctor z).obj M).homology q))
    (lNegative : ∀ q : ℤ, q < 0 →
      lam.len (((koszulModuleFunctor z).obj M).homology q) ≠ ⊤) :
    lambdaEuler lam ((koszulModuleFunctor z).obj M) = 0 :=
  lambdaEuler_koszulModule_eq_zero_of_last_homology_action_zero lam z M
    (koszul_last_homologyMap_eq_zero_of_mem_span_sup z M a ha hz) tFull lNegative

end SerrePositivity
