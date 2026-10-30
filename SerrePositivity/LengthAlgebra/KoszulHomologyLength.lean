module

public import SerrePositivity.HomologicalAlgebra.KoszulTower
public import SerrePositivity.LengthAlgebra.ConeHomologyLength
public import SerrePositivity.CategoryTheory.IteratedCone
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Category
public import SerrePositivity.PerfectComplex.NormalizedEuler

/-! # 無限分解にも適用できる Koszul ホモロジー長の二項公式

各スカラーが零ホモトピックなら、各段の錐の長完全列は短完全列になる。
複体の有界性・射影性は不要であり、長さの定義域と各次数での有限性だけを使う。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits Pretriangulated

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

variable {J : Ideal R} (lam : NormalizedLength R J)

/-- 零ホモトピックな射の錐の長さ公式。ホモロジー零の一般定理への互換入口。 -/
lemma lambdaHomology_null_cone {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hf : Homotopy f 0) (q : ℤ)
    (hQ : IsPowTorsion J (Q.homology q)) (hP : IsPowTorsion J (P.homology (q + 1))) :
    IsPowTorsion J ((Cone.cone f).homology q) ∧
      lam.len ((Cone.cone f).homology q) =
        lam.len (Q.homology q) + lam.len (P.homology (q + 1)) :=
  lambdaHomology_cone_of_homologyMap_eq_zero lam f
    (fun i ↦ by simpa only [HomologicalComplex.homologyMap_zero] using hf.homologyMap_eq i)
    q hQ hP

/-- 零スカラーの Koszul 構成は、各次数の冪ねじれ性と長さの有限性を保つ。
有界性・射影性を使わず、各段の短完全列だけを用いる。 -/
lemma lambdaHomology_koszul_null_finite {e : ℕ} (x : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0))
    (ht : ∀ q, IsPowTorsion J (P.homology q)) (hfin : ∀ q, lam.len (P.homology q) ≠ ⊤) :
    (∀ q, IsPowTorsion J ((koszulComplexOn x P).homology q)) ∧
    (∀ q, lam.len ((koszulComplexOn x P).homology q) ≠ ⊤) := by
  induction e with
  | zero => exact ⟨ht, hfin⟩
  | succ e ih =>
    obtain ⟨ht', hfin'⟩ := ih (Fin.init x) (fun j ↦ hx j.castSucc)
    have hn : Nonempty (Homotopy
        (smulId (x (Fin.last e)) (koszulComplexOn (Fin.init x) P)) 0) :=
      (nonempty_homotopy_smul_id_zero_iff _ _).mpr
        (koszulComplexOn_smul_zero (Fin.init x) P
          (fun j ↦ (nonempty_homotopy_smul_id_zero_iff _ _).mp (hx j.castSucc))
          (x (Fin.last e)) ((nonempty_homotopy_smul_id_zero_iff _ _).mp (hx (Fin.last e))))
    have hc (q : ℤ) := lambdaHomology_null_cone lam _ hn.some q (ht' q) (ht' (q + 1))
    refine ⟨fun q ↦ (hc q).1, fun q ↦ ?_⟩
    change lam.len ((Cone.cone _).homology q) ≠ ⊤
    rw [(hc q).2]
    exact ENNReal.add_ne_top.mpr ⟨hfin' q, hfin' (q + 1)⟩

/-- 実際の Koszul 塔の長さは、共通の錐の係数作用素で計算される。
有限性の確認と数値漸化式の一般論を分離し、無限分解にも適用できる。 -/
lemma lambdaHomology_koszul_null_pow {e : ℕ} (x : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0))
    (ht : ∀ q, IsPowTorsion J (P.homology q)) (hfin : ∀ q, lam.len (P.homology q) ≠ ⊤) :
    (∀ q, IsPowTorsion J ((koszulComplexOn x P).homology q)) ∧
    (∀ q, lam.len ((koszulComplexOn x P).homology q) ≠ ⊤) ∧
    ∀ q, (lam.len ((koszulComplexOn x P).homology q)).toReal =
      ((cochainLengthShift + 1) ^ e) (fun q ↦ (lam.len (P.homology q)).toReal) q := by
  have hf := lambdaHomology_koszul_null_finite lam x P hx ht hfin
  refine ⟨hf.1, hf.2, ?_⟩
  let y : ℕ → R := fun j ↦ if h : j < e then x ⟨j, h⟩ else 0
  have hy : (fun j : Fin e ↦ y j) = x := by funext j; simp [y, j.isLt]
  have hh (k : ℕ) (hk : k ≤ e) (j : Fin k) :
      Nonempty (Homotopy (smulId (y j) P) 0) := by
    simpa [y, show (j : ℕ) < e by omega] using hx ⟨j, by omega⟩
  have hb := coneLength_pow_of_recurrence
    (fun k q ↦ (lam.len ((koszulComplexOn (fun j : Fin k ↦ y j) P).homology q)).toReal) e
    (fun k hk q ↦ by
      have hf' := lambdaHomology_koszul_null_finite lam _ P (hh k (by omega)) ht hfin
      have hn : Nonempty (Homotopy
          (smulId (y k) (koszulComplexOn (fun j : Fin k ↦ y j) P)) 0) :=
        (nonempty_homotopy_smul_id_zero_iff _ _).mpr
          (koszulComplexOn_smul_zero _ P
            (fun j ↦ (nonempty_homotopy_smul_id_zero_iff _ _).mp (hh k (by omega) j))
            (y k) ((nonempty_homotopy_smul_id_zero_iff _ _).mp
              (by simpa only [y, dite_eq_left hk, smulId] using hx ⟨k, hk⟩)))
      have hc := lambdaHomology_null_cone lam _ hn.some q (hf'.1 q) (hf'.1 (q + 1))
      have hre := congrArg ENNReal.toReal hc.2
      rw [ENNReal.toReal_add (hf'.2 q) (hf'.2 (q + 1))] at hre
      exact hre)
  intro q
  have hbq := congrFun hb q
  change (lam.len ((koszulComplexOn (fun j : Fin e ↦ y j) P).homology q)).toReal =
    ((cochainLengthShift + 1) ^ e) (fun q ↦ (lam.len (P.homology q)).toReal) q at hbq
  rw [hy] at hbq
  exact hbq

/-- 零ホモトピックなスカラーの Koszul ホモロジー長の二項係数公式。 -/
theorem lambdaHomology_koszul_null_binomial {e : ℕ} (x : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0))
    (ht : ∀ q, IsPowTorsion J (P.homology q)) (hfin : ∀ q, lam.len (P.homology q) ≠ ⊤) (q : ℤ) :
    (lam.len ((koszulComplexOn x P).homology q)).toReal =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) * (lam.len (P.homology (q + j))).toReal := by
  rw [(lambdaHomology_koszul_null_pow lam x P hx ht hfin).2.2 q, coneLength_binomial]

end SerrePositivity
