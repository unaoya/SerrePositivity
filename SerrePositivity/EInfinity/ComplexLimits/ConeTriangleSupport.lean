module
public import SerrePositivity.EInfinity.ComplexLimits.ConeTriangleIndex

/-!
概要：三相時刻の零相・二相の一意性から、元の三角形添字の単射性を判定する。
方針：前置・終端固定の添字の値を場合分けし、後続と前面埋め込みの単射性を使う。
規約：任意の部分集合を保持する。使われ方：混合 HA の退化した項の消滅。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits

lemma coneTriangleFrontIndex_injOn_iff {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Set (Fin (n + 1))) :
    Set.InjOn (coneTriangleFrontIndex τ) I ↔
      ∀ i ∈ I, ∀ j ∈ I, τ i = 0 → τ j = 0 → i = j := by
  constructor
  · intro h i hi j hj hti htj
    exact h hi hj ((coneTriangleFrontIndex_zero τ i hti).trans
      (coneTriangleFrontIndex_zero τ j htj).symm)
  · intro h i hi j hj hij
    by_cases hti : τ i = 0
    · by_cases htj : τ j = 0
      · exact h i hi j hj hti htj
      · rw [coneTriangleFrontIndex_zero τ i hti,
          coneTriangleFrontIndex_ne_zero τ j htj] at hij
        exact False.elim (Fin.succ_ne_zero _ hij.symm)
    · by_cases htj : τ j = 0
      · rw [coneTriangleFrontIndex_ne_zero τ i hti,
          coneTriangleFrontIndex_zero τ j htj] at hij
        exact False.elim (Fin.succ_ne_zero _ hij)
      · rw [coneTriangleFrontIndex_ne_zero τ i hti,
          coneTriangleFrontIndex_ne_zero τ j htj] at hij
        exact Fin.succ_injective _ hij

lemma coneTriangleBackIndex_injOn_iff {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Set (Fin (n + 1))) :
    Set.InjOn (coneTriangleBackIndex τ) I ↔
      ∀ i ∈ I, ∀ j ∈ I, τ i = 2 → τ j = 2 → i = j := by
  constructor
  · intro h i hi j hj hti htj
    exact h hi hj ((coneTriangleBackIndex_two τ i hti).trans
      (coneTriangleBackIndex_two τ j htj).symm)
  · intro h i hi j hj hij
    by_cases hti : τ i = 2
    · by_cases htj : τ j = 2
      · exact h i hi j hj hti htj
      · rw [coneTriangleBackIndex_two τ i hti,
          coneTriangleBackIndex_ne_two τ j htj] at hij
        exact False.elim (Fin.castSucc_ne_last _ hij.symm)
    · by_cases htj : τ j = 2
      · rw [coneTriangleBackIndex_ne_two τ i hti,
          coneTriangleBackIndex_two τ j htj] at hij
        exact False.elim (Fin.castSucc_ne_last _ hij)
      · rw [coneTriangleBackIndex_ne_two τ i hti,
          coneTriangleBackIndex_ne_two τ j htj] at hij
        exact Fin.castSucc_injective _ hij

lemma coneTriangleFrontIndex_not_injOn {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Set (Fin (n + 1))) (i j : Fin (n + 1)) (hi : i ∈ I) (hj : j ∈ I)
    (hne : i ≠ j) (hti : τ i = 0) (htj : τ j = 0) :
    ¬ Set.InjOn (coneTriangleFrontIndex τ) I := by
  intro h
  exact hne ((coneTriangleFrontIndex_injOn_iff τ I).mp h i hi j hj hti htj)

lemma coneTriangleBackIndex_not_injOn {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Set (Fin (n + 1))) (i j : Fin (n + 1)) (hi : i ∈ I) (hj : j ∈ I)
    (hne : i ≠ j) (hti : τ i = 2) (htj : τ j = 2) :
    ¬ Set.InjOn (coneTriangleBackIndex τ) I := by
  intro h
  exact hne ((coneTriangleBackIndex_injOn_iff τ I).mp h i hi j hj hti htj)

end SerrePositivity.EInfinity.ComplexLimits
