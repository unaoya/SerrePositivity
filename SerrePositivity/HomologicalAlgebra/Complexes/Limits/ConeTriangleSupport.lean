module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTriangleIndex

/-!
概要：三相時刻の零相・二相の一意性から、元の三角形添字の単射性を判定する。
方針：前置・終端固定の添字の値を場合分けし、後続と前面埋め込みの単射性を使う。
規約：任意の部分集合を保持する。使われ方：混合 HA の退化した項の消滅。
-/
@[expose] public section
namespace SerrePositivity.ComplexLimits

lemma coneTriangleFrontIndex_injOn_iff {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Set (Fin (n + 1))) :
    Set.InjOn (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ) I ↔
      ∀ i ∈ I, ∀ j ∈ I, τ i = 0 → τ j = 0 → i = j := by
  constructor
  · intro h i hi j hj hti htj
    exact h hi hj ((_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_zero τ i hti).trans
      (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_zero τ j htj).symm)
  · intro h i hi j hj hij
    by_cases hti : τ i = 0
    · by_cases htj : τ j = 0
      · exact h i hi j hj hti htj
      · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_zero τ i hti,
          _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_ne_zero τ j htj] at hij
        exact False.elim (Fin.succ_ne_zero _ hij.symm)
    · by_cases htj : τ j = 0
      · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_ne_zero τ i hti,
          _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_zero τ j htj] at hij
        exact False.elim (Fin.succ_ne_zero _ hij)
      · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_ne_zero τ i hti,
          _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_ne_zero τ j htj] at hij
        exact Fin.succ_injective _ hij

lemma coneTriangleBackIndex_injOn_iff {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Set (Fin (n + 1))) :
    Set.InjOn (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ) I ↔
      ∀ i ∈ I, ∀ j ∈ I, τ i = 2 → τ j = 2 → i = j := by
  constructor
  · intro h i hi j hj hti htj
    exact h hi hj ((_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ i hti).trans
      (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ j htj).symm)
  · intro h i hi j hj hij
    by_cases hti : τ i = 2
    · by_cases htj : τ j = 2
      · exact h i hi j hj hti htj
      · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ i hti,
          _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ j htj] at hij
        exact False.elim (Fin.castSucc_ne_last _ hij.symm)
    · by_cases htj : τ j = 2
      · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ i hti,
          _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ j htj] at hij
        exact False.elim (Fin.castSucc_ne_last _ hij)
      · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ i hti,
          _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ j htj] at hij
        exact Fin.castSucc_injective _ hij

lemma coneTriangleFrontIndex_not_injOn {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Set (Fin (n + 1))) (i j : Fin (n + 1)) (hi : i ∈ I) (hj : j ∈ I)
    (hne : i ≠ j) (hti : τ i = 0) (htj : τ j = 0) :
    ¬ Set.InjOn (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ) I := by
  intro h
  exact hne ((_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_injOn_iff τ I).mp h i hi j hj hti htj)

lemma coneTriangleBackIndex_not_injOn {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Set (Fin (n + 1))) (i j : Fin (n + 1)) (hi : i ∈ I) (hj : j ∈ I)
    (hne : i ≠ j) (hti : τ i = 2) (htj : τ j = 2) :
    ¬ Set.InjOn (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ) I := by
  intro h
  exact hne ((_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_injOn_iff τ I).mp h i hi j hj hti htj)

end SerrePositivity.ComplexLimits
