module

public import SerrePositivity.EInfinity.SimplexCuts.NormalizedGenerators

/-!
# 元の零次の指定面から来る同じ零単体の生成元

Berger–Fresse §2.2.6、M14 L12a、報告 §350。
次数と指定面の同じSigma入力を零次へ特殊化する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- 零次の指定面は、同じ零単体の正規化生成元を与える（BF §2.2.6）。 -/
lemma faceData_generator_zero (A : Type u) [CommRing A] (S : SSet.{0}) {q : ℕ}
    (F : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)) (hF : F.1 = 0) (x : S _⦋q⦌) :
    ∃ y : S _⦋0⦌,
      (⟨F.1, gen A S F.1 (S.map (SimplexCategory.mkHom F.2).op x)⟩ :
        Σ d : ℕ, (chains A S).X (-(d : ℤ))) = ⟨0, gen A S 0 y⟩ := by
  rcases F with ⟨d, f⟩
  change d = 0 at hF
  subst d
  exact ⟨S.map (SimplexCategory.mkHom f).op x, rfl⟩

end SerrePositivity.EInfinity.SimplexCuts
