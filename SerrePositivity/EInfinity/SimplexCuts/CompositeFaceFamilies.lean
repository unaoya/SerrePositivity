module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeNestedEquiv
public import SerrePositivity.EInfinity.IntervalCuts.InsertionFamilies

/-!
# 元の合成切断と二段切断の指定面の族

Berger–Fresse §2.2.6、M14 L12a の指定面の照合。
次数と元のverticesを組にし、二段側は既存の出力順序と同じ面の合成を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の合成切断の次数と指定面を保持した族（BF §2.2.6）。 -/
def positiveCompositeFaceFamily {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    Fin (m + (n + 1)) → Σ t : ℕ, Fin (t + 1) →o Fin (q + 1) :=
  fun a => ⟨outputDegree c.2 (positiveCompositeCutWord u v k c.1) a,
    vertices c.2 (positiveCompositeCutWord u v k c.1) a⟩

/-- 元の二段切断の面を同じ出力順序で合成した族（BF §2.2.6）。 -/
def positiveNestedFaceFamily {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    Fin (m + (n + 1)) → Σ t : ℕ, Fin (t + 1) →o Fin (q + 1) :=
  IntervalCuts.insertionFamily
    (fun a => (⟨outputDegree c.1 (positiveWord u) a,
      vertices c.1 (positiveWord u) a⟩ : Σ t : ℕ, Fin (t + 1) →o Fin (q + 1)))
    (fun b => ⟨outputDegree c.2 (positiveWord v) b,
      (vertices c.1 (positiveWord u) k).comp (vertices c.2 (positiveWord v) b)⟩) k

end SerrePositivity.EInfinity.SimplexCuts
