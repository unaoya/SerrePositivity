module

public import SerrePositivity.EInfinity.SimplexCuts.FaceFamilyTensors
public import SerrePositivity.EInfinity.SimplexCuts.CompositeFaceFamilies

/-!
# 同じ二段の指定面と生成元の全族

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則、報告 §309。
同じ指定入力次数・生成元・有限族を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open IntervalCuts (prefixFamily suffixFamily insertionFamily)
open scoped Simplicial

/-- 同じ二段の面族の生成元は、元の指定因子を内側生成元で置換した族（BF §2.2.6）。 -/
lemma positiveNested_vectorFamily_eq_insertion (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) (x : S _⦋q⦌) :
    (fun a =>
      (⟨(positiveNestedFaceFamily u v k c a).1,
        gen A S (positiveNestedFaceFamily u v k c a).1
          (S.map (SimplexCategory.mkHom (positiveNestedFaceFamily u v k c a).2).op x)⟩ :
        Σ d : ℕ, (chains A S).X (-(d : ℤ)))) =
      insertionFamily
        (fun a => ⟨outputDegree c.1 (positiveWord u) a,
          gen A S (outputDegree c.1 (positiveWord u) a)
            (S.map (face c.1 (positiveWord u) a).op x)⟩)
        (fun b => ⟨outputDegree c.2 (positiveWord v) b,
          gen A S (outputDegree c.2 (positiveWord v) b)
            (S.map (face c.2 (positiveWord v) b).op
              (S.map (face c.1 (positiveWord u) k).op x))⟩) k := by
  funext a
  unfold positiveNestedFaceFamily insertionFamily
  cases he : operadInsertionEquiv m (n + 1) k a with
  | inl b => rfl
  | inr b =>
    exact congrArg (fun z => (⟨outputDegree c.2 (positiveWord v) b, z⟩ :
      Σ d : ℕ, (chains A S).X (-(d : ℤ))))
      (gen_map_comp_faces A S (vertices c.1 (positiveWord u) k)
        (vertices c.2 (positiveWord v) b) x)

end SerrePositivity.EInfinity.SimplexCuts
