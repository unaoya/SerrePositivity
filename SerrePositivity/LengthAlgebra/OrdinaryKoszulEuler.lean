module

public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.FiniteLength

/-! # 通常の Koszul Euler 数と係数制限

剰余体への全射により、係数環上の通常長さと基底上の長さを同定する。
正則性・Noether 性・有限拡大・階数公式は要求しない。有限性を仮定しない
等式なので、無限長を零へ送る数値規約も両辺で一致する。
-/

@[expose] public section

universe u
namespace SerrePositivity
open CategoryTheory IsLocalRing

/-- 剰余体が同じ局所係数環では、通常の Koszul Euler 数は基底上の評価に等しい。 -/
lemma ordinary_koszulEuler_eq_koszulEulerChar
    {A T : Type u} [CommRing A] [CommRing T] [IsLocalRing T] [Algebra A T]
    {e : ℕ} (z : Fin e → A)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T))) :
    LengthAlgebra.koszulEuler (NormalizedLength.ordinary T) (algebraMap A T ∘ z) =
      koszulEulerChar A T z := by
  rw [LengthAlgebra.koszulEuler, ← chiOrd_eq_lambdaEuler_ordinary]
  unfold chiOrd koszulEulerChar
  congr 1
  funext q
  rw [length_restrictScalars_eq hres]

end SerrePositivity
