module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeCutExponentModeq
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSignModEqTransport

/-!
# 元の合成切断と二段切断の同じ整数係数

Berger–Fresse §1.2.5・§2.2.4・§2.2.6、M14 L12a の C452。
報告 §199 の元のcompositionSign・cutSignをそのまま比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C452：非退化な元の切断の整数係数は、同じ二段切断の係数に厳密に一致（BF §2.2.6）。 -/
lemma positiveCompositeCutCoefficient_eq_nested {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) :
    Surjection.compositionSign u v k c.1 * cutSign c.2 (positiveCompositeCutWord u v k c.1).val =
      positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c) :=
  positiveCompositeCutCoefficient_eq_nested_of_modeq u v k c
    (positiveCompositeCut_exponent_modeq u v k c h)

end SerrePositivity.EInfinity.SimplexCuts
