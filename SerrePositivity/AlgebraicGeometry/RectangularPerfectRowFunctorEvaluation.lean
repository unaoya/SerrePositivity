module

public import SerrePositivity.AlgebraicGeometry.RectangularPerfectRowFunctor

/-!
概要：同じ矩形の行の関手の同型を、元の各タプルの環同型で評価する。
方針：検証済みの成分の同型の評価式を、そのまま関手の同型の成分へ渡す。
規約：元の余積と各実際の係数環を保持する。
使われ方：増大行の可換性で関手の同型を展開せず同じ評価式を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} [Fintype ι] [DecidableEq ι]
variable (U : ι → Y.Opens) (p : ℕ) (hp : p.Prime)
variable (h : ∀ n : SimplexCategoryᵒᵖ,
  ∀ O, (p : ((Arrow.mk f).cechNerve.obj n).presheaf.obj O) = 0)

/-- 同じ関手の同型の評価は、元の同じ矩形の環同型の評価。 -/
theorem rectangularPerfectRowFunctorIso_hom_apply (k : ℕ)
    (hN : ∀ n : SimplexCategory, (p : (rectangularPerfectRowGammaFunctor f U k).obj n) = 0)
    (n : SimplexCategory)
    (x : (frobeniusRingDiagram (rectangularPerfectRowGammaFunctor f U k) p hp hN).obj n)
    (q : Fin (k + 1) → Fin (n.len + 1) → ι) :
    (((rectangularPerfectRowFunctorIso f U p hp h k hN).hom.app n).hom x) q =
      rectangularPerfectRowEquiv f U p hp n k (hN n)
        (fun q ↦ h (op n) (op (cechOpenIntersection (schemeCechTupleOpen f U (op n))
          (cechTupleSupport q)))) x q :=
  rectangularPerfectRowComponentIso_hom_apply f U p hp h k hN n x q

end SerrePositivity.AlgebraicGeometry
