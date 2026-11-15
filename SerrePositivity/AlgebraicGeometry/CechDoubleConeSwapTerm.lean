module

public import SerrePositivity.AlgebraicGeometry.CechRefinementConeMap

/-!
概要：既存の二重 cone を交換する、符号付きの各項の線形写像。
方針：零次・一次・以後の直積を分け、中間二成分を交換して符号を合わせる。
規約：まだ微分との可換性や全複体の完全性を主張しない。
使われ方：実際の共通細分の四角形の増大全複体の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable {A B A' B' : CochainComplex (ModuleCat.{u} R) ℕ}
variable (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')

/-- 二重 cone を交換する符号付きの各項の線形写像。 -/
def cechDoubleConeSwapTerm : ∀ n,
    cechRefinementConeTerm (cechRefinementCone A B f) (cechRefinementCone A' B' g) n →ₗ[R]
      cechRefinementConeTerm (cechRefinementCone A A' a) (cechRefinementCone B B' b) n
  | 0 => LinearMap.id
  | 1 =>
    { toFun := fun x ↦ (-x.2.1, (-x.1, x.2.2))
      map_add' := by
        intro x y
        change (-(x.2.1 + y.2.1), (-(x.1 + y.1), x.2.2 + y.2.2)) =
          (-x.2.1 + -y.2.1, (-x.1 + -y.1, x.2.2 + y.2.2))
        simp only [neg_add]
      map_smul' := by
        intro r x
        change (-(r • x.2.1), (-(r • x.1), r • x.2.2)) =
          (r • -x.2.1, (r • -x.1, r • x.2.2))
        simp only [smul_neg] }
  | n + 2 =>
    { toFun := fun x ↦ ((-x.1.1, -x.2.1), (-x.1.2, x.2.2))
      map_add' := by
        intro x y
        change ((-(x.1.1 + y.1.1), -(x.2.1 + y.2.1)),
          (-(x.1.2 + y.1.2), x.2.2 + y.2.2)) =
          ((-x.1.1 + -y.1.1, -x.2.1 + -y.2.1),
            (-x.1.2 + -y.1.2, x.2.2 + y.2.2))
        simp only [neg_add]
      map_smul' := by
        intro r x
        change ((-(r • x.1.1), -(r • x.2.1)), (-(r • x.1.2), r • x.2.2)) =
          ((r • -x.1.1, r • -x.2.1), (r • -x.1.2, r • x.2.2))
        simp only [smul_neg] }

/-- 同じ二重 cone の交換を二回行うと、各項で恒等になる。 -/
theorem cechDoubleConeSwapTerm_involutive (n : ℕ) :
    (cechDoubleConeSwapTerm a b f g n).comp (cechDoubleConeSwapTerm f g a b n) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero =>
      change (-(-x.1), (-(-x.2.1), x.2.2)) = x
      simp only [neg_neg]
      exact Prod.ext rfl (Prod.ext rfl rfl)
    | succ n =>
      change ((-(-x.1.1), -(-x.1.2)), (-(-x.2.1), x.2.2)) = x
      simp only [neg_neg]
      exact Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl rfl)

end SerrePositivity.AlgebraicGeometry
