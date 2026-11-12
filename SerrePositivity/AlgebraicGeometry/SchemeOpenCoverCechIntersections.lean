module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCech
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Order.CompleteLattice.Finset

/-!
概要：Čech の有限交叉をスキームの逆像と開埋め込みの像に対応させる。
方針：空交叉と有限個の交叉に分け、既存の逆像の公式を適用する。
規約：増大項の空交叉も含め、開埋め込みの像では opensRange との交叉を残す。
使われ方：アフィン座標上の準連接係数の計算を元のスキームへ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {ι : Type} [DecidableEq ι]
variable (f : X ⟶ Y) (U : ι → Y.Opens)

/-- スキームの逆像は Čech の有限交叉を保つ。 -/
theorem cechOpenIntersection_scheme_preimage (T : Finset ι) :
    f ⁻¹ᵁ cechOpenIntersection U T =
      cechOpenIntersection (fun i ↦ f ⁻¹ᵁ U i) T := by
  induction T using Finset.induction_on with
  | empty => simp [cechOpenIntersection]
  | @insert i T hi ih =>
    change f ⁻¹ᵁ (⨅ j ∈ insert i T, U j) =
      ⨅ j ∈ insert i T, f ⁻¹ᵁ U j
    rw [← Finset.inf_eq_iInf, ← Finset.inf_eq_iInf, Finset.inf_insert,
      Finset.inf_insert, Scheme.Hom.preimage_inf]
    simpa only [Finset.inf_eq_iInf, cechOpenIntersection] using
      congrArg (fun W ↦ f ⁻¹ᵁ U i ⊓ W) ih

/-- 開埋め込みの像による交叉の表示。空交叉では像全体を与える。 -/
theorem cechOpenIntersection_scheme_image_preimage [IsOpenImmersion f] (T : Finset ι) :
    f ''ᵁ cechOpenIntersection (fun i ↦ f ⁻¹ᵁ U i) T =
      f.opensRange ⊓ cechOpenIntersection U T := by
  rw [← cechOpenIntersection_scheme_preimage, f.image_preimage_eq_opensRange_inf]

end SerrePositivity.AlgebraicGeometry
