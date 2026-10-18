module

public import SerrePositivity.KST.DerivedBlowup.RestrictionComposition
public import SerrePositivity.KST.DerivedBlowup.ExteriorDGCategory

/-!
概要：KST §3.1 の係数環射の等式に沿う dg 係数制限の比較。
方針：Hom の複体を環射の等式で移送し、等式の消去で dg 関手の法則を確認する。
規約：対象写像は恒等で、Hom の各成分も元を変えない。
使われ方：有限重なり環関手の合成等式を dg 遷移へ反映する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：等しい環射による係数制限の間の dg 比較関手。
方針：Hom に環射の等式による複体移送を置く。
規約：KST §3.1。使われ方：環図式の関手性に沿う行先 dg 圏の比較。 -/
def restrictionRingHomTransportDGFunctor {φ ψ : R →+* S} (h : φ = ψ)
    (D : Type v) [DGCategory S D] :
    DGFunctor R (DGRestriction φ D) (DGRestriction ψ D) := by
  cases h
  exact EnrichedFunctor.id (Complex R) (DGRestriction φ D)

/-- 概要：環射等式の制限比較は対象を保つ。
方針：環射の等式を消去して恒等関手を計算する。
規約：KST §3.1。使われ方：dg 関手の合成比較の対象写像。 -/
theorem restrictionRingHomTransportDGFunctor_obj {φ ψ : R →+* S} (h : φ = ψ)
    (D : Type v) [DGCategory S D] (x : D) :
    (restrictionRingHomTransportDGFunctor h D).obj x = x := by
  cases h
  rfl

/-- 概要：環射の等式による dg 比較は Hom の各次数の元を変えない。
方針：環射の等式を消去すると恒等複体射になる。
規約：KST §3.1。使われ方：係数環関手の合成式による dg 遷移の比較。 -/
theorem restrictionRingHomTransportDGFunctor_exterior_apply {φ ψ : R →+* S} (h : φ = ψ)
    {M : Type u} [AddCommGroup M] [Module S M] (d : M →ₗ[S] S)
    (x y : ExteriorKoszulObject d) (q : ℤ) (z : (exteriorKoszulCochain d).X q) :
    (((restrictionRingHomTransportDGFunctor h (ExteriorKoszulObject d)).map x y).f q) z = z := by
  cases h
  rfl

end SerrePositivity.KST.DerivedBlowup
