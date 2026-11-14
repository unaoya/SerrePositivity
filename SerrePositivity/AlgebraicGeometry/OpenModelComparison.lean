module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict

/-!
概要：降ろした開の逆像の等式から、元の開との実際の Cartesian な比較を作る。
方針：開埋め込みの lift と開の逆像による pullback の判定を使う。
規約：比較射の存在を別の入力にしない。
使われ方：G2 の降ろした重なりの開から貼り合わせの比較の入力を供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {U X Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (a : X ⟶ Y)
  (V : Y.Opens) (h : a ⁻¹ᵁ V = j.opensRange)

include h

/-- 逆像の開の等式から、元の開への実際の比較射を作る。 -/
def openModelComparison : U ⟶ V :=
  IsOpenImmersion.lift V.ι (j ≫ a) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change a (j z) ∈ (V : Set Y)
    change j z ∈ (a ⁻¹ᵁ V : Set X)
    rw [h]
    exact ⟨z, rfl⟩)

/-- 開の比較射は、元の射と同じ可換式を満たす。 -/
@[reassoc (attr := simp)] theorem openModelComparison_fac :
    openModelComparison j a V h ≫ V.ι = j ≫ a :=
  IsOpenImmersion.lift_fac _ _ _

/-- 降ろした開と元の開の、実際に作った比較は Cartesian。 -/
theorem isPullback_openModelComparison :
    IsPullback (openModelComparison j a V h) j V.ι a :=
  IsOpenImmersion.isPullback _ _ _ _ (openModelComparison_fac j a V h).symm
    (by simpa only [Scheme.Opens.opensRange_ι] using h)

end SerrePositivity.AlgebraicGeometry
