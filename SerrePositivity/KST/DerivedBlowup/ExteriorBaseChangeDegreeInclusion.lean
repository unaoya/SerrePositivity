module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChange

/-!
概要：KST Def3.1 の外積の同次部分へのスカラー拡大包含は単射である。
方針：外積の次数射影を tensor して左逆を構成する。
規約：係数環の平坦性は仮定しない。同次部分の直和分解を使う。
使われ方：外積基底変更同型を同次次数へ制限する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- 概要：総外積から第n外積への標準線形射影。
方針：graded decomposition の第n成分を取る。
規約：KST Def3.1。使われ方：係数変更後の同次包含の左逆。 -/
def exteriorDegreeProjection (n : ℕ) :
    ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra.exteriorPower R n M :=
  (DFinsupp.lapply n).comp
    (DirectSum.decomposeLinearEquiv (fun i => ExteriorAlgebra.exteriorPower R i M)).toLinearMap

/-- 概要：同次部分の包含後の射影は恒等。
方針：graded decomposition の同次元上の公式を使う。
規約：KST Def3.1。使われ方：スカラー拡大後も残る分裂単射性。 -/
@[simp] theorem exteriorDegreeProjection_coe (n : ℕ)
    (z : ExteriorAlgebra.exteriorPower R n M) : exteriorDegreeProjection n z.val = z := by
  change (DirectSum.decomposeLinearEquiv
    (fun i => ExteriorAlgebra.exteriorPower R i M) z.val) n = z
  rw [DirectSum.decomposeLinearEquiv_apply_coe]
  simp

/-- 概要：同次外積のスカラー拡大を総外積のスカラー拡大へ包含する。
方針：同次部分加群の包含を tensor する。
規約：KST Def3.1。使われ方：同次基底変更写像の総外積での比較。 -/
def exteriorBaseChangeDegreeInclusion (n : ℕ) :
    S ⊗[R] ExteriorAlgebra.exteriorPower R n M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S)
    (ExteriorAlgebra.exteriorPower R n M).subtype

/-- 概要：総外積のスカラー拡大から第n同次部分のスカラー拡大への射影。
方針：標準次数射影を tensor する。
規約：KST Def3.1。使われ方：同次包含の左逆。 -/
def exteriorBaseChangeDegreeProjection (n : ℕ) :
    S ⊗[R] ExteriorAlgebra R M →ₗ[S] S ⊗[R] ExteriorAlgebra.exteriorPower R n M :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) (exteriorDegreeProjection n)

/-- 概要：スカラー拡大後の同次包含は次数射影で分裂する。
方針：純粋 tensor 上で元の射影の左逆を使い、加法的に延長する。
規約：KST Def3.1、平坦性不要。使われ方：係数変更後の同次包含の単射性。 -/
@[simp] theorem exteriorBaseChangeDegreeProjection_inclusion (n : ℕ)
    (z : S ⊗[R] ExteriorAlgebra.exteriorPower R n M) :
    exteriorBaseChangeDegreeProjection n (exteriorBaseChangeDegreeInclusion n z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    change s ⊗ₜ[R] exteriorDegreeProjection n z.val = s ⊗ₜ[R] z
    rw [exteriorDegreeProjection_coe]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- 概要：スカラー拡大後の同次包含は単射。
方針：同次射影の左逆に等式を写す。
規約：KST Def3.1。使われ方：同次基底変更の逆元律の検証。 -/
theorem exteriorBaseChangeDegreeInclusion_injective (n : ℕ) :
    Function.Injective (exteriorBaseChangeDegreeInclusion (R := R) (S := S) (M := M) n) := by
  intro x y h
  have hh := congrArg (exteriorBaseChangeDegreeProjection n) h
  simpa only [exteriorBaseChangeDegreeProjection_inclusion] using hh

end SerrePositivity.KST.DerivedBlowup
