module

public import SerrePositivity.KST.DerivedBlowup.FreeExteriorScalarMap

/-!
概要：KST §3.1 の自由生成加群の変換と外積係数変更の自然性。
方針：係数写像を半線形写像として束ね、生成加群上の可換性を総外積へ延長する。
規約：任意の自由生成加群間の線形変換を扱う。
使われ方：チャート基底変換と異なる係数環への移行の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R S : Type u} [CommRing R] [CommRing S] {I J : Type}

/-- 概要：自由生成加群の係数変更の半線形写像。
方針：各座標で環射の加法・乗法保存を使う。
規約：KST §3.1。使われ方：任意の生成元変換との自然性の検証。 -/
def freeGeneratorScalarLinearMap (φ : R →+* S) : (I →₀ R) →ₛₗ[φ] (I →₀ S) where
  toFun := freeGeneratorScalarMap φ
  map_add' x y := by ext j; exact map_add φ (x j) (y j)
  map_smul' r m := by ext j; exact map_mul φ r (m j)

/-- 概要：自由生成加群の係数変更は標準基底の係数を環射で送る。
方針：有限台関数を各座標で比較する。
規約：KST §3.1。使われ方：基底変換行列の係数変更。 -/
theorem freeGeneratorScalarMap_single (φ : R →+* S) (j : I) (r : R) :
    freeGeneratorScalarMap φ (Finsupp.single j r) = Finsupp.single j (φ r) := by
  classical
  ext k
  simp [freeGeneratorScalarMap, Finsupp.single_apply]

variable [DecidableEq I] [DecidableEq J]

/-- 概要：生成元変換と可換な係数変更は総外積でも可換。
方針：係数・生成元で自然性を示し、積と和で延長する。
規約：KST §3.1、二つの係数環の線形写像を生成加群上で比較する。
使われ方：Koszul 基底変換の dg 係数変更に関する自然性。 -/
theorem freeExteriorScalarMap_natural (φ : R →+* S)
    (f : (I →₀ R) →ₗ[R] (J →₀ R)) (g : (I →₀ S) →ₗ[S] (J →₀ S))
    (h : ∀ m, freeGeneratorScalarMap φ (f m) = g (freeGeneratorScalarMap φ m))
    (z : ExteriorAlgebra R (I →₀ R)) :
    freeExteriorScalarMap φ (ExteriorAlgebra.map f z) =
      ExteriorAlgebra.map g (freeExteriorScalarMap φ z) := by
  induction z using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, freeExteriorScalarMap_algebraMap,
      freeExteriorScalarMap_algebraMap, AlgHom.commutes]
  | ι m =>
    rw [ExteriorAlgebra.map_apply_ι, freeExteriorScalarMap_ι,
      freeExteriorScalarMap_ι, ExteriorAlgebra.map_apply_ι, h]
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end SerrePositivity.KST.DerivedBlowup
