module

public import SerrePositivity.KST.DerivedBlowup.ExteriorUnit
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
概要：KST Def3.1 の外積 Koszul 複体の次数0項を基底環と同定する。
方針：零延長の標準同型と第0外積の標準同型を合成する。
規約：単位射の次数0成分がこの同型の逆になる。
使われ方：空列の反復 cone 模型との比較の基底段階。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：Koszul cochain の次数0項と基底環の標準同型。
方針：第0外積への同型と zeroEquiv を合成する。
規約：KST Def3.1。使われ方：空列の模型比較と増大写像。 -/
def exteriorCochainZeroIso (d : M →ₗ[R] R) :
    (exteriorKoszulCochain d).X 0 ≅ ModuleCat.of R R :=
  exteriorCochainXIsoNonpos d 0 (by omega) ≪≫
    (exteriorPower.zeroEquiv R M).toModuleIso

/-- 概要：Koszul 単位射の次数0成分は基底環同型の逆。
方針：総外積に包含し、単位射と第0外積の逆写像を比較する。
規約：KST Def3.1。使われ方：単位射の次数0での可逆性。 -/
theorem exteriorKoszulUnit_f_zero (d : M →ₗ[R] R) :
    (exteriorKoszulUnit d).f 0 = (exteriorCochainZeroIso d).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply exteriorCochainInclusion_injective d 0
  rw [exteriorKoszulUnit_inclusion]
  change algebraMap R (ExteriorAlgebra R M) r =
    exteriorCochainInclusion d 0
      ((exteriorCochainXIsoNonpos d 0 (by omega)).inv.hom ((exteriorPower.zeroEquiv R M).symm r))
  rw [exteriorCochainInclusion_inv]
  simp [exteriorPower.zeroEquiv, Algebra.smul_def]

/-- 概要：Koszul 単位射は次数0で可逆。
方針：標準同型の逆として同定する。
規約：KST Def3.1、微分の値には依存しない。使われ方：空列の複体同型。 -/
theorem exteriorKoszulUnit_f_zero_isIso (d : M →ₗ[R] R) :
    IsIso ((exteriorKoszulUnit d).f 0) := by
  rw [exteriorKoszulUnit_f_zero]
  infer_instance

end SerrePositivity.KST.DerivedBlowup
