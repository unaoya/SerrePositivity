module

public import SerrePositivity.KST.DerivedBlowup.ExteriorIntegerInclusion
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
概要：KST Def3.1 の有限自由 Koszul 外積模型の項と次数境界。
方針：各非正次数を同次外積と同定し、既存の外積の有限性・自由性・消滅を使う。
規約：基底環の非零性や関係式の正則性は仮定しない。
使われ方：チャートの完全複体性と反復 cone 模型との有限次数比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：有限生成加群の Koszul 外積複体の各項は有限生成。
方針：非正次数では有限外積との同型、正次数では零対象性を使う。
規約：KST Def3.1、関係式の正則性不要。使われ方：局所有限表示の検証。 -/
theorem exteriorKoszulCochain_finite [Module.Finite R M] (d : M →ₗ[R] R) (q : ℤ) :
    Module.Finite R ((exteriorKoszulCochain d).X q) := by
  by_cases hq : q ≤ 0
  · exact Module.Finite.equiv (exteriorCochainXIsoNonpos d q hq).toLinearEquiv.symm
  · have := ModuleCat.subsingleton_of_isZero
      (exteriorKoszulCochain_isZero_X_pos d q (lt_of_not_ge hq))
    infer_instance

/-- 概要：自由加群の Koszul 外積複体の各項は自由。
方針：非正次数では外積の基底を標準同型で移し、正次数では零加群を使う。
規約：KST Def3.1、任意可換環。使われ方：Koszul チャートの項の射影性。 -/
theorem exteriorKoszulCochain_free [Module.Free R M] (d : M →ₗ[R] R) (q : ℤ) :
    Module.Free R ((exteriorKoszulCochain d).X q) := by
  by_cases hq : q ≤ 0
  · exact Module.Free.of_equiv (exteriorCochainXIsoNonpos d q hq).toLinearEquiv.symm
  · have := ModuleCat.subsingleton_of_isZero
      (exteriorKoszulCochain_isZero_X_pos d q (lt_of_not_ge hq))
    infer_instance

/-- 概要：有限生成系の個数より下の Koszul cochain 項は零。
方針：外積次数が生成系の個数を超えると零であることを使う。
規約：KST Def3.1、生成系の線形独立性は不要。使われ方：有限振幅の証明。 -/
theorem exteriorKoszulCochain_isZero_X_lt {I : Type v} [Finite I] (g : I → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (d : M →ₗ[R] R)
    (q : ℤ) (hq : q < -(Nat.card I : ℤ)) : IsZero ((exteriorKoszulCochain d).X q) := by
  have hnonpos : q ≤ 0 := by omega
  have := exteriorPower.subsingleton_of_span_eq_top_of_card_lt g hg (-q).toNat (by omega)
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of R (ExteriorAlgebra.exteriorPower R (-q).toNat M))).of_iso
      (exteriorCochainXIsoNonpos d q hnonpos)

end SerrePositivity.KST.DerivedBlowup
