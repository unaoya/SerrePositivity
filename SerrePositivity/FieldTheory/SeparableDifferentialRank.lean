module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # 分離的な体拡大での微分の階数

階数安定化の分離的な段階。Mathlibの形式的エタールな拡大の微分同型と、
係数拡大の次元公式を使う。底体の有限p-rankは要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct
variable (R K L : Type*) [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [Algebra.IsSeparable K L]

/-- 分離的な拡大では、通常の微分空間は同じ自然な写像による係数拡大。 -/
def separableDifferentialBaseChangeEquiv :
    L ⊗[K] KaehlerDifferential R K ≃ₗ[L] KaehlerDifferential R L := by
  let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R K L

@[simp] theorem separableDifferentialBaseChangeEquiv_tmul_D (l : L) (k : K) :
    separableDifferentialBaseChangeEquiv R K L (l ⊗ₜ[K] KaehlerDifferential.D R K k) =
      l • KaehlerDifferential.D R L (algebraMap K L k) := by
  simp [separableDifferentialBaseChangeEquiv, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D]

/-- 有限な通常微分空間は、分離的な拡大後も有限。拡大L/Kの有限性は不要。 -/
theorem finite_kaehlerDifferential_of_isSeparable
    [Module.Finite K (KaehlerDifferential R K)] :
    Module.Finite L (KaehlerDifferential R L) := by
  exact Module.Finite.equiv (separableDifferentialBaseChangeEquiv R K L)

/-- 微分の有限性を伴う、分離的な拡大での階数保存。 -/
theorem finrank_kaehlerDifferential_of_isSeparable
    [Module.Finite K (KaehlerDifferential R K)] :
    Module.finrank L (KaehlerDifferential R L) =
      Module.finrank K (KaehlerDifferential R K) := by
  rw [← (separableDifferentialBaseChangeEquiv R K L).finrank_eq,
    Module.finrank_baseChange]

end SerrePositivity
