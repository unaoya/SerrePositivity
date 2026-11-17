module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotal
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
概要：零次行だけに台を持つ元の二重複体の、同じtotalの軸射影。
方針：元の各直和入射で標準の逆写像の二つの合成を照合する。
規約：元のtotalと既存のtotalToRowZeroをそのまま使う。
使われ方：実際のΓのsingleを用いた増大複体への出口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
local notation "up" => ComplexShape.up ℕ
variable (K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)

set_option backward.isDefEq.respectTransparency false in
/-- 零次行だけに台を持つとき、元の同じ軸射影は同型。 -/
theorem cechIntegerTotalToRowZero_isIso
    (hz : ∀ a b, b ≠ 0 → IsZero ((K.X a).X b)) :
    IsIso (SerrePositivity.HomologicalAlgebra.totalToRowZero K) := by
  let π := SerrePositivity.HomologicalAlgebra.totalToRowZero K
  haveI (n : ℕ) : IsIso (π.f n) := by
    let i : (SerrePositivity.HomologicalAlgebra.bicomplexRow K 0).X n ⟶
        (K.total up).X n := K.ιTotal up n 0 n (by change n + 0 = n; omega)
    refine ⟨⟨i, ?_, ?_⟩⟩
    · apply HomologicalComplex₂.total.hom_ext
      intro a b h
      by_cases hb : b = 0
      · subst b
        have ha : a = n := by simpa using h
        subst a
        simp [π, i, SerrePositivity.HomologicalAlgebra.totalToRowZero,
          SerrePositivity.HomologicalAlgebra.rowZeroApp]
      · exact (hz a b hb).eq_of_src _ _
    · simp [π, i, SerrePositivity.HomologicalAlgebra.totalToRowZero,
        SerrePositivity.HomologicalAlgebra.rowZeroApp]
  exact HomologicalComplex.Hom.isIso_of_components π

/-- 同じtotalと零次行の同型。 -/
def cechIntegerTotalToRowZeroIso
    (hz : ∀ a b, b ≠ 0 → IsZero ((K.X a).X b)) :
    K.total up ≅ SerrePositivity.HomologicalAlgebra.bicomplexRow K 0 := by
  haveI := cechIntegerTotalToRowZero_isIso K hz
  exact asIso (SerrePositivity.HomologicalAlgebra.totalToRowZero K)

end SerrePositivity.AlgebraicGeometry
