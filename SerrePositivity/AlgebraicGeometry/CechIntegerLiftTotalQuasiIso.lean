module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalNaturality
public import SerrePositivity.HomologicalAlgebra.BicomplexColumnQuasiIso

/-!
概要：元の整数係数の各列の全射擬同型を、同じtotalへ渡す。
方針：既存の同値関手と自然なtotalの比較を使い、既存HAの判定を適用する。
規約：同じ元の射と係数の宇宙を保つ。
使われ方：F8の全複体とČech細分の実際の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
local notation "up" => ComplexShape.up ℕ
variable {K L : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up}
variable [K.HasTotal up] [L.HasTotal up]
variable [(cechIntegerLiftBicomplex K).HasTotal up] [(cechIntegerLiftBicomplex L).HasTotal up]

/-- 元の各列の擬同型と各成分の全射性から、同じtotalの射も擬同型。 -/
theorem cechIntegerLiftTotal_quasiIso_of_columns (f : K ⟶ L)
    (hf : ∀ a, QuasiIso (f.f a))
    (hs : ∀ a b, Function.Surjective (((f.f a).f b).hom)) :
    QuasiIso (HomologicalComplex₂.total.map f up) := by
  apply (cechIntegerLiftTotal_quasiIso_iff f).mp
  apply SerrePositivity.HomologicalAlgebra.bicomplexTotal_quasiIso_of_columns
  · intro a
    letI := hf a
    exact inferInstanceAs (QuasiIso
      ((cechIntegerLiftFunctor.mapHomologicalComplex up).map (f.f a)))
  · intro a b
    exact hs a b

end SerrePositivity.AlgebraicGeometry
