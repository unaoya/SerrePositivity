module

public import SerrePositivity.AlgebraicGeometry.OpenFamilyCechRefinementCoefficients
public import SerrePositivity.AlgebraicGeometry.OpenFamilyCechPerfectCoefficients
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitRingIsoNaturality

/-!
概要：同じ開の細分の構造層の可換四角を、実際の Frobenius 係数へ移す。
方針：元の可換四角に、同じ環同型の Frobenius 自然性を適用する。
規約：元の開の制限と混合積の細分の射を保持する。
使われ方：二重 Čech の縦方向の実際の係数比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι κ : Type}
variable (U : ι → Y.Opens) (V : κ → Y.Opens) (ρ : κ → ι) (hV : ∀ j, V j ≤ U (ρ j))
variable (p : ℕ) (hp : p.Prime)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ開の細分に、元のタプル開と混合積の Frobenius 係数の比較は自然。 -/
theorem openFamilyCechPerfectSectionsEquiv_refinement (n : SimplexCategory)
    (t : Fin (n.len + 1) → κ)
    (hM : (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
      (op (schemeCechTupleOpen f U (op n) (fun j ↦ ρ (t j))))) = 0)
    (hN : (p : ((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
      (op (schemeCechTupleOpen f V (op n) t))) = 0)
    (z : FrobeniusDirectLimit (((Arrow.mk f).cechNerve.obj (op n)).presheaf.obj
      (op (schemeCechTupleOpen f U (op n) (fun j ↦ ρ (t j))))) p hp hM) :
    openFamilyCechPerfectSectionsEquiv f V p hp n t hN
        (frobeniusDirectLimitMap p hp hM hN
          (((Arrow.mk f).cechNerve.obj (op n)).presheaf.map
            (homOfLE (openFamilyCechRefinementOpen_le f U V ρ hV n t)).op).hom z) =
      frobeniusDirectLimitMap p hp
        (openFamilyCechMixed_primeCast f U p n (fun j ↦ ρ (t j)) hM)
        (openFamilyCechMixed_primeCast f V p n t hN)
        (Scheme.Γ.map (openFamilyCechRefinementMap f U V ρ hV n t).op).hom
        (openFamilyCechPerfectSectionsEquiv f U p hp n (fun j ↦ ρ (t j)) hM z) := by
  apply frobeniusDirectLimitRingIso_naturality p hp hM
    (openFamilyCechMixed_primeCast f U p n (fun j ↦ ρ (t j)) hM) hN
    (openFamilyCechMixed_primeCast f V p n t hN)
    (openFamilyCechSectionsIso f U n (fun j ↦ ρ (t j))) (openFamilyCechSectionsIso f V n t)
    _ _ ?_ z
  exact openFamilyCechSectionsIso_refinement f U V ρ hV n t

end SerrePositivity.AlgebraicGeometry
