module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0Stage
public import SerrePositivity.AlgebraicGeometry.FullCechH0KernelEvaluation

/-!
概要：Frobenius 各段からの Čech H⁰ 比較の逆像を零次コサイクルで表示する。
方針：標準写像との整合性と H⁰・核の自然性を合成する。
規約：右辺は各標準開の係数順極限への実際の標準写像。
使われ方：スカラー類と Čech 増大写像の同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι] [Fintype ι]
variable (D : Finset ι ⥤ CommAlgCat.{u} R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

/-- Frobenius 各段の適合切断に対応する H⁰ 類の零次コサイクルは各成分の標準像。 -/
theorem algebraCechFrobeniusH0ColimitIso_inv_of_cocycle (n : ℕ)
    (s : fullAlgebraCechEqualizer D) (t : Fin 1 → ι) :
    ((fullCechH0KernelIso (colimit
      (algebraCechFrobeniusCoefficientFunctor D p hp hR))).hom.hom
        ((algebraCechFrobeniusH0ColimitIso D p hp hR).inv.hom
          (frobeniusDirectLimitOf (fullAlgebraCechEqualizer D) p hp
            (algebraCechEqualizer_primeCast D p hR) n s))).val t =
      ((colimit.ι (algebraCechFrobeniusCoefficientFunctor D p hp hR) n).app
        (cechTupleSupport t)).hom (s.val t) := by
  rw [algebraCechFrobeniusH0ColimitIso_inv_of, fullCechH0KernelIso_naturality_apply]
  exact congrArg (fun x ↦
    ((colimit.ι (algebraCechFrobeniusCoefficientFunctor D p hp hR) n).app
      (cechTupleSupport t)).hom (x t)) (fullAlgebraCechIntH0Equiv_kernel D s)

end SerrePositivity.AlgebraicGeometry
