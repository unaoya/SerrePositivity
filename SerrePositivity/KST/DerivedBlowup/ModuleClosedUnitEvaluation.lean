module

public import SerrePositivity.DifferentialGraded.Module.Action
public import SerrePositivity.DifferentialGraded.Module.ClosedMaps

/-!
概要：KST §3.1 の指定閉零係数射の加群作用の計算。
方針：閉零射の cochain を単位複体の生成元で評価する。
規約：全次数 dg 加群の実際の作用を使う。
使われ方：構造加群の局所単位生成元と指定遷移の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open DifferentialGraded CochainComplex HomComplex

variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：指定閉零係数射の通常 chain map 作用はその閉零 cycle の斉次作用。
方針：mapFromUnit の cochain 公式と単位射の後合成の評価公式を使う。
規約：KST §3.1。使われ方：指定局所遷移の生成元上での計算。 -/
theorem moduleClosedUnitAction_apply (M : RightModule R D) {x y : Dᵒᵖ}
    (t : 𝟙_ (Complex R) ⟶ (x ⟶[Complex R] y)) (q : ℤ) (v : (M.obj x).X q) :
    (mapFromUnit R (M.obj x) (M.obj y) (t ≫ M.map x y)).f q v =
      moduleAction R M (cycleFromUnit (x ⟶[Complex R] y) t).val v (add_zero q) := by
  change (Cochain.ofHom (mapFromUnit R _ _ (t ≫ M.map x y))).v q q (add_zero q) v = _
  rw [mapFromUnit_cochain, cycleFromUnit_postcomp]
  rfl

end SerrePositivity.KST.DerivedBlowup
