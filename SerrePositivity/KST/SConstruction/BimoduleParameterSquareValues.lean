module
public import SerrePositivity.DifferentialGraded.Bimodule.Value


/-! # パラメータ可換四角形の元の値での回収
概要：双加群の全 Hom での可換式を、元の二対象の値での可換式へ戻す。
方針：全加群 Hom の評価と元の閉零射の値を照合する。
規約：パラメータと全次数を保つ。使われ方：実 tensor による可換四角形の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [Small.{u} B] [DGCategory A C]

/-- 元の全 Hom で可換な K 四角形は、元の二対象の値でも全次数で可換。 -/
lemma bimoduleParameter_square_value {K : Complex A}
    {P P' N N' : BimoduleCategory A B C}
    (τ : BimoduleParamTrans A B C K (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A B C P'))
    (υ : BimoduleParamTrans A B C K (BimoduleCategory.underlying A B C N)
      (BimoduleCategory.underlying A B C N')) (f : P ⟶ N) (g : P' ⟶ N')
    (h : ∀ c, τ.app c ≫ moduleHomPostcompose A B _ _ _ (g.val c) =
      υ.app c ≫ moduleHomPrecompose A B _ _ _ (f.val c)) (b : B) (c : C) :
    Bimodule.paramValue A B C τ b c ≫
        homPostcompose ((BimoduleCategory.underlying A B C P).value b c)
          ((BimoduleCategory.valueEvaluation A B C b c).map g) =
      Bimodule.paramValue A B C υ b c ≫
        homPrecompose ((BimoduleCategory.valueEvaluation A B C b c).map f)
          ((BimoduleCategory.underlying A B C N').value b c) := by
  have hh := congrArg (fun k => k ≫ moduleHomπ A B
    ((BimoduleCategory.underlying A B C P).rightAt c)
    ((BimoduleCategory.underlying A B C N').rightAt c) b) (h c)
  simp only [Category.assoc] at hh
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π] at hh
  exact hh

end SerrePositivity.KST.SConstruction
