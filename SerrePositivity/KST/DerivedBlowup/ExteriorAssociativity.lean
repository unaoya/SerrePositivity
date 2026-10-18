module

public import SerrePositivity.KST.DerivedBlowup.ExteriorUnitLaws

/-!
概要：KST Def3.1 の Koszul 外積複体の乗法の結合則。
方針：三重同次 tensor に制限し、総外積への単射で結合性を比較する。
規約：既存 Ch(R) の associator を使う。
使われ方：Koszul チャートの一対象 dg 圏の圏法則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory MonoidalCategory HomologicalComplex

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：Koszul 外積複体の積はモノイダル圏の結合則を満たす。
方針：三重 tensor の成分で associator を評価し、総外積の mul_assoc を使う。
規約：KST Def3.1。使われ方：dg 圏の assoc。 -/
theorem exteriorKoszul_assoc (d : M →ₗ[R] R) :
    (α_ (exteriorKoszulCochain d) (exteriorKoszulCochain d)
        (exteriorKoszulCochain d)).inv ≫
      exteriorKoszulMultiplication d ▷ _ ≫ exteriorKoszulMultiplication d =
      _ ◁ exteriorKoszulMultiplication d ≫ exteriorKoszulMultiplication d := by
  apply DifferentialGraded.rightTriple_ext
  intro i j k n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x yz
  induction yz using TensorProduct.inductionOn with
  | tmul y z =>
    change (exteriorKoszulMultiplication d).f n
      ((exteriorKoszulMultiplication d ▷ _).f n
        ((α_ (exteriorKoszulCochain d) (exteriorKoszulCochain d)
          (exteriorKoszulCochain d)).inv.f n
          (ιTensorObj (exteriorKoszulCochain d)
            (exteriorKoszulCochain d ⊗ exteriorKoszulCochain d)
            i (j + k) n hn
            (x ⊗ₜ[R] ιTensorObj (exteriorKoszulCochain d)
              (exteriorKoszulCochain d) j k (j + k) rfl (y ⊗ₜ[R] z))))) =
      (exteriorKoszulMultiplication d).f n
        ((_ ◁ exteriorKoszulMultiplication d).f n
          (ιTensorObj (exteriorKoszulCochain d)
            (exteriorKoszulCochain d ⊗ exteriorKoszulCochain d)
            i (j + k) n hn
            (x ⊗ₜ[R] ιTensorObj (exteriorKoszulCochain d)
              (exteriorKoszulCochain d) j k (j + k) rfl (y ⊗ₜ[R] z))))
    rw [DifferentialGraded.associator_inv_apply,
      DifferentialGraded.whiskerRight_apply, DifferentialGraded.whiskerLeft_apply]
    simp only [exteriorKoszulMultiplication_apply]
    apply exteriorCochainInclusion_injective d n
    simp only [exteriorCochainInclusion_product]
    exact mul_assoc _ _ _
  | add a b ha hb =>
    simp only [TensorProduct.tmul_add, map_add]
    exact congrArg₂ (· + ·) ha hb

end SerrePositivity.KST.DerivedBlowup
