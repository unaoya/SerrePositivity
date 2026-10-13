module

public import SerrePositivity.Spectra.SymmetricSequence.TensorPowerMultiplication
public import SerrePositivity.Spectra.SymmetricSequence.DayMonoidal

/-! # 反復テンソルの対称列の単位射

単位対象の左Kan拡張の普遍性から、第0段の恒等射を単位射へ延長する。
因子化・一意性と左右の標準射上の単位比較を証明する。
convolution全体の左右単位則は `TensorPowerUnitLaws` で証明する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [HasColimitsOfSize.{0, 0} C]

/-- 第0段の恒等射を、一点圏からの自然変換として読む。 -/
def tensorPowerUnitData (X : C) :
    Functor.fromPUnit.{0} (𝟙_ C) ⟶
      Functor.fromPUnit.{0} (FiniteBijection.of 0) ⋙ tensorPowerSequence X where
  app _ := 𝟙 (𝟙_ C)
  naturality _ _ _ := by
    change 𝟙 (𝟙_ C) ≫ 𝟙 (𝟙_ C) =
      𝟙 (𝟙_ C) ≫ (tensorPowerSequence X).map (𝟙 (FiniteBijection.of 0))
    erw [CategoryTheory.Functor.map_id]
    rfl

/-- 第0段の恒等射から、単位対象の普遍性によって得る単位射。 -/
def tensorPowerUnit (X : C) : convolutionTensorUnit ⟶ tensorPowerSequence X :=
  (convolutionTensorUnit (C := C)).descOfIsLeftKanExtension convolutionUnitCan
    (tensorPowerSequence X) (tensorPowerUnitData X)

/-- 単位射は空集合での恒等射を因子化する。 -/
lemma tensorPowerUnit_fac (X : C) :
    convolutionUnitCan ≫ Functor.whiskerLeft (Functor.fromPUnit.{0} (FiniteBijection.of 0))
      (tensorPowerUnit X) = tensorPowerUnitData X :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

/-- 標準射と単位射の第0段の成分との合成は恒等射。 -/
lemma tensorPowerUnit_fac_app (X : C) :
    convolutionUnitCan.app ⟨⟨⟩⟩ ≫ (tensorPowerUnit X).app (FiniteBijection.of 0) = 𝟙 (𝟙_ C) :=
  congrArg (fun f ↦ f.app ⟨⟨⟩⟩) (tensorPowerUnit_fac X)

/-- 同じ第0段の因子化を与える単位射は一意。 -/
lemma tensorPowerUnit_unique (X : C) (η : convolutionTensorUnit ⟶ tensorPowerSequence X)
    (h : convolutionUnitCan ≫ Functor.whiskerLeft
        (Functor.fromPUnit.{0} (FiniteBijection.of 0)) η = tensorPowerUnitData X) :
    η = tensorPowerUnit X := by
  apply Functor.hom_ext_of_isLeftKanExtension _ convolutionUnitCan
  exact h.trans (tensorPowerUnit_fac X).symm

/-- 左単位の標準射上で、乗法との合成は基礎圏の左単位子に一致する。 -/
lemma tensorPowerUnit_left_generator (X : C) (n : ℕ) :
    (convolutionUnitCan.app ⟨⟨⟩⟩ ▷ TensorPowers.power X n) ≫
        ((tensorPowerUnit X).app (FiniteBijection.of 0) ▷ TensorPowers.power X n) ≫
        (convolutionUnit (tensorPowerSequence X) (tensorPowerSequence X)).app
          (FiniteBijection.of 0, FiniteBijection.of n) ≫
        (tensorPowerMultiplication X).app (FiniteBijection.of (0 + n)) =
      (λ_ (TensorPowers.power X n)).hom ≫
        eqToHom (congrArg (TensorPowers.power X) (Nat.zero_add n).symm) := by
  rw [← comp_whiskerRight_assoc, tensorPowerUnit_fac_app]
  erw [id_whiskerRight, Category.id_comp]
  rw [tensorPowerMultiplication_fac_app]
  exact TensorPowers.appendIso_zero_left X n

/-- 右単位の標準射上で、乗法との合成は基礎圏の右単位子に一致する。 -/
lemma tensorPowerUnit_right_generator (X : C) (n : ℕ) :
    (TensorPowers.power X n ◁ convolutionUnitCan.app ⟨⟨⟩⟩) ≫
        (TensorPowers.power X n ◁ (tensorPowerUnit X).app (FiniteBijection.of 0)) ≫
        (convolutionUnit (tensorPowerSequence X) (tensorPowerSequence X)).app
          (FiniteBijection.of n, FiniteBijection.of 0) ≫
        (tensorPowerMultiplication X).app (FiniteBijection.of (n + 0)) =
      (ρ_ (TensorPowers.power X n)).hom := by
  rw [← whiskerLeft_comp_assoc, tensorPowerUnit_fac_app]
  erw [whiskerLeft_id, Category.id_comp]
  rw [tensorPowerMultiplication_fac_app]
  exact TensorPowers.appendIso_zero_right X n

variable [MonoidalClosed C]

/-- 登録済みのモノイダル単位からの射として読む単位射。 -/
def tensorPowerUnitHom (X : C) : 𝟙_ (SymmetricSequence C) ⟶ tensorPowerSequence X :=
  tensorPowerUnit X

/-- 登録済みの単位からの射は、左Kan拡張から得た単位射そのもの。 -/
lemma tensorPowerUnitHom_eq (X : C) : tensorPowerUnitHom X = tensorPowerUnit X := rfl

end SerrePositivity.SymmetricSequence
