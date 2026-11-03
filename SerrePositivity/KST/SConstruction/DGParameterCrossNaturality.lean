module
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # パラメータ横断のパラメータ射に関する自然性
概要：K′→K は、加群値を横切る元の符号付き交換と可換である。
方針：符号付き braiding と associator の自然性を適用する。
規約：交差因子の順を保持する。使われ方：実 tensor パラメータ作用の引き戻し。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

/-- 元のパラメータ横断は、パラメータ複体の chain map と可換。 -/
@[reassoc]
lemma dgParameterCross_naturality {K L : Complex A} (a : L ⟶ K) (P Q : Complex A) :
    (a ▷ (P ⊗ Q)) ≫ parameterCross K P Q =
      parameterCross L P Q ≫ (P ◁ (a ▷ Q)) := by
  have h := signedSwap_naturality a (𝟙 P)
  simp only [id_tensorHom, tensorHom_id] at h
  unfold parameterCross
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc, h,
    comp_whiskerRight, Category.assoc, associator_naturality_middle]
  simp only [Category.assoc]

end SerrePositivity.KST.SConstruction
