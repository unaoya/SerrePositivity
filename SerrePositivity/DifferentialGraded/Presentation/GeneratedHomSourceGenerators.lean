module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSourceContainment
/-!
概要：元の小出発提示の全 Hom 像を含む κ 個以下の指定係数族を構成する。
方針：対象対・整数次数・固定自由基底で係数を添字付けし、基底像から全像を回収する。
規約：元の関係部分加群と実 dg 関手を保持する。
使われ方：c′ の共通係数閉包へ元の出発提示を収容する基底族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)

abbrev DGCodeHomGeneratorIndex : Type u :=
  c.Objects R κ × c.Objects R κ × ULift.{u} ℤ × κ.ord.ToType

lemma dgCodeHomGeneratorIndex_cardinal_le (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.mk (DGCodeHomGeneratorIndex R κ c) ≤ κ := by
  have hO : Cardinal.mk (c.Objects R κ) ≤ κ := le_of_lt
    (by simpa only [DGCategoryPresentationCode.Objects, Cardinal.mk_toType, Cardinal.card_ord] using Cardinal.mk_Iio_lt c.ordinal (by simp))
  have hZ : Cardinal.mk (ULift.{u} ℤ) ≤ κ := Cardinal.mk_le_aleph0.trans hκ
  simp only [DGCodeHomGeneratorIndex, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_toType, Cardinal.card_ord]
  exact Cardinal.mul_le_of_le hκ hO
    (Cardinal.mul_le_of_le hκ hO (Cardinal.mul_le_of_le hκ hZ le_rfl))

variable {J : Type u} (D : Type v) [DGCategory R D] (value : J → D)
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))

def dgCodeGeneratorSource (i : DGCodeHomGeneratorIndex R κ c) : J := (F.obj i.1).label

def dgCodeGeneratorTarget (i : DGCodeHomGeneratorIndex R κ c) : J := (F.obj i.2.1).label

def dgCodeGeneratorDegree (i : DGCodeHomGeneratorIndex R κ c) : ℤ := i.2.2.1.down

def dgCodeGeneratorCoefficient (i : DGCodeHomGeneratorIndex R κ c) :
    GradedHom R (value (dgCodeGeneratorSource R κ c D value F i))
      (value (dgCodeGeneratorTarget R κ c D value F i)) (dgCodeGeneratorDegree R κ c i) :=
  (F.map i.1 i.2.1).f i.2.2.1.down (dgCodeHomGenerator R κ c i.1 i.2.1 i.2.2.1.down i.2.2.2)

lemma dgCodeGeneratorImage_contains :
    ∀ x y n (f : GradedHom R x y n), (F.map x y).f n f ∈
      DGGeneratedHomWord.linearSpan (dgCodeGeneratorSource R κ c D value F)
        (dgCodeGeneratorTarget R κ c D value F) (dgCodeGeneratorDegree R κ c) R D value
        (dgCodeGeneratorCoefficient R κ c D value F) (F.obj x).label (F.obj y).label n := by
  apply generatedHomImage_of_codeGenerators R κ c _ _ _ D value _ F
  intro x y n b
  exact DGGeneratedHomWord.evaluate_mem_span _ _ _ R D value
    (dgCodeGeneratorCoefficient R κ c D value F) (.generator ⟨x, y, ULift.up n, b⟩)

end SerrePositivity.DifferentialGraded
