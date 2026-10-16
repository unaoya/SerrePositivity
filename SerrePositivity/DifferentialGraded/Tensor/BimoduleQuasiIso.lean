module
public import SerrePositivity.DifferentialGraded.Bimodule.RelativeKFlat
public import SerrePositivity.DifferentialGraded.Bimodule.QuasiIso
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
public import SerrePositivity.DifferentialGraded.Tensor.QuasiIsoLeft

/-! # bimodule合成の準同型保存に必要な片側の条件 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 後の因子の右制限が相対K-flatなら、前の因子の任意の準同型を保存する。 -/
lemma composeMap_first_quasiIso {P P' : BimoduleCategory A B C} (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (f : P ⟶ P') (hf : BimoduleCategory.quasiIso A B C f) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E f (𝟙 Q)) := by
  intro b e
  rw [composeMap_value_eval]
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id]
  exact moduleRelativeKFlat_preserves_leftQuasiIso A C
    ((BimoduleCategory.underlying A C E Q).rightAt e) (hQ e)
    ((BimoduleCategory.leftEvaluation A B C b).map f)
    (BimoduleCategory.quasiIso_leftEvaluation A B C hf b)

/-- 後の因子の両端の右制限が全Hom射影的なら、前の因子は任意でよい。 -/
lemma composeMap_second_projective_quasiIso (P : BimoduleCategory A B C)
    {Q Q' : BimoduleCategory A C E}
    (hQ : ∀ e, moduleHomotopicallyProjective A C
      ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C
      ((BimoduleCategory.evaluation A C E e).obj Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E (𝟙 P) g) := by
  intro b e
  rw [composeMap_value_eval]
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id]
  exact BalancedTensor.rightTensor_projective_quasiIso A C
    ((BimoduleCategory.underlying A B C P).leftAt b) (hQ e) (hQ' e)
    ((BimoduleCategory.evaluation A C E e).map g)
    (BimoduleCategory.quasiIso_evaluation A C E hg e)

/-- 片側の全Hom射影性で、両変数の準同型を同時に保存する。 -/
lemma composeMap_projective_quasiIso {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E}
    (hQ : ∀ e, moduleHomotopicallyProjective A C
      ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C
      ((BimoduleCategory.evaluation A C E e).obj Q'))
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hf : BimoduleCategory.quasiIso A B C f) (hg : BimoduleCategory.quasiIso A C E g) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E f g) := by
  have h₁ := composeMap_first_quasiIso A B C E Q
    (Bimodule.rightRelativeKFlat_of_rightAt_projective A C E
      (BimoduleCategory.underlying A C E Q) hQ) f hf
  have h₂ := composeMap_second_projective_quasiIso A B C E P' hQ hQ' g hg
  have he := composeMap_comp A B C E f (𝟙 P') (𝟙 Q) g
  simp only [Category.comp_id, Category.id_comp] at he
  rw [he]
  exact (BimoduleCategory.quasiIso A B E).comp_mem _ _ h₁ h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
