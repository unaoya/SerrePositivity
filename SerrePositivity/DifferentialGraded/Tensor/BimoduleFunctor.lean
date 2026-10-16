module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMapFamilies
public import SerrePositivity.DifferentialGraded.Bimodule.ValueExt

/-! # 全Hom自然な閉零bimodule圏上の相対tensor双関手 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 既存のbimodule対象の合成を全Hom自然な閉零射へ拡張する。 -/
def composeMap {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    BimoduleCategory.of A B E (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)) ⟶
    BimoduleCategory.of A B E (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')) :=
  ⟨composeRightMap A B C E f g, composeRightMap_naturality A B C E f g⟩

@[simp]
lemma composeMap_eval {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (e : E) :
    (BimoduleCategory.evaluation A B E e).map (composeMap A B C E f g) =
      composeRightMap A B C E f g e := rfl

@[simp]
lemma composeMap_value_eval {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    (BimoduleCategory.valueEvaluation A B E b e).map (composeMap A B C E f g) =
      composeValueMap A B C E f g b e :=
  (composeRightMap_eval A B C E f g b e).trans (composeValueHom_eq A B C E f g b e)

lemma composeMap_id (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) :
    composeMap A B C E (𝟙 P) (𝟙 Q) =
      𝟙 (BimoduleCategory.of A B E
        (compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q))) := by
  apply BimoduleCategory.value_hom_ext A B E
  intro b e
  rw [composeMap_value_eval, CategoryTheory.Functor.map_id]
  exact composeValueMap_id A B C E P Q b e

lemma composeMap_comp {P P' P'' : BimoduleCategory A B C}
    {Q Q' Q'' : BimoduleCategory A C E} (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    composeMap A B C E (f ≫ f') (g ≫ g') =
      composeMap A B C E f g ≫ composeMap A B C E f' g' := by
  apply BimoduleCategory.value_hom_ext A B E
  intro b e
  rw [composeMap_value_eval, (BimoduleCategory.valueEvaluation A B E b e).map_comp,
    composeMap_value_eval, composeMap_value_eval]
  exact composeValueMap_comp A B C E f f' g g' b e

/-- 全Hom自然性を射に保持した、実際の閉零bimodule圏上の合成双関手。 -/
def composeFunctor :
    BimoduleCategory A B C × BimoduleCategory A C E ⥤ BimoduleCategory A B E where
  obj PQ := BimoduleCategory.of A B E
    (compose A B C E (BimoduleCategory.underlying A B C PQ.1)
      (BimoduleCategory.underlying A C E PQ.2))
  map fg := composeMap A B C E fg.1 fg.2
  map_id PQ := composeMap_id A B C E PQ.1 PQ.2
  map_comp fg gh := composeMap_comp A B C E fg.1 gh.1 fg.2 gh.2

end SerrePositivity.DifferentialGraded.BimoduleTensor
