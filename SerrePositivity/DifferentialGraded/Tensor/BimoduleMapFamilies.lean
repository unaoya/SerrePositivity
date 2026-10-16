module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMapNaturality
public import SerrePositivity.DifferentialGraded.Bimodule.Category

/-! # 相対tensorの値のmapを全Hom自然な右加群射へ束ねる -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]
variable {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}

/-- tensorの値のmapを右B加群の実際の閉零射へ持ち上げる。 -/
def composeRightMap (f : P ⟶ P') (g : Q ⟶ Q') (e : E) :
    ForgetEnrichment.of (Complex A)
      ((compose A B C E (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q)).rightAt e) ⟶
    ForgetEnrichment.of (Complex A)
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).rightAt e) :=
  moduleMorphismMk A B
    (M := (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).rightAt e)
    (N := (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).rightAt e)
    (fun b => composeValueHom A B C E f g b.unop e)
    (fun b b' => composeValueHom_right_naturality A B C E f g b b' e)

@[simp]
lemma composeRightMap_eval (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    (moduleEvaluation A B b).map (composeRightMap A B C E f g e) =
      composeValueHom A B C E f g b e :=
  moduleMorphismMk_eval A B
    (M := (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).rightAt e)
    (N := (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).rightAt e)
    (fun b => composeValueHom A B C E f g b.unop e)
    (fun b b' => composeValueHom_right_naturality A B C E f g b b' e) b

@[simp]
lemma composeRightMap_component (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    moduleMorphismComponent A B
      ((compose A B C E (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q)).rightAt e)
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).rightAt e)
      (composeRightMap A B C E f g e) b = composeValueHom A B C E f g b e :=
  composeRightMap_eval A B C E f g b e

/-- この右加群射族は、左E作用の主Hom endに関しても全次数で自然。 -/
lemma composeRightMap_naturality (f : P ⟶ P') (g : Q ⟶ Q') (e e' : E) :
    (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).toFunctor.map e e' ≫
      moduleHomPostcompose A B _ _ _ (composeRightMap A B C E f g e') =
    (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).toFunctor.map e e' ≫
      moduleHomPrecompose A B _ _ _ (composeRightMap A B C E f g e) := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [composeRightMap_component]
  have hh := composeValueHom_left_naturality A B C E f g b e e'
  change ((compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).toFunctor.map e e' ≫
      moduleHomπ A B _ _ b) ≫ _ =
    ((compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).toFunctor.map e e' ≫
      moduleHomπ A B _ _ b) ≫ _ at hh
  exact (Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _))

end SerrePositivity.DifferentialGraded.BimoduleTensor
