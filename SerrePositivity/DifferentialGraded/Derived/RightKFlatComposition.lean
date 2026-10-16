module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorFunctor
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorEvaluation

/-! # 右相対K-flatな対象の充満部分圏での合成と導来比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 既存の合成対象とK-flat合成閉性の証拠を、同じ充満部分圏に束ねる。 -/
def rightKFlatCompose (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) : RightKFlatBimoduleCategory A C F :=
  ⟨BimoduleCategory.of A C F (compose A C E F (BimoduleCategory.underlying A C E Q.obj)
      (BimoduleCategory.underlying A E F R.obj)),
    Bimodule.rightRelativeKFlat_compose A C E F (BimoduleCategory.underlying A C E Q.obj)
      (BimoduleCategory.underlying A E F R.obj) Q.property R.property⟩

/-- 右K-flat対象の型付き表示に対する既存の導来合成関手。 -/
abbrev rightKFlatDerivedCompose (Q : RightKFlatBimoduleCategory A C E) :=
  derivedComposeWith A B C E Q.obj Q.property

def rightKFlatDerivedMap {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q.obj ⟶ Q'.obj) :
    rightKFlatDerivedCompose A B C E Q ⟶ rightKFlatDerivedCompose A B C E Q' :=
  derivedComposeWithMap A B C E Q.property Q'.property g

def rightKFlatDerivedAssociator (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) :
    rightKFlatDerivedCompose A B C E Q ⋙ rightKFlatDerivedCompose A B E F R ≅
      rightKFlatDerivedCompose A B C F (rightKFlatCompose A C E F Q R) :=
  derivedAssociatorIso A B C E F Q.obj R.obj Q.property R.property

omit [Small.{u} E] in
lemma rightKFlatDerivedCompose_map_base (Q : RightKFlatBimoduleCategory A C E)
    {P P' : BimoduleCategory A B C} (f : P ⟶ P') :
    (rightKFlatDerivedCompose A B C E Q).map ((bimoduleToDerived A B C).map f) =
      (bimoduleToDerived A B E).map (composeMap A B C E f (𝟙 Q.obj)) :=
  derivedComposeWith_map_base A B C E Q.obj Q.property f

omit [Small.{u} E] in
lemma rightKFlatDerivedMap_base_app {Q Q' : RightKFlatBimoduleCategory A C E}
    (g : Q.obj ⟶ Q'.obj) (P : BimoduleCategory A B C) :
    (rightKFlatDerivedMap A B C E g).app ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g) :=
  derivedComposeWithMap_base_app A B C E Q.property Q'.property g P

lemma rightKFlatDerivedAssociator_base_app (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) (P : BimoduleCategory A B C) :
    (rightKFlatDerivedAssociator A B C E F Q R).hom.app ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B F).map
        (associatorIso A B C E F (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q.obj) (BimoduleCategory.underlying A E F R.obj)).hom
      :=
  derivedAssociatorIso_base_app A B C E F Q.obj R.obj Q.property R.property P

end SerrePositivity.DifferentialGraded.BimoduleTensor
