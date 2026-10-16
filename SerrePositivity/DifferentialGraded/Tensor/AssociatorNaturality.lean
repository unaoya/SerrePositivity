module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorMapNaturality
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.TripleFunctors

/-! # 閉零bimodule射の三変数に関する結合比較の生成元自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]
variable {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
  {R R' : BimoduleCategory A E F}
local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "P₁" => BimoduleCategory.underlying A B C P'
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "Q₁" => BimoduleCategory.underlying A C E Q'
local notation "R₀" => BimoduleCategory.underlying A E F R
local notation "R₁" => BimoduleCategory.underlying A E F R'

/-- 実際の閉零bimodule射の三変数についての結合同型の自然性。 -/
lemma associatorIso_naturality (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    composeMap A B E F (composeMap A B C E f g) h ≫
      (associatorIso A B C E F P₁ Q₁ R₁).hom =
    (associatorIso A B C E F P₀ Q₀ R₀).hom ≫
      composeMap A B C F f (composeMap A C E F g h) := by
  apply BimoduleCategory.value_hom_ext A B F
  intro b d
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    associatorIso_hom_value_eval]
  exact associatorValue_map_naturality A B C E F f g h b d

/-- 二通りの反復合成の、閉零bimodule圏における三変数自然同型。 -/
def associatorNatIso : leftTripleFunctor A B C E F ≅ rightTripleFunctor A B C E F :=
  NatIso.ofComponents
    (fun X => associatorIso A B C E F (BimoduleCategory.underlying A B C X.1.1)
      (BimoduleCategory.underlying A C E X.1.2) (BimoduleCategory.underlying A E F X.2))
    (fun f => associatorIso_naturality A B C E F f.1.1 f.1.2 f.2)

@[simp]
lemma associatorNatIso_app
    (X : (BimoduleCategory A B C × BimoduleCategory A C E) × BimoduleCategory A E F) :
    (associatorNatIso A B C E F).app X =
      associatorIso A B C E F (BimoduleCategory.underlying A B C X.1.1)
        (BimoduleCategory.underlying A C E X.1.2) (BimoduleCategory.underlying A E F X.2) := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
