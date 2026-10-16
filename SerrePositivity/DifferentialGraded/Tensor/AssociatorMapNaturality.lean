module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorMapElements
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHom

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

lemma associatorValueHom_map_naturality (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (d : F) :
    composeValueHom A B E F (composeMap A B C E f g) h b d ≫
      associatorValueHom A B C E F P₁ Q₁ R₁ b d =
    associatorValueHom A B C E F P₀ Q₀ R₀ b d ≫
      composeValueHom A B C F f (composeMap A C E F g h) b d := by
  apply Cochain.ofHom_injective
  apply associatorLeft_cochain_element_ext A B C E F P₀ Q₀ R₀ b d
  intro c e k r s i m n hi hm hn τ q v
  simp only [add_zero] at hn
  cases hn
  simp only [Cochain.ofHom_v]
  change associatorValueComponent A B C E F P₁ Q₁ R₁ b d m
    (composeMapComponent A B E F (composeMap A B C E f g) h b d m
      (associatorLeftElement A B C E F P₀ Q₀ R₀ b c e d τ q v hi hm)) =
    composeMapComponent A B C F f (composeMap A C E F g h) b d m
      (associatorValueComponent A B C E F P₀ Q₀ R₀ b d m
        (associatorLeftElement A B C E F P₀ Q₀ R₀ b c e d τ q v hi hm))
  exact associatorComponent_map_element A B C E F f g h b c e d
    (l := k + r) τ q v hi rfl hm

/-- 値のchain mapとしての、元の結合同型の閉零三変数自然性。 -/
lemma associatorValue_map_naturality (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R')
    (b : B) (d : F) :
    composeValueMap A B E F (composeMap A B C E f g) h b d ≫
      (associatorValueIso A B C E F P₁ Q₁ R₁ b d).hom =
    (associatorValueIso A B C E F P₀ Q₀ R₀ b d).hom ≫
      composeValueMap A B C F f (composeMap A C E F g h) b d := by
  simpa only [composeValueHom_eq, associatorValueHom_eq] using
    associatorValueHom_map_naturality A B C E F f g h b d

end SerrePositivity.DifferentialGraded.BimoduleTensor
