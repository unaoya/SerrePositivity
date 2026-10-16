module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightComponentCompatibility
public import SerrePositivity.DifferentialGraded.Module.Isomorphism

/-! # 結合比較の右B全Hom自然性と右加群同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 右B作用の主Hom写像についての結合比較の自然性。 -/
lemma associatorValueHom_right_naturality (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) :
    associatorLeftBMap A B C E F P Q R b b' f ≫
      homPostcompose ((compose A B E F (compose A B C E P Q) R).value b.unop f)
        (associatorValueHom A B C E F P Q R b'.unop f) =
    associatorRightBMap A B C E F P Q R b b' f ≫
      homPrecompose (associatorValueHom A B C E F P Q R b.unop f)
        ((compose A B C F P (compose A C E F Q R)).value b'.unop f) := by
  apply hom_naturality_of_apply
  intro p g
  rw [associatorLeftBMap_apply, associatorRightBMap_apply]
  apply associatorLeft_cochain_element_ext A B C E F P Q R b.unop f
  intro c e k r s i m n hi hm hn t q v
  have hL := cochain_comp_ofHom_apply
    (associatorLeftBCochain A B C E F P Q R b b' f p g)
    (associatorValueHom A B C E F P Q R b'.unop f) hn
    (associatorLeftElement A B C E F P Q R b.unop c e f (n := m) t q v hi hm)
  have hR := cochain_ofHom_comp_apply
    (associatorValueHom A B C E F P Q R b.unop f)
    (associatorRightBCochain A B C E F P Q R b b' f p g) hn
    (associatorLeftElement A B C E F P Q R b.unop c e f (n := m) t q v hi hm)
  have hc := associatorComponent_rightCochain_compatibility A B C E F P Q R b b' c e f
    hi hm hn g t q v
  simp only [associatorValueHom_apply] at hL hR
  exact hL.trans (hc.trans hR.symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
