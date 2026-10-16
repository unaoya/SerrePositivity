module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHomNaturality

/-! # 結合比較の左端のdg作用との整合性 -/
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

/-- 結合比較は左F作用の主Hom写像と全次数で可換。 -/
lemma associatorValue_left_naturality (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) :
    associatorLeftMap A B C E F P Q R b f f' ≫
      homPostcompose ((compose A B E F (compose A B C E P Q) R).value b f)
        (associatorValueIso A B C E F P Q R b f').hom =
    associatorRightMap A B C E F P Q R b f f' ≫
      homPrecompose (associatorValueIso A B C E F P Q R b f).hom
        ((compose A B C F P (compose A C E F Q R)).value b f') := by
  simpa only [associatorValueHom_eq] using
    associatorValueHom_left_naturality A B C E F P Q R b f f'

end SerrePositivity.DifferentialGraded.BimoduleTensor
