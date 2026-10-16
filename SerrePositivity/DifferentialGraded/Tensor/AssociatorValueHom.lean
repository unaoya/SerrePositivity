module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorComponent
public import SerrePositivity.DifferentialGraded.Complexes.MapComponentFunctions

/-! # 結合比較と左作用の二段の生成元輸送 -/
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

/-- 固定した成分関数を使って結合比較のchain mapを表示する。 -/
def associatorValueHom (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    (compose A B E F (compose A B C E P Q) R).value b f ⟶
      (compose A B C F P (compose A C E F Q R)).value b f :=
  chainMapOfComponentFunctions (associatorValueIso A B C E F P Q R b f).hom
    (associatorValueComponent A B C E F P Q R b f)
    (associatorValueComponent_eq A B C E F P Q R b f)

@[simp]
lemma associatorValueHom_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) (n : ℤ)
    (z : ((compose A B E F (compose A B C E P Q) R).value b f).X n) :
    (associatorValueHom A B C E F P Q R b f).f n z =
      associatorValueComponent A B C E F P Q R b f n z := rfl

lemma associatorValueHom_eq (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    associatorValueHom A B C E F P Q R b f =
      (associatorValueIso A B C E F P Q R b f).hom :=
  chainMapOfComponentFunctions_eq _ _ _

end SerrePositivity.DifferentialGraded.BimoduleTensor
