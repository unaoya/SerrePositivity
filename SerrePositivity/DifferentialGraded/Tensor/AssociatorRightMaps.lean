module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightAction
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.UnitScalarEvaluation

/-! # 反復tensorの右B作用の主Homとcochain評価 -/
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

@[irreducible]
def associatorLeftBMap (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (f : F) : (b ⟶[Complex A] b') ⟶
    homComplex A ((compose A B E F (compose A B C E P Q) R).value b.unop f)
      ((compose A B E F (compose A B C E P Q) R).value b'.unop f) :=
  ((compose A B E F (compose A B C E P Q) R).rightAt f).map b b'

@[irreducible]
def associatorRightBMap (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (f : F) : (b ⟶[Complex A] b') ⟶
    homComplex A ((compose A B C F P (compose A C E F Q R)).value b.unop f)
      ((compose A B C F P (compose A C E F Q R)).value b'.unop f) :=
  ((compose A B C F P (compose A C E F Q R)).rightAt f).map b b'

@[irreducible]
def associatorLeftBCochain (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (f : F) (p : ℤ) (g : GradedHom A b b' p) :
    Cochain ((compose A B E F (compose A B C E P Q) R).value b.unop f)
      ((compose A B E F (compose A B C E P Q) R).value b'.unop f) p :=
  (((compose A B E F (compose A B C E P Q) R).rightAt f).map b b').f p g

@[irreducible]
def associatorRightBCochain (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (f : F) (p : ℤ) (g : GradedHom A b b' p) :
    Cochain ((compose A B C F P (compose A C E F Q R)).value b.unop f)
      ((compose A B C F P (compose A C E F Q R)).value b'.unop f) p :=
  (((compose A B C F P (compose A C E F Q R)).rightAt f).map b b').f p g

lemma associatorLeftBMap_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) (p : ℤ) (g : GradedHom A b b' p) :
    (associatorLeftBMap A B C E F P Q R b b' f).f p g =
      associatorLeftBCochain A B C E F P Q R b b' f p g := by
  unfold associatorLeftBMap associatorLeftBCochain
  rfl

lemma associatorRightBMap_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) (p : ℤ) (g : GradedHom A b b' p) :
    (associatorRightBMap A B C E F P Q R b b' f).f p g =
      associatorRightBCochain A B C E F P Q R b b' f p g := by
  unfold associatorRightBMap associatorRightBCochain
  rfl

lemma associatorLeftBCochain_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) {p m n : ℤ} (g : GradedHom A b b' p)
    (x : ((compose A B E F (compose A B C E P Q) R).value b.unop f).X m) (hn : m + p = n) :
    (associatorLeftBCochain A B C E F P Q R b b' f p g).v m n hn x =
      moduleAction A ((compose A B E F (compose A B C E P Q) R).rightAt f) g x hn := by
  unfold associatorLeftBCochain
  rfl

lemma associatorRightBCochain_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) {p m n : ℤ} (g : GradedHom A b b' p)
    (x : ((compose A B C F P (compose A C E F Q R)).value b.unop f).X m) (hn : m + p = n) :
    (associatorRightBCochain A B C E F P Q R b b' f p g).v m n hn x =
      moduleAction A ((compose A B C F P (compose A C E F Q R)).rightAt f) g x hn := by
  unfold associatorRightBCochain
  rfl


end SerrePositivity.DifferentialGraded.BimoduleTensor
