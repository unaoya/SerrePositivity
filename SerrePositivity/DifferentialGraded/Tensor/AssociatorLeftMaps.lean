module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorLeftAction
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation
public import SerrePositivity.DifferentialGraded.Bimodule.ActionEvaluation

/-! # 反復tensorの左端dg作用の主Homとcochain評価 -/
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

/-- 左括弧の値に固定した全次数の作用cochain。 -/
@[irreducible]
def associatorLeftCochain (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f f' : F) (p : ℤ) (g : GradedHom A f f' p) :
    Cochain ((compose A B E F (compose A B C E P Q) R).value b f)
      ((compose A B E F (compose A B C E P Q) R).value b f') p :=
  (compose A B E F (compose A B C E P Q) R).leftCochain g b

/-- 右括弧の値に固定した全次数の作用cochain。 -/
@[irreducible]
def associatorRightCochain (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f f' : F) (p : ℤ) (g : GradedHom A f f' p) :
    Cochain ((compose A B C F P (compose A C E F Q R)).value b f)
      ((compose A B C F P (compose A C E F Q R)).value b f') p :=
  (compose A B C F P (compose A C E F Q R)).leftCochain g b

lemma associatorLeftCochain_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) {p m n : ℤ} (g : GradedHom A f f' p)
    (v : ((compose A B E F (compose A B C E P Q) R).value b f).X m) (hn : m + p = n) :
    (associatorLeftCochain A B C E F P Q R b f f' p g).v m n hn v =
      SerrePositivity.DifferentialGraded.leftAction A
        ((compose A B E F (compose A B C E P Q) R).leftAt b) g v hn := by
  unfold associatorLeftCochain
  exact Bimodule.leftCochain_apply A B F _ g b v hn

lemma associatorRightCochain_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) {p m n : ℤ} (g : GradedHom A f f' p)
    (v : ((compose A B C F P (compose A C E F Q R)).value b f).X m) (hn : m + p = n) :
    (associatorRightCochain A B C E F P Q R b f f' p g).v m n hn v =
      SerrePositivity.DifferentialGraded.leftAction A
        ((compose A B C F P (compose A C E F Q R)).leftAt b) g v hn := by
  unfold associatorRightCochain
  exact Bimodule.leftCochain_apply A B F _ g b v hn

/-- 左括弧の合成のF作用を、その値の主Hom間の射として固定する。 -/
@[irreducible]
def associatorLeftMap (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f f' : F) : (f ⟶[Complex A] f') ⟶
    homComplex A ((compose A B E F (compose A B C E P Q) R).value b f)
      ((compose A B E F (compose A B C E P Q) R).value b f') :=
  (compose A B E F (compose A B C E P Q) R).toFunctor.map f f' ≫
    moduleHomπ A B ((compose A B E F (compose A B C E P Q) R).rightAt f)
      ((compose A B E F (compose A B C E P Q) R).rightAt f') b

/-- 右括弧の合成のF作用を、その値の主Hom間の射として固定する。 -/
@[irreducible]
def associatorRightMap (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f f' : F) : (f ⟶[Complex A] f') ⟶
    homComplex A ((compose A B C F P (compose A C E F Q R)).value b f)
      ((compose A B C F P (compose A C E F Q R)).value b f') :=
  (compose A B C F P (compose A C E F Q R)).toFunctor.map f f' ≫
    moduleHomπ A B ((compose A B C F P (compose A C E F Q R)).rightAt f)
      ((compose A B C F P (compose A C E F Q R)).rightAt f') b

lemma associatorLeftMap_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) (p : ℤ) (g : GradedHom A f f' p) :
    (associatorLeftMap A B C E F P Q R b f f').f p g =
      associatorLeftCochain A B C E F P Q R b f f' p g := by
  unfold associatorLeftMap associatorLeftCochain
  rfl

lemma associatorRightMap_apply (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f f' : F) (p : ℤ) (g : GradedHom A f f' p) :
    (associatorRightMap A B C E F P Q R b f f').f p g =
      associatorRightCochain A B C E F P Q R b f f' p g := by
  unfold associatorRightMap associatorRightCochain
  rfl


end SerrePositivity.DifferentialGraded.BimoduleTensor
