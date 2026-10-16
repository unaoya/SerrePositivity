module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorRightValueHomNaturality
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
lemma associatorValue_right_naturality (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) :
    associatorLeftBMap A B C E F P Q R b b' f ≫
      homPostcompose ((compose A B E F (compose A B C E P Q) R).value b.unop f)
        (associatorValueIso A B C E F P Q R b'.unop f).hom =
    associatorRightBMap A B C E F P Q R b b' f ≫
      homPrecompose (associatorValueIso A B C E F P Q R b.unop f).hom
        ((compose A B C F P (compose A C E F Q R)).value b'.unop f) := by
  simpa only [associatorValueHom_eq] using
    associatorValueHom_right_naturality A B C E F P Q R b b' f

lemma associatorValue_right_naturality_actual (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b b' : Bᵒᵖ) (f : F) :
    ((compose A B E F (compose A B C E P Q) R).rightAt f).map b b' ≫
      homPostcompose ((compose A B E F (compose A B C E P Q) R).value b.unop f)
        (associatorValueIso A B C E F P Q R b'.unop f).hom =
    ((compose A B C F P (compose A C E F Q R)).rightAt f).map b b' ≫
      homPrecompose (associatorValueIso A B C E F P Q R b.unop f).hom
        ((compose A B C F P (compose A C E F Q R)).value b'.unop f) := by
  have h := associatorValue_right_naturality A B C E F P Q R b b' f
  unfold associatorLeftBMap associatorRightBMap at h
  exact h

/-- 固定F対象での結合比較を全dg自然な右B加群同型へ束ねる。 -/
def associatorRightModuleIso (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (f : F) :
    ForgetEnrichment.of (Complex A) ((compose A B E F (compose A B C E P Q) R).rightAt f) ≅
      ForgetEnrichment.of (Complex A) ((compose A B C F P (compose A C E F Q R)).rightAt f) :=
  moduleIsoMk A B
    (M := (compose A B E F (compose A B C E P Q) R).rightAt f)
    (N := (compose A B C F P (compose A C E F Q R)).rightAt f)
    (fun b => associatorValueIso A B C E F P Q R b.unop f)
    (fun b b' => associatorValue_right_naturality_actual A B C E F P Q R b b' f)

@[simp]
lemma associatorRightModuleIso_hom_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A)
        ((compose A B E F (compose A B C E P Q) R).rightAt f))
      (Y := ForgetEnrichment.of (Complex A)
        ((compose A B C F P (compose A C E F Q R)).rightAt f))
      (associatorRightModuleIso A B C E F P Q R f).hom =
      (associatorValueIso A B C E F P Q R b f).hom :=
  moduleIsoMk_hom_eval A B
    (M := (compose A B E F (compose A B C E P Q) R).rightAt f)
    (N := (compose A B C F P (compose A C E F Q R)).rightAt f) _ _ b

@[simp]
lemma associatorRightModuleIso_inv_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    (moduleEvaluation A B b).map
      (X := ForgetEnrichment.of (Complex A)
        ((compose A B C F P (compose A C E F Q R)).rightAt f))
      (Y := ForgetEnrichment.of (Complex A)
        ((compose A B E F (compose A B C E P Q) R).rightAt f))
      (associatorRightModuleIso A B C E F P Q R f).inv =
      (associatorValueIso A B C E F P Q R b f).inv :=
  moduleIsoMk_inv_eval A B
    (M := (compose A B E F (compose A B C E P Q) R).rightAt f)
    (N := (compose A B C F P (compose A C E F Q R)).rightAt f) _ _ b

end SerrePositivity.DifferentialGraded.BimoduleTensor
