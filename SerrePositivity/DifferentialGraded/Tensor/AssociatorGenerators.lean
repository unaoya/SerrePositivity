module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValues
public import SerrePositivity.DifferentialGraded.Tensor.ChangeLeft

/-! # 実際のbimodule結合比較と三重生成元 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左括弧の実際の合成bimoduleの値への三重包含。 -/
def associatorLeftι (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) :
    R.value e f ⊗ (Q.value c e ⊗ P.value b c) ⟶
      (compose A B E F (compose A B C E P Q) R).value b f :=
  (R.value e f ◁ BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c) ≫
    BalancedTensor.ι A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e

/-- 右括弧の実際の合成bimoduleの値への三重包含。 -/
def associatorRightι (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) :
    R.value e f ⊗ (Q.value c e ⊗ P.value b c) ⟶
      (compose A B C F P (compose A C E F Q R)).value b f :=
  BalancedTensor.Fubini.rightι A C E Q (R.rightAt f) (P.leftAt b) c e

/-- 左加群構造の比較による輸送は実際の三重包含をFubiniの包含へ送る。 -/
lemma associatorLeftι_transport (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f : F) :
    associatorLeftι A B C E F P Q R b c e f ≫
      eqToHom (congrArg (fun N : LeftModule A E => BalancedTensor.obj A E (R.rightAt f) N)
        (compose_leftAt_eq A B C E P Q b)) =
    BalancedTensor.Fubini.leftι A C E Q (R.rightAt f) (P.leftAt b) c e := by
  have h := BalancedTensor.ι_changeLeft_hom A E (R.rightAt f)
    (compose_leftAt_eq A B C E P Q b) e
  have he : eqToHom (congrArg (fun N : LeftModule A E => R.value e f ⊗ N.obj e)
      (compose_leftAt_eq A B C E P Q b)) =
      𝟙 (R.value e f ⊗ BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b)) := rfl
  have hh := h.trans (congrArg (fun g : R.value e f ⊗
      BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b) ⟶ R.value e f ⊗
        BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b) =>
      g ≫ BalancedTensor.ι A E (R.rightAt f) (leftAt A B C E P Q b) e) he)
  have hlast := hh.trans (Category.id_comp _)
  have hraw := congrArg (fun g => (R.value e f ◁
    BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c) ≫ g) hlast
  dsimp only [associatorLeftι, BalancedTensor.Fubini.leftι,
    BalancedTensor.Fubini.leftModule, leftAt, BalancedTensor.changeLeft, eqToIso.hom] at hraw ⊢
  exact (Category.assoc (R.value e f ◁ BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c)
    (BalancedTensor.ι A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e)
    (eqToHom (congrArg (fun N : LeftModule A E => BalancedTensor.obj A E (R.rightAt f) N)
      (compose_leftAt_eq A B C E P Q b)))).trans hraw

@[reassoc (attr := simp)]
lemma associatorLeftι_hom (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) :
    associatorLeftι A B C E F P Q R b c e f ≫ (associatorValueIso A B C E F P Q R b f).hom =
      associatorRightι A B C E F P Q R b c e f := by
  have h := congrArg (fun g => g ≫
    (BalancedTensor.Fubini.iso A C E Q (R.rightAt f) (P.leftAt b)).hom)
    (associatorLeftι_transport A B C E F P Q R b c e f)
  rw [BalancedTensor.Fubini.leftι_iso_hom] at h
  unfold associatorValueIso
  simp only [Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc]
  exact h

@[reassoc (attr := simp)]
lemma associatorRightι_inv (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) :
    associatorRightι A B C E F P Q R b c e f ≫ (associatorValueIso A B C E F P Q R b f).inv =
      associatorLeftι A B C E F P Q R b c e f := by
  rw [← associatorLeftι_hom A B C E F P Q R b c e f, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- 実際の左括弧の合成からの射を三重生成元で判定する。 -/
lemma associatorLeft_hom_ext (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f : F) {T : Complex A}
    {g h : (compose A B E F (compose A B C E P Q) R).value b f ⟶ T}
    (heq : ∀ c e, associatorLeftι A B C E F P Q R b c e f ≫ g =
      associatorLeftι A B C E F P Q R b c e f ≫ h) : g = h := by
  apply BalancedTensor.hom_ext A E (R.rightAt f) ((compose A B C E P Q).leftAt b)
  intro e
  apply BalancedTensor.param_hom_ext A C (Q.rightAt e) (P.leftAt b)
  intro c
  exact heq c e

lemma associatorRight_hom_ext (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f : F) {T : Complex A}
    {g h : (compose A B C F P (compose A C E F Q R)).value b f ⟶ T}
    (heq : ∀ c e, associatorRightι A B C E F P Q R b c e f ≫ g =
      associatorRightι A B C E F P Q R b c e f ≫ h) : g = h :=
  BalancedTensor.Fubini.right_hom_ext A C E Q (R.rightAt f) (P.leftAt b) heq

end SerrePositivity.DifferentialGraded.BimoduleTensor
