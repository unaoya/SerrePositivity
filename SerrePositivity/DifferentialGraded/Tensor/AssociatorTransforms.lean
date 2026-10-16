module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorBimodule
public import SerrePositivity.DifferentialGraded.Bimodule.ClosedIso

/-! # 結合比較の右加群同型と左作用の全Hom自然性 -/
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


/-- 結合比較の全Homに関して豊穣自然な単位パラメータ変換。 -/
def associatorHom (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) :
    BimoduleParamTrans A B F (𝟙_ (Complex A))
      (compose A B E F (compose A B C E P Q) R) (compose A B C F P (compose A C E F Q R)) :=
  Bimodule.isoFamilyHom A B F (associatorRightModuleIso A B C E F P Q R)
    (associatorRightModuleIso_naturality A B C E F P Q R)

@[simp]
lemma associatorHom_app (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (associatorHom A B C E F P Q R).app f =
      ForgetEnrichment.homTo (Complex A) (associatorRightModuleIso A B C E F P Q R f).hom := rfl

/-- 結合比較の全Homに関して豊穣自然な単位パラメータ変換。 -/
def associatorInv (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) :
    BimoduleParamTrans A B F (𝟙_ (Complex A))
      (compose A B C F P (compose A C E F Q R)) (compose A B E F (compose A B C E P Q) R) :=
  Bimodule.isoFamilyInv A B F (associatorRightModuleIso A B C E F P Q R)
    (associatorRightModuleIso_naturality A B C E F P Q R)

@[simp]
lemma associatorInv_app (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (associatorInv A B C E F P Q R).app f =
      ForgetEnrichment.homTo (Complex A) (associatorRightModuleIso A B C E F P Q R f).inv := rfl

/-- 結合比較の順逆の合成は全Hom endの閉単位元。 -/
lemma associator_hom_inv_app (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      ((associatorHom A B C E F P Q R).app f ⊗ₘ
        (associatorInv A B C E F P Q R).app f) ≫
      eComp (Complex A) ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B E F (compose A B C E P Q) R).rightAt f) =
      eId (Complex A) ((compose A B E F (compose A B C E P Q) R).rightAt f) :=
  Bimodule.isoFamily_hom_inv_app A B F (associatorRightModuleIso A B C E F P Q R)
    (associatorRightModuleIso_naturality A B C E F P Q R) f

/-- 結合比較の順逆の合成は全Hom endの閉単位元。 -/
lemma associator_inv_hom_app (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      ((associatorInv A B C E F P Q R).app f ⊗ₘ
        (associatorHom A B C E F P Q R).app f) ≫
      eComp (Complex A) ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f) =
      eId (Complex A) ((compose A B C F P (compose A C E F Q R)).rightAt f) :=
  Bimodule.isoFamily_inv_hom_app A B F (associatorRightModuleIso A B C E F P Q R)
    (associatorRightModuleIso_naturality A B C E F P Q R) f

/-- 主Hom endを評価すると元の結合同型の閉成分に戻る。 -/
lemma associatorHom_π (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    (associatorHom A B C E F P Q R).app f ≫
      moduleHomπ A B ((compose A B E F (compose A B C E P Q) R).rightAt f)
        ((compose A B C F P (compose A C E F Q R)).rightAt f) b =
      closedMap A (associatorValueIso A B C E F P Q R b f).hom := by
  exact (moduleEvaluation_closedMap A B b
    (associatorRightModuleIso A B C E F P Q R f).hom).symm.trans
      (congrArg (fun k : (compose A B E F (compose A B C E P Q) R).value b f ⟶
          (compose A B C F P (compose A C E F Q R)).value b f => closedMap A k)
        (associatorRightModuleIso_hom_eval A B C E F P Q R b f))

/-- 主Hom endを評価すると元の結合同型の閉成分に戻る。 -/
lemma associatorInv_π (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) :
    (associatorInv A B C E F P Q R).app f ≫
      moduleHomπ A B ((compose A B C F P (compose A C E F Q R)).rightAt f)
        ((compose A B E F (compose A B C E P Q) R).rightAt f) b =
      closedMap A (associatorValueIso A B C E F P Q R b f).inv := by
  exact (moduleEvaluation_closedMap A B b
    (associatorRightModuleIso A B C E F P Q R f).inv).symm.trans
      (congrArg (fun k : (compose A B C F P (compose A C E F Q R)).value b f ⟶
          (compose A B E F (compose A B C E P Q) R).value b f => closedMap A k)
        (associatorRightModuleIso_inv_eval A B C E F P Q R b f))

end SerrePositivity.DifferentialGraded.BimoduleTensor
