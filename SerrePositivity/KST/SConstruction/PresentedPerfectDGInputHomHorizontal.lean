module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHomWhiskering
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHomComposition
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalComposition

/-! # ラベル付き模型の元の入力 Hom の横合成則
概要：元の入力 Hom の横合成は、既存のラベル等号移送を保って厳密に回収される。
方針：前後合成の二式と全次数縦合成を使い、中間比較を相殺する。
規約：元の非離散 Hom と等号移送を保持する。使われ方：厳密豊穣 K への高次入力作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 元の二つの入力 Hom 作用は、同じラベル合成等号の移送後に横合成を回収する。 -/
lemma presentedPerfectDGInputHom_horizontal (F F' : DGFunctor A D E)
    (G G' : DGFunctor A E T) (X : PresentedPerfectDGObject A D) :
    ((presentedPerfectDGInputHom A D E F F' X ≫ (presentedPerfectDGAction A E T G).map
          ((presentedPerfectDGAction A D E F).obj X) ((presentedPerfectDGAction A D E F').obj X)) ⊗ₘ
        presentedPerfectDGInputHom A E T G G' ((presentedPerfectDGAction A D E F').obj X)) ≫
        eComp (Complex A)
          ((presentedPerfectDGAction A E T G).obj ((presentedPerfectDGAction A D E F).obj X))
          ((presentedPerfectDGAction A E T G).obj ((presentedPerfectDGAction A D E F').obj X))
          ((presentedPerfectDGAction A E T G').obj ((presentedPerfectDGAction A D E F').obj X)) ≫
          enrichedClosedIsoConjugation (Complex A)
            (presentedPerfectDGCompositionTransport A D E T F G X)
            (presentedPerfectDGCompositionTransport A D E T F' G' X) =
      dgFunctorHorizontal A D E T F F' G G' ≫
        presentedPerfectDGInputHom A D T (F.comp G) (F'.comp G') X := by
  have hc := congrArg (fun k =>
    ((presentedPerfectDGInputHom A D E F F' X ≫ (presentedPerfectDGAction A E T G).map
        ((presentedPerfectDGAction A D E F).obj X) ((presentedPerfectDGAction A D E F').obj X)) ⊗ₘ
      presentedPerfectDGInputHom A E T G G' ((presentedPerfectDGAction A D E F').obj X)) ≫ k)
    (enrichedClosedIsoConjugation_comp (Complex A)
      (presentedPerfectDGCompositionTransport A D E T F G X)
      (presentedPerfectDGCompositionTransport A D E T F' G X)
      (presentedPerfectDGCompositionTransport A D E T F' G' X))
  simp only [tensorHom_comp_tensorHom_assoc] at hc
  rw [presentedPerfectDGInputHom_post, presentedPerfectDGInputHom_pre] at hc
  have hi := congrArg (fun k =>
    (dgFunctorHomPost A D E T G F F' ⊗ₘ dgFunctorHomPre A E T D F' G G') ≫ k)
    (presentedPerfectDGInputHom_composition A D T (F.comp G) (F'.comp G) (F'.comp G') X)
  simp only [tensorHom_comp_tensorHom_assoc] at hi
  simp only [dgFunctorHorizontal, Category.assoc]
  convert hc.symm.trans hi.symm using 1
  rfl

/-- 同じ横合成則は、元のラベル等号による Hom 複体の等号移送そのもので成立する。 -/
lemma presentedPerfectDGInputHom_horizontal_eqToHom (F F' : DGFunctor A D E)
    (G G' : DGFunctor A E T) (X : PresentedPerfectDGObject A D) :
    ((presentedPerfectDGInputHom A D E F F' X ≫ (presentedPerfectDGAction A E T G).map
          ((presentedPerfectDGAction A D E F).obj X) ((presentedPerfectDGAction A D E F').obj X)) ⊗ₘ
        presentedPerfectDGInputHom A E T G G' ((presentedPerfectDGAction A D E F').obj X)) ≫
        eComp (Complex A)
          ((presentedPerfectDGAction A E T G).obj ((presentedPerfectDGAction A D E F).obj X))
          ((presentedPerfectDGAction A E T G).obj ((presentedPerfectDGAction A D E F').obj X))
          ((presentedPerfectDGAction A E T G').obj ((presentedPerfectDGAction A D E F').obj X)) ≫
          eqToHom (congrArg₂ (homObject A (PresentedPerfectDGObject A T))
            (presentedPerfectDGActionObject_comp A D E T F G X)
            (presentedPerfectDGActionObject_comp A D E T F' G' X)) =
      dgFunctorHorizontal A D E T F F' G G' ≫
        presentedPerfectDGInputHom A D T (F.comp G) (F'.comp G') X := by
  rw [presentedPerfectDGHom_transport A T
    (presentedPerfectDGActionObject_comp A D E T F G X)
    (presentedPerfectDGActionObject_comp A D E T F' G' X)]
  exact presentedPerfectDGInputHom_horizontal A D E T F F' G G' X

end SerrePositivity.KST.SConstruction
