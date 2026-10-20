module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorIterationHom
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHomHorizontal
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionComposition

/-! # 二回の tensor dg 作用と合成入力作用の元の等号移送
概要：入力とラベルを同時に動かす二回作用を、合成入力の作用と比較する。
方針：全 Hom 分解に既存の入力横合成則とラベル作用の合成則を適用する。
規約：元のラベル等号の共役を使う。使われ方：同じ三重 tensor 上の dg 関手等号。
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

/-- 二回の全 Hom 作用は、元の対象等号移送によって同じ合成入力の作用となる。 -/
lemma presentedPerfectDGTensorIteration_transport (F F' : DGFunctor A D E)
    (G G' : DGFunctor A E T) (X Y : PresentedPerfectDGObject A D) :
    (α_ (dgFunctorHom A E T G G') (dgFunctorHom A D E F F')
        (homObject A (PresentedPerfectDGObject A D) X Y)).hom ≫
      (𝟙 (dgFunctorHom A E T G G') ⊗ₘ presentedPerfectDGTensorHom A D E F F' X Y) ≫
        presentedPerfectDGTensorHom A E T G G'
          ((presentedPerfectDGAction A D E F).obj X)
          ((presentedPerfectDGAction A D E F').obj Y) ≫
          enrichedClosedIsoConjugation (Complex A)
            (presentedPerfectDGCompositionTransport A D E T F G X)
            (presentedPerfectDGCompositionTransport A D E T F' G' Y) =
      (((β_ (dgFunctorHom A E T G G') (dgFunctorHom A D E F F')).hom ≫
        dgFunctorHorizontal A D E T F F' G G') ⊗ₘ
          𝟙 (homObject A (PresentedPerfectDGObject A D) X Y)) ≫
        presentedPerfectDGTensorHom A D T (F.comp G) (F'.comp G') X Y := by
  slice_lhs 1 3 => rw [presentedPerfectDGTensorIterationHom]
  rw [Category.assoc]
  erw [← enrichedClosedIsoConjugation_comp (Complex A)
    (presentedPerfectDGCompositionTransport A D E T F G X)
    (presentedPerfectDGCompositionTransport A D E T F' G' X)
    (presentedPerfectDGCompositionTransport A D E T F' G' Y)]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc]
  rw [presentedPerfectDGInputHom_horizontal]
  have hm := presentedPerfectDGAction_comp_map A D E T F' G' X Y
  change ((presentedPerfectDGAction A D E F').map X Y ≫
    (presentedPerfectDGAction A E T G').map _ _) ≫
      enrichedClosedIsoConjugation (Complex A)
        (presentedPerfectDGCompositionTransport A D E T F' G' X)
        (presentedPerfectDGCompositionTransport A D E T F' G' Y) = _ at hm
  simp only [Category.assoc] at hm
  rw [hm]
  simp only [presentedPerfectDGTensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.assoc]
  rfl

end SerrePositivity.KST.SConstruction
