module
public import SerrePositivity.KST.SConstruction.RightActionBraiding
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGRightTensorAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorIterationTransport

/-! # 元の実 Perf 右作用の二回適用と合成入力
概要：ラベル・前入力・後入力の順の全 Hom を、同じ入力横合成の作用と比較する。
方針：元の三因子交換則を、既存の全次数 Perf 合成比較と同じ対象等号移送に適用する。
規約：同じラベル・Hom・Koszul 符号を保持。使われ方：実 dg 右作用の合成等号。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [DGCategory A E] [DGCategory A T]
  [Small.{u} D] [Small.{u} E] [Small.{u} T]

/-- 二回の全 Hom 右作用は、元の対象等号移送で同じ合成入力の作用になる。 -/
lemma presentedPerfectDGRightTensorIteration_transport
    (F F' : DGFunctor A D E) (G G' : DGFunctor A E T) (X Y : PresentedPerfectDGObject A D) :
    ((presentedPerfectDGRightTensorHom A D E F F' X Y ⊗ₘ 𝟙 (dgFunctorHom A E T G G')) ≫
      presentedPerfectDGRightTensorHom A E T G G'
        ((presentedPerfectDGAction A D E F).obj X)
        ((presentedPerfectDGAction A D E F').obj Y)) ≫
      enrichedClosedIsoConjugation (Complex A)
        (presentedPerfectDGCompositionTransport A D E T F G X)
        (presentedPerfectDGCompositionTransport A D E T F' G' Y) =
    (α_ (homObject A (PresentedPerfectDGObject A D) X Y) (dgFunctorHom A D E F F')
      (dgFunctorHom A E T G G')).hom ≫
      (𝟙 (homObject A (PresentedPerfectDGObject A D) X Y) ⊗ₘ
        dgFunctorHorizontal A D E T F F' G G') ≫
      presentedPerfectDGRightTensorHom A D T (F.comp G) (F'.comp G') X Y := by
  exact rightActionPairing_associativity
    (presentedPerfectDGTensorHom A D E F F' X Y)
    (presentedPerfectDGTensorHom A E T G G'
      ((presentedPerfectDGAction A D E F).obj X) ((presentedPerfectDGAction A D E F').obj Y))
    (enrichedClosedIsoConjugation (Complex A)
      (presentedPerfectDGCompositionTransport A D E T F G X)
      (presentedPerfectDGCompositionTransport A D E T F' G' Y))
    (dgFunctorHorizontal A D E T F F' G G')
    (presentedPerfectDGTensorHom A D T (F.comp G) (F'.comp G') X Y)
    (presentedPerfectDGTensorIteration_transport A D E T F F' G G' X Y)

end SerrePositivity.KST.SConstruction
