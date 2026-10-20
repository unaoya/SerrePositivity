module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorComposition

/-! # 入力とラベルを同時に動かす厳密 tensor dg 作用
概要：元の全次数入力とラベルの Hom 作用を、一つの厳密 dg 関手に束ねる。
方針：元の tensor 単位と斉次交換律から得た全次数合成保存を使う。
規約：入力 Hom やラベル Hom を離散化しない。使われ方：native nerve の高次作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

local instance tensorActionFunctorEnrichment :
    DGCategory A (DGTensorCategory A (DGFunctor A D E) (PresentedPerfectDGObject A D)) :=
  dgTensorEnrichment A (DGFunctor A D E) (PresentedPerfectDGObject A D)

/-- 二つの元の閉単位は、tensor Hom 作用で同じ作用対象の閉単位へ送られる。 -/
lemma presentedPerfectDGTensorHom_identity
    (x : DGTensorCategory A (DGFunctor A D E) (PresentedPerfectDGObject A D)) :
    eId (Complex A) x ≫ presentedPerfectDGTensorHom A D E x.1 x.1 x.2 x.2 =
      eId (Complex A) ((presentedPerfectDGAction A D E x.1).obj x.2) := by
  rw [dgTensor_identity, Category.assoc]
  change (λ_ (𝟙_ (Complex A))).inv ≫
    (dgFunctorIdentity A D E x.1 ⊗ₘ eId (Complex A) x.2) ≫
      ((presentedPerfectDGInputHom A D E x.1 x.1 x.2 ⊗ₘ
        (presentedPerfectDGAction A D E x.1).map x.2 x.2) ≫ _) = _
  rw [tensorHom_comp_tensorHom_assoc, presentedPerfectDGInputHom_identity,
    (presentedPerfectDGAction A D E x.1).map_id]
  exact dgEnrichedUnitsMultiply _

/-- 元の厳密 dg 入力とラベルを同時に動かす、全次数の tensor dg 関手。 -/
def presentedPerfectDGTensorAction :
    DGFunctor A (DGTensorCategory A (DGFunctor A D E) (PresentedPerfectDGObject A D))
      (PresentedPerfectDGObject A E) where
  obj x := (presentedPerfectDGAction A D E x.1).obj x.2
  map x y := presentedPerfectDGTensorHom A D E x.1 y.1 x.2 y.2
  map_id := presentedPerfectDGTensorHom_identity A D E
  map_comp := presentedPerfectDGTensorHom_composition A D E

/-- tensor dg 作用の全 Hom は、元の入力作用とラベル作用の合成を厳密に回収する。 -/
lemma presentedPerfectDGTensorAction_map
    (x y : DGTensorCategory A (DGFunctor A D E) (PresentedPerfectDGObject A D)) :
    (presentedPerfectDGTensorAction A D E).map x y =
      presentedPerfectDGTensorHom A D E x.1 y.1 x.2 y.2 := rfl

end SerrePositivity.KST.SConstruction
