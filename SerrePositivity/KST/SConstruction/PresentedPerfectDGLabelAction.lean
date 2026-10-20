module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHomComposition
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHomUnit
public import SerrePositivity.KST.SConstruction.DGFunctorEnrichment

/-! # 固定したラベルにおける元の高次入力の dg 関手
概要：元の入力関手圏の全次数 Hom を使い、各ラベルで厳密な dg 関手を得る。
方針：元の入力 Hom 作用と、その単位・全次数合成の保存を束ねる。
規約：ラベル全体の出力 end を要求しない。使われ方：高次入力の tensor 作用への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 同じラベルにおける、元の厳密 dg 関手圏からの全 Hom を持つ dg 作用。 -/
def presentedPerfectDGLabelAction (X : PresentedPerfectDGObject A D) :
    DGFunctor A (DGFunctor A D E) (PresentedPerfectDGObject A E) where
  obj F := (presentedPerfectDGAction A D E F).obj X
  map F G := presentedPerfectDGInputHom A D E F G X
  map_id F := presentedPerfectDGInputHom_identity A D E F X
  map_comp F G H := presentedPerfectDGInputHom_composition A D E F G H X

/-- 固定したラベルの dg 作用は、元の同じ入力 Hom chain map を保持する。 -/
lemma presentedPerfectDGLabelAction_map (X : PresentedPerfectDGObject A D)
    (F G : DGFunctor A D E) :
    (presentedPerfectDGLabelAction A D E X).map F G =
      presentedPerfectDGInputHom A D E F G X := rfl

end SerrePositivity.KST.SConstruction
