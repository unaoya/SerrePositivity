module
public import SerrePositivity.KST.SConstruction.DGExtensionParameterUnit
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHomFactorization

/-! # 元の入力 Hom 作用の閉単位保存
概要：元の入力 Hom end の閉単位は、各ラベルで同じ dg 閉単位へ送られる。
方針：任意パラメータの因子化と、元の単位自然変換の全段の保存を使う。
規約：零単体の関手の恒等保存だけで代用しない。使われ方：高次 Perf 作用の dg 単位。
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
  (F : DGFunctor A D E)

/-- 元の入力 Hom end の単位は、各ラベルの作用の同じ全 Hom の単位へ送られる。 -/
lemma presentedPerfectDGInputHom_identity (X : PresentedPerfectDGObject A D) :
    dgFunctorIdentity A D E F ≫ presentedPerfectDGInputHom A D E F F X =
      eId (Complex A) ((presentedPerfectDGAction A D E F).obj X) := by
  have h := presentedPerfectDGInputHom_factorization A D E (dgFunctorParamIdentity A D E F) X
  rw [presentedPerfectDGParameter_identity] at h
  exact h

end SerrePositivity.KST.SConstruction
