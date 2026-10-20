module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorCompositionFunctors
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorIterationTransport

/-! # 同じ三重 tensor 上の厳密 dg 作用の合成則
概要：二回のラベル付き dg 作用と合成入力の作用を、元の dg 関手の等号へ束ねる。
方針：全 Hom の等号移送と既存の対象等号を豊穣関手の外延性に適用する。
規約：全次数と signed 交換を保つ。使われ方：厳密 dg 入力による豊穣 K の関手性。
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

/-- 同じ三重 tensor 上の二回作用と合成入力作用は、元の対象等号で全 Hom が一致する。 -/
lemma presentedPerfectDGTensorIterated_map_transport
    (x y : DGTensorCategory A
      (DGTensorCategory A (DGFunctor A E T) (DGFunctor A D E)) (PresentedPerfectDGObject A D)) :
    (presentedPerfectDGTensorIterated A D E T).map x y ≫
      enrichedClosedIsoConjugation (Complex A)
        (presentedPerfectDGCompositionTransport A D E T x.1.2 x.1.1 x.2)
        (presentedPerfectDGCompositionTransport A D E T y.1.2 y.1.1 y.2) =
      (presentedPerfectDGTensorComposite A D E T).map x y := by
  rw [presentedPerfectDGTensorIterated_map, presentedPerfectDGTensorComposite_map]
  dsimp only [dgTensorBraidingHom]
  simp only [Category.assoc]
  erw [presentedPerfectDGTensorIteration_transport]
  rfl

/-- 二回の元の tensor dg 作用と合成入力作用は、同じ始域上の厳密 dg 関手として等しい。 -/
lemma presentedPerfectDGTensorAction_comp :
    presentedPerfectDGTensorIterated A D E T = presentedPerfectDGTensorComposite A D E T := by
  apply presentedPerfectDGFunctor_ext A T (presentedPerfectDGTensorIterated_obj A D E T)
  intro x y
  exact presentedPerfectDGTensorIterated_map_transport A D E T x y

end SerrePositivity.KST.SConstruction
