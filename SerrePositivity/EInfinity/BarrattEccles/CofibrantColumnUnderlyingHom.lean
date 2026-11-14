module
public import SerrePositivity.EInfinity.BarrattEccles.CAlgDerivedForgetSource
public import SerrePositivity.EInfinity.FrameHom.MixedNerveHomRecovery
public import SerrePositivity.EInfinity.ComplexLimits.DerivedNatTransComponent
/-! 概要：cofibrant 相対列の忘却後の全通常射を元の複体円柱へ回収する。
方針：Hom 持ち上げを元の忘却と交換し、同じ全パラメータを下げる。
規約：元の代数射・複体射と全円柱を保持する。
使われ方：実 U の全源比較と元の単位三角形の接合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.FrameHom
variable (A : Type u) [CommRing A]

/-- 概要：元の cofibrant 代数の通常忘却。
方針：同じ包含と通常忘却を合成する。
規約：底の cofibrancy を要求しない。使われ方：全 Hom 宇宙回収。 -/
def cofibrantAlgebraOrdinaryForget : CofibrantAlgebra A ⥤ Complex A :=
  cofibrantAlgebraInclusion A ⋙ Operad.Algebra.forget (operad A)

/-- 概要：同じ導来源は Hom を上げた元の忘却から厳密に回収される。
方針：全単体列と元の通常射を比較する。
規約：全パラメータを保持。使われ方：全自然変換の回収。 -/
lemma cofibrantAlgebraUnderlyingDerivedSource_eq_lifted :
    cofibrantAlgebraUnderlyingDerivedSource A =
      nerveMap (MixedNerve.lifted (cofibrantAlgebraOrdinaryForget A)) ≫
        MixedNerve.down (Complex A) ≫ ComplexLimits.complexOrdinaryDerivedSource A := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  apply congrArg ((ComplexLimits.complexOrdinaryDerivedSource A).app n)
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：相対列の忘却後の全自然変換は元の複体円柱の全制限。
方針：全後合成の回収と同じ Hom 宇宙の回収公式を使う。
規約：元の全図式と射を保持。使われ方：実 U の全屋根の回収。 -/
lemma cofibrantColumnUnderlyingHom_arrow {I : Type (u + 1)} [Category.{u} I]
    {V W : I ⥤ CofibrantAlgebra A} (a : V ⟶ W) :
    Arrow.mk (NerveColumn.hom (cofibrantAlgebraUnderlyingDerivedSource A)
      (MixedNerve.liftedNatTrans (C := I) (D := CofibrantAlgebra A) a)) =
    Arrow.mk ((hoFunctor.map ((pre (MixedNerve.down I)).app
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor.map
      (ComplexLimits.complexOrdinaryDerivedNatTransHom A
        (Functor.whiskerRight a (cofibrantAlgebraOrdinaryForget A)))) := by
  rw [cofibrantAlgebraUnderlyingDerivedSource_eq_lifted]
  rw [NerveColumn.hom_whiskerRight]
  have ha : Functor.whiskerRight (MixedNerve.liftedNatTrans (C := I) (D := CofibrantAlgebra A) a)
      (MixedNerve.lifted (cofibrantAlgebraOrdinaryForget A)) =
      MixedNerve.liftedNatTrans (Functor.whiskerRight a (cofibrantAlgebraOrdinaryForget A)) := rfl
  rw [ha]
  exact MixedNerve.liftedHom_postcomp_arrow I
    (Functor.whiskerRight a (cofibrantAlgebraOrdinaryForget A))
    (ComplexLimits.complexOrdinaryDerivedSource A)

end SerrePositivity.EInfinity.BarrattEccles
