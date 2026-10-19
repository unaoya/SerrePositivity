module

public import SerrePositivity.KST.Spectra.TensorExchangeCoherence
public import SerrePositivity.KST.Spectra.InternalHomExchangeTarget

/-!
概要：閉対称モノイダル圏で、テンソル作用の Hom 写像と内部 Hom の源交換は整合する。
方針：評価の自然性と六角形から得た因子交換の等式へ還元する。
規約：単体集合の性質は使わない。使われ方：スペクトルの cotensor の構造可換性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.InternalHomExchange
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

abbrev tensorSuspend (S X : C) := S ⊗ X

def tensorHom (S X Y : C) : (ihom X).obj Y ⟶ (ihom (S ⊗ X)).obj (S ⊗ Y) :=
  curry ((α_ S X ((ihom X).obj Y)).hom ≫ S ◁ (ihom.ev X).app Y)

omit [SymmetricCategory C] in
@[reassoc]
lemma tensorHom_evaluation (S X Y : C) :
    (S ⊗ X) ◁ tensorHom S X Y ≫ (ihom.ev (S ⊗ X)).app (S ⊗ Y) =
      (α_ S X ((ihom X).obj Y)).hom ≫ S ◁ (ihom.ev X).app Y := uncurry_curry _

lemma tensorHom_strength (S X A Y : C) :
    tensorHom S X ((ihom A).obj Y) ≫
        (ihom (tensorSuspend S X)).map (HomTensorStrength.map S A Y) ≫
        (iso (tensorSuspend S X) A (tensorSuspend S Y)).hom =
      (iso X A Y).hom ≫ (ihom A).map (tensorHom S X Y) := by
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_ihom_map,
    uncurry_uncurry_hom]
  rw [HomTensorStrength.exchange_natural_right_assoc,
    HomTensorStrength.exchange_natural_right_assoc]
  have hev := congrArg (fun f ↦ A ◁ f)
    ((ihom.ev (tensorSuspend S X)).naturality (HomTensorStrength.map S A Y))
  change A ◁ (tensorSuspend S X ◁ (ihom (tensorSuspend S X)).map
      (HomTensorStrength.map S A Y) ≫
      (ihom.ev (tensorSuspend S X)).app ((ihom A).obj (tensorSuspend S Y))) =
    A ◁ ((ihom.ev (tensorSuspend S X)).app (tensorSuspend S ((ihom A).obj Y)) ≫
      HomTensorStrength.map S A Y) at hev
  simp only [whiskerLeft_comp] at hev
  rw [← Category.assoc (A ◁ tensorSuspend S X ◁
    (ihom (tensorSuspend S X)).map (HomTensorStrength.map S A Y)),
    hev, Category.assoc]
  rw [← whiskerLeft_comp_assoc A (tensorSuspend S X ◁ tensorHom S X ((ihom A).obj Y)),
    tensorHom_evaluation S]
  rw [HomTensorStrength.evaluation]
  simp only [whiskerLeft_comp, Category.assoc]
  erw [HomTensorStrength.exchange_natural_right_assoc A S
    ((ihom.ev X).app ((ihom A).obj Y))]
  conv_rhs =>
    unfold tensorHom
    rw [MonoidalClosed.uncurry_curry]
  erw [associator_naturality_right_assoc S X
    ((ihom.ev A).app ((ihom X).obj Y)),
    associator_naturality_right_assoc S X (A ◁ (iso X A Y).hom)]
  have hr := congrArg (fun f ↦ S ◁ f)
    (uncurry_uncurry_hom X A Y)
  change S ◁
      (X ◁ (A ◁ (iso X A Y).hom ≫ (ihom.ev A).app ((ihom X).obj Y)) ≫
        (ihom.ev X).app Y) = _ at hr
  simp only [whiskerLeft_comp, Category.assoc] at hr
  rw [hr]
  have hc := congrArg (fun f : tensorSuspend S X ⊗ (A ⊗ ((ihom X).obj ((ihom A).obj Y))) ⟶
      S ⊗ (A ⊗ (X ⊗ ((ihom X).obj ((ihom A).obj Y)))) ↦ f ≫
      S ◁ A ◁ (ihom.ev X).app ((ihom A).obj Y) ≫
        S ◁ (ihom.ev A).app Y)
    (HomTensorStrength.exchange_tensor_left S X A
      ((ihom X).obj ((ihom A).obj Y)))
  simp only [Category.assoc] at hc
  exact hc

end SerrePositivity.KST.Spectra.InternalHomExchange
